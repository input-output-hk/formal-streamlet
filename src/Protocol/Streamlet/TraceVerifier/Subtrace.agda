-- {-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.TraceVerifier.Subtrace (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Decidability ⋯

--

∈-mapWith∈⁺ : ∀ {A B : Type} {x}{xs : List A} {f : ∀ {x} → x ∈ xs → B} →
  ∀ (x∈ : x ∈ xs) →
  f {x} x∈ ∈ L.Mem.mapWith∈ xs f
∈-mapWith∈⁺ {xs = _ ∷ _} = λ where
  (here refl) → here refl
  (there p)   → there $ ∈-mapWith∈⁺ p

--

-- * verifying a whole trace

data Action : Type where
  Propose Vote  : Pid → Chain → List Transaction → Action
  -- RegisterVote  : Pid → ℕ → Action
  FinalizeBlock : Pid → Chain → Block → Action
  DishonestStep : Pid → Message → Action
  Deliver Drop  : ℕ → Action
  AdvanceEpoch  : Action

Actions = List Action

private variable
  α α′ : Action
  αs αs′ : Actions

-- ** silent steps

-- data Silent : (s —→ s′) → Type where
--   instance RegisterVote :
--     Silent (LocalStep (RegisterVote _ _))

Silent : (s —→ s′) → Type
Silent = λ where
  (LocalStep (RegisterVote _ _)) → ⊤
  _ → ⊥

¬Silent : (s —→ s′) → Type
¬Silent = λ where
  (LocalStep (RegisterVote _ _)) → ⊥
  _ → ⊤

data _—→ᵉ_ : GlobalState → GlobalState → Type where
  silent :
    ∀ (s→ : s —→ s′) ⦃ _ : Silent s→ ⦄ →
    ∙ s′ —→ᵉ s″
      ──────────────
      s —→ᵉ s″

  stop :
    ∀ (s→ : s —→ s′) ⦃ _ : ¬Silent s→ ⦄ →
      ──────────────
      s —→ᵉ s′

-- ** labels

private
  toℕ : ∀ {A : Type} {x} {xs : List A} → x ∈ xs → ℕ
  toℕ = Fi.toℕ ∘ L.Any.index

getLabel : (s —→ᵉ s′) → Action
getLabel (silent _ st) = getLabel st
getLabel (stop st ⦃ ¬e ⦄)
  with st | ¬e
... | LocalStep {p = p} {mm = mm} (ProposeBlock {ch = ch} {txs = txs} _ _ _ _) | tt = Propose p ch txs
... | LocalStep {p = p} {mm = mm} (VoteBlock {ch = ch} {txs = txs} _ _ _ _ _ _) | tt = Vote p ch txs
... | LocalStep {p = p} {mm = mm} (FinalizeBlock ch b _ _) | tt = FinalizeBlock p ch b
... | DishonestLocalStep {p = p} {m = m} _ _ | tt = DishonestStep p m
... | Deliver env∈ | tt = Deliver (toℕ env∈)
... | Drop env∈ | tt = Drop (toℕ env∈)
... | AdvanceEpoch | tt = AdvanceEpoch

private
  getLabel≢Deliver : ∀ {n} ⦃ _ : Honest p ⦄ s (lst : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    let st = LocalStep {s = s} lst in
    ⦃ _ : ¬Silent st ⦄ →
    getLabel (stop st) ≢ Deliver n
  getLabel≢Deliver _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

  getLabel≢Drop : ∀ {n} ⦃ _ : Honest p ⦄ s (lst : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    let st = LocalStep {s = s} lst in
    ⦃ _ : ¬Silent st ⦄ →
    getLabel (stop st) ≢ Drop n
  getLabel≢Drop _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

  getLabel≢Dishonest : ∀ ⦃ _ : Honest p ⦄ s (lst : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    let st = LocalStep {s = s} lst in
    ⦃ _ : ¬Silent st ⦄ →
    getLabel (stop st) ≢ DishonestStep p′ m
  getLabel≢Dishonest _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

  getLabel≢Advance : ∀ ⦃ _ : Honest p ⦄ s (lst : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    let st = LocalStep {s = s} lst in
    ⦃ _ : ¬Silent st ⦄ →
    getLabel (stop st) ≢ AdvanceEpoch
  getLabel≢Advance _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

-- ** validity of actions

ValidAction : Action → GlobalState → Type
ValidAction α s = ∃ λ s′ → ∃ λ (st : s —→ᵉ s′) → getLabel st ≡ α

private
  index? : ∀ {A : Type} n (xs : List A) →
    Dec $ ∃ λ x → ∃ λ (x∈ : x ∈ xs) → toℕ x∈ ≡ n
  index? n [] = no λ where (_ , () , _)
  index? zero (x ∷ xs) = yes (-, here refl , refl)
  index? (suc n) (x ∷ xs)
    with index? n xs
  ... | no ¬p
    = no λ where (x , there x∈ , eq) → ¬p (x , x∈ , Nat.suc-injective eq)
  ... | yes (x , x∈ , eq)
    = yes (x , there x∈ , cong suc eq)

  index≡ : ∀ {A : Type} {x y : A} n (xs : List A) →
    (x∈ : x ∈ xs) → toℕ x∈ ≡ n →
    (y∈ : y ∈ xs) → toℕ y∈ ≡ n →
    ∃ λ (eq : x ≡ y) → subst (_∈ _) eq x∈ ≡ y∈
  index≡ _ _ (here refl) refl (here refl) refl = refl , refl
  index≡ (suc n) (_ ∷ xs) (there x∈) refl (there y∈) eq
    with refl , eq ← index≡ n xs x∈ refl y∈ (Nat.suc-injective eq)
    = refl , cong there eq

  Vote-inj : (Message ∋ Vote sb) ≡ Vote sb′ → sb ≡ sb′
  Vote-inj refl = refl

  Deliver-inj : ∀ {n m : ℕ} → Deliver n ≡ Deliver m → n ≡ m
  Deliver-inj refl = refl

  Drop-inj : ∀ {n m : ℕ} → Drop n ≡ Drop m → n ≡ m
  Drop-inj refl = refl

registerVote′ : ∀ s p ⦃ _ : Honest p ⦄ (m∈ : m ∈ (s ＠ p) .inbox) → GlobalState
registerVote′ s p m∈ = updateLocal p (registerVote (s ＠ p) m∈) s

registerVote′-ph≡ : ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ (m∈ : m ∈ (s ＠ p′) .inbox) →
  (registerVote′ s p′ m∈ ＠ p) .phase ≡ Ready
  ─────────────────────────────────────────
  (s ＠ p) .phase ≡ Ready
registerVote′-ph≡ {p}{p′}{m}{s} ⦃ hp ⦄ m∈ ph≡
  with p ≟ p′
... | no p≢
  rewrite pLookup∘updateAt′ p p′ {const $ registerVote (s ＠ p′) m∈} (p≢ ∘ ↑-injective) (s .stateMap)
  = ph≡
... | yes refl
  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const $ registerVote ((s ＠ p) ⦃ hp ⦄) m∈} (s .stateMap)
  = ph≡

registerVote′-m∈⇒ : ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ (m∈ : m ∈ (s ＠ p′) .inbox) →
  let s′ = registerVote′ s p′ m∈ in
  AnyFirst (m′ ≡_) ((s′ ＠ p) .inbox)
  ──────────────────────────────────
  AnyFirst (m′ ≡_) ((s ＠ p) .inbox)
registerVote′-m∈⇒ {p}{p′}{m}{s}{m′} ⦃ hp ⦄ m∈ m∈′
  with p ≟ p′
... | no p≢
  rewrite pLookup∘updateAt′ p p′ {const $ registerVote (s ＠ p′) m∈} (p≢ ∘ ↑-injective) (s .stateMap)
  = m∈′
... | yes refl
  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const $ registerVote ((s ＠ p) ⦃ hp ⦄) m∈} (s .stateMap)
  = Any⇒AnyFirst
  $ ∈-─⁻ m∈
  $ AnyFirst⇒Any m∈′

registerVote′-sb∉⇒ : ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ (m∈ : m ∈ (s ＠ p′) .inbox) →
  let s′ = registerVote′ s p′ m∈ in
  sb ∉ map _∙signedBlock ((s′ ＠ p) .db)
  ─────────────────────────────────────
  sb ∉ map _∙signedBlock ((s ＠ p) .db)
registerVote′-sb∉⇒ {p}{p′}{m}{s}{sb} ⦃ hp ⦄ m∈ sb∉
  with p ≟ p′
... | no p≢
  rewrite pLookup∘updateAt′ p p′ {const $ registerVote (s ＠ p′) m∈} (p≢ ∘ ↑-injective) (s .stateMap)
  = sb∉
... | yes refl
  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const $ registerVote ((s ＠ p) ⦃ hp ⦄) m∈} (s .stateMap)
  = sb∉ ∘ there

ValidAction-Deliver : ∀ n →
  ValidAction (Deliver n) s →
  ∃ λ env → ∃ λ (env∈ : env ∈ s .networkBuffer) → toℕ env∈ ≡ n
ValidAction-Deliver n = λ where
  (_ , stop (LocalStep st) , α≡) → ⊥-elim $ getLabel≢Deliver _ st α≡
  (_ , stop (Deliver env∈) , α≡) → -, env∈ , Deliver-inj α≡
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Deliver n (_ , st , α≡)

ValidAction-Drop : ∀ n →
  ValidAction (Drop n) s →
  ∃ λ env → ∃ λ (env∈ : env ∈ s .networkBuffer) → toℕ env∈ ≡ n
ValidAction-Drop n = λ where
  (_ , stop (LocalStep st) , α≡) → ⊥-elim $ getLabel≢Drop _ st α≡
  (_ , stop (Drop env∈) , α≡) → -, env∈ , Drop-inj α≡
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Drop n (_ , st , α≡)

ValidAction-DishonestStep :
  ValidAction (DishonestStep p m′) s →
  Dishonest p
ValidAction-DishonestStep = λ where
  (_ , stop (LocalStep st) , α≡) → ⊥-elim $ getLabel≢Dishonest _ st α≡
  (_ , stop (DishonestLocalStep ¬hp _) , refl) → ¬hp
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-DishonestStep (_ , st , α≡)

ValidAction-DishonestStep⇒NoForging :
  ValidAction (DishonestStep p′ m′) s →
  (Honest (m′ ∙pid) → m′ ∈ s .history)
ValidAction-DishonestStep⇒NoForging = λ where
  (_ , stop (LocalStep st) , α≡) → ⊥-elim $ getLabel≢Dishonest _ st α≡
  (_ , stop (DishonestLocalStep _ ¬frg) , refl) → ¬frg
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-DishonestStep⇒NoForging (_ , st , α≡)

ValidAction-Finalize⇒Honest :
  ValidAction (FinalizeBlock p ch b) s →
  Honest p
ValidAction-Finalize⇒Honest = λ where
  (_ , stop (LocalStep (FinalizeBlock _ _ _ _)) , refl) → it
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Finalize⇒Honest (_ , st , α≡)

ValidAction-Finalize⇒ValidChain :
  ValidAction (FinalizeBlock p ch b) s →
  ValidChain (b ∷ ch)
ValidAction-Finalize⇒ValidChain = λ where
  (_ , stop (LocalStep (FinalizeBlock _ _ vch _)) , refl) → vch
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Finalize⇒ValidChain (_ , st , α≡)

ValidAction-Propose⇒Honest :
  ValidAction (Propose p ch txs) s →
  Honest p
ValidAction-Propose⇒Honest = λ where
  (_ , stop (LocalStep (ProposeBlock _ _ _ _)) , refl) → it
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Propose⇒Honest (_ , st , α≡)

ValidAction-Propose⇒ph≡ : ⦃ _ : Honest p ⦄ →
  ValidAction (Propose p ch txs) s →
  (s ＠ p) .phase ≡ Ready
ValidAction-Propose⇒ph≡ {s = s} = λ where
  (_ , stop (LocalStep (ProposeBlock ph≡ _ _ _)) , refl) → ph≡
  (_ , silent (LocalStep {p′} (RegisterVote m∈ _)) st , α≡) →
    registerVote′-ph≡ {s = s} m∈ $ ValidAction-Propose⇒ph≡ (_ , st , α≡)

ValidAction-Propose⇒p≡L :
  ValidAction (Propose p ch txs) s →
  p ≡ epochLeader (s .e-now)
ValidAction-Propose⇒p≡L = λ where
  (_ , stop (LocalStep (ProposeBlock _ p≡L _ _)) , refl) → p≡L
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Propose⇒p≡L (_ , st , α≡)

ValidAction-Propose⇒ValidChain :
  ValidAction (Propose p ch txs) s →
  let b = ⟨ ch ♯ , s .e-now , txs ⟩ in
  ValidChain (b ∷ ch)
ValidAction-Propose⇒ValidChain = λ where
  (_ , stop (LocalStep (ProposeBlock _ _ _ vch)) , refl) → vch
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Propose⇒ValidChain (_ , st , α≡)

ValidAction-Vote⇒Honest :
  ValidAction (Vote p ch txs) s →
  Honest p
ValidAction-Vote⇒Honest = λ where
  (_ , stop (LocalStep (VoteBlock _ _ _ _ _ _)) , refl) → it
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Vote⇒Honest (_ , st , α≡)

ValidAction-Vote⇒m∈ : ⦃ _ : Honest p ⦄ →
  ValidAction (Vote p ch txs) s →
  let
    b  = ⟨ ch ♯ , s .e-now , txs ⟩
    sᵖ = signBlock (epochLeader $ s .e-now) b
  in
    AnyFirst (Propose sᵖ ≡_) ((s ＠ p) .inbox)
ValidAction-Vote⇒m∈ {s = s} = λ where
  (_ , stop (LocalStep (VoteBlock m∈ _ _ _ _ _)) , refl) → m∈
  (_ , silent (LocalStep {p′} (RegisterVote m∈ _)) st , α≡) →
    registerVote′-m∈⇒ {s = s} m∈ $ ValidAction-Vote⇒m∈ (_ , st , α≡)

ValidAction-Vote⇒sb∉ : ⦃ _ : Honest p ⦄ →
  ValidAction (Vote p ch txs) s →
  let
    b  = ⟨ ch ♯ , s .e-now , txs ⟩
    sᵖ = signBlock (epochLeader $ s .e-now) b
  in
    sᵖ ∉ map _∙signedBlock ((s ＠ p) .db)
ValidAction-Vote⇒sb∉ {s = s} = λ where
  (_ , stop (LocalStep (VoteBlock _ sb∉ _ _ _ _)) , refl) → sb∉
  (_ , silent (LocalStep {p′} (RegisterVote m∈ _)) st , α≡) →
    registerVote′-sb∉⇒ {s = s} m∈ $ ValidAction-Vote⇒sb∉ (_ , st , α≡)

ValidAction-Vote⇒ph≡ : ⦃ _ : Honest p ⦄ →
  ValidAction (Vote p ch txs) s →
  (s ＠ p) .phase ≡ Ready
ValidAction-Vote⇒ph≡ {s = s} = λ where
  (_ , stop (LocalStep (VoteBlock _ _ ph≡ _ _ _)) , refl) → ph≡
  (_ , silent (LocalStep {p′} (RegisterVote m∈ _)) st , α≡) →
    registerVote′-ph≡ {s = s} m∈ $ ValidAction-Vote⇒ph≡ (_ , st , α≡)

ValidAction-Vote⇒p≢L :
  ValidAction (Vote p ch txs) s →
  p ≢ epochLeader (s .e-now)
ValidAction-Vote⇒p≢L = λ where
  (_ , stop (LocalStep (VoteBlock _ _ _ p≢L _ _)) , refl) → p≢L
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Vote⇒p≢L (_ , st , α≡)

ValidAction-Vote⇒ValidChain :
  ValidAction (Vote p ch txs) s →
  let b = ⟨ ch ♯ , s .e-now , txs ⟩ in
  ValidChain (b ∷ ch)
ValidAction-Vote⇒ValidChain = λ where
  (_ , stop (LocalStep (VoteBlock _ _ _ _ _ vch)) , refl) → vch
  (_ , silent (LocalStep (RegisterVote _ _)) st , α≡) →
    ValidAction-Vote⇒ValidChain (_ , st , α≡)

hp⇔∈hon :
  Honest p
  ══════════════
  p ∈ honestPids
hp⇔∈hon = L.Mem.∈-filter⁺ honest? (L.Mem.∈-allFin _)
        , proj₂ ∘ L.Mem.∈-filter⁻ honest? {xs = L.allFin nodes}

∈hon⇒hp : p ∈ honestPids → Honest p
∈hon⇒hp = hp⇔∈hon .proj₂

hp⇒∈hon : Honest p → p ∈ honestPids
hp⇒∈hon = hp⇔∈hon .proj₁

∃Honest↔Any : ∀ (P : ∀ p → Honest p → Type) →
  (∃ λ p → ∃ λ (hp : Honest p) → P p hp)
  ════════════════════════════════════════════════════
  ∃ λ p → ∃ λ (p∈ : p ∈ honestPids) → P p (∈hon⇒hp p∈)
∃Honest↔Any P
  = (λ (p , hp , Pp) → p , hp⇒∈hon hp , subst (P p) (Honest-irr _ _) Pp)
  , (λ (p , p∈ , Pp) → p , ∈hon⇒hp p∈ , subst (P p) (Honest-irr _ _) Pp)

{-
Unique-honestPids : Unique honestPids
Unique-honestPids = filter⁺ _ $ allFin⁺ _
  where open L.Unique

open import Data.List.Membership.Propositional.Properties.WithK
  using (unique⇒irrelevant)
-}

instance
  Dec-∃∈ : ∀ {A : Type} {xs : List A} {P : ∀ {x} → x ∈ xs → Type}
    → ⦃ ∀ {x} {x∈ : x ∈ xs} → P x∈ ⁇ ⦄
    → (∃ λ x → Σ (x ∈ xs) P) ⁇
  Dec-∃∈ {xs = xs} {P = P} .dec
    with xs
  ... | [] = no λ where (_ , () , _)
  ... | x ∷ xs
    with ¿ P (here refl) ¿
  ... | yes px
    = yes (x , here refl , px)
  ... | no ¬px
    with ¿ ∃ (λ x → Σ (x ∈ xs) (P ∘ there)) ¿
  ... | no ∄x
    = no λ where (_ ,  here refl , px) → ¬px px
                 (x , there x∈ , px) → ∄x (x , x∈ , px)
  ... | yes (x , x∈ , px)
    = yes (x , there x∈ , px)

∃Honest? : ∀ (P : ∀ {p} → Honest p → Type) → ⦃ ∀ {p} {hp : Honest p} → P hp ⁇ ⦄ →
  Dec (∃ λ p → ∃ λ (p∈ : p ∈ honestPids) → P (∈hon⇒hp p∈))
∃Honest? _ = dec

∃FinalizedChain : GlobalState → Chain → Block → Pid → Type
∃FinalizedChain s ch b p = ValidAction (FinalizeBlock p ch b) s

∃Propose : GlobalState → Chain → List Transaction → Pid → Type
∃Propose s ch txs p = ValidAction (Propose p ch txs) s

∃Vote : GlobalState → Chain → List Transaction → Pid → Type
∃Vote s ch txs p = ValidAction (Vote p ch txs) s

pattern Stop-FinalizedLocally vch fch =
  _ , stop (LocalStep (FinalizeBlock _ _ vch fch)) , refl
pattern Stop-ProposedLocally ph≡ p≡L lch vch =
  _ , stop (LocalStep (ProposeBlock ph≡ p≡L lch vch)) , refl
pattern Stop-VotedLocally m∈ sb∉ ph≡ p≢L lch vch =
  _ , stop (LocalStep (VoteBlock m∈ sb∉ ph≡ p≢L lch vch)) , refl
pattern Continue-RegisterVote m∈ sb∉ s→ α≡ =
  _ , silent (LocalStep (RegisterVote m∈ sb∉)) s→ , α≡

pattern _⊣_ s→ α≡ = _ , s→ , α≡

data IsVote : Message → Type where
  isVote : IsVote (Vote sb)

instance
  Dec-IsVote : IsVote ⁇¹
  Dec-IsVote {Propose _} .dec = no λ ()
  Dec-IsVote {Vote _}    .dec = yes isVote

CanRegisterVote : ∀ p ⦃ _ : Honest p ⦄ → GlobalState → Type
CanRegisterVote p s = let ls = s ＠ p in
  ∃ λ m → m ∈ ls .inbox
        × IsVote m
        × m ∙signedBlock ∉ map _∙signedBlock (ls .db)

instance
  Dec-CanRegisterVote : ⦃ _ : Honest p ⦄ → CanRegisterVote p s ⁇
  Dec-CanRegisterVote {p}{s} .dec
    with ls ← s ＠ p
    with ¿ Any (λ m → IsVote m × (m ∙signedBlock ∉ map _∙signedBlock (ls . db))) (ls .inbox) ¿
  ... | no m∉
    = no λ (_ , m∈ , isV , sb∉) → m∉ $ L.Any.map (λ where refl → isV , sb∉) m∈
  ... | yes m∈
    = yes $ satisfied′ m∈

CanRegisterVote+Action : ∀ α p ⦃ _ : Honest p ⦄ → GlobalState → Type
CanRegisterVote+Action α p s =
  Σ (CanRegisterVote p s) λ (_ , m∈ , _) →
    ValidAction α (registerVote′ s p m∈)

instance
  Dec-CanRegisterVote+Action :
    ⦃ _ : Honest p ⦄ →
    ⦃ ∀ {s} → ValidAction α s ⁇ ⦄ →
    CanRegisterVote+Action α p s ⁇
  Dec-CanRegisterVote+Action {p}{α}{s} .dec
    with ¿ (let ls = s ＠ p in
           Any (λ (m , m∈) → IsVote m
                           × m ∙signedBlock ∉ map _∙signedBlock (ls . db)
                           × ValidAction α (registerVote′ s p m∈))
               (enumerate∈ $ ls .inbox))
         ¿
  ... | yes i∈
    with (Vote sb , m∈) , _ , isV , sb∉ , vα ← satisfied′ i∈
    = yes ((-, m∈ , isV , sb∉) , vα)
  ... | no i∉
    = no λ ((_ , m∈ , isV , sb∉) , vα) →
    let
      ls = s ＠ p

      QED : ∃ λ mm∈ → let (m , m∈) = mm∈ in
          ( IsVote m
          × m ∙signedBlock ∉ map _∙signedBlock (ls . db)
          × ValidAction α (registerVote′ s p m∈)
          ) × (mm∈ ∈ enumerate∈ (ls .inbox))
      QED = (_ , m∈) , (isV , sb∉ , vα) , ∈-mapWith∈⁺ m∈
    in
      i∉ (∃⇒Any QED)

  {-# TERMINATING #-} -- TODO: well-foundedness via `registerVote-totalInboxSize≡`
  Dec-ValidAction : ValidAction ⁇²
  Dec-ValidAction {x = Propose p ch txs}{s} .dec
    with ¿ Honest p ¿
  ... | no ¬hp = no (¬hp ∘ ValidAction-Propose⇒Honest)
  ... | yes hp = QED ⦃ hp ⦄
    where
    _b = ⟨ ch ♯ , s .e-now , txs ⟩

    QED : ⦃ _ : Honest p ⦄ → Dec (∃Propose s ch txs p)
    QED
      with ¿ ValidChain (_b ∷ ch) ¿
    ... | no ¬vch = no (¬vch ∘ ValidAction-Propose⇒ValidChain)
    ... | yes vch
      with p ≟ epochLeader (s .e-now)
    ... | no p≢L = no (p≢L ∘ ValidAction-Propose⇒p≡L)
    ... | yes p≡L
      with (s ＠ p) .phase ≟ Ready
    ... | no ph≢ = no (ph≢ ∘ ValidAction-Propose⇒ph≡)
    ... | yes ph≡
      with ¿ ch longest-notarized-chain-∈ ((s ＠ p) .db) ¿
    ... | yes lch
      = yes $ Stop-ProposedLocally ph≡ p≡L lch vch
    ... | no ¬lch
      with ∃Honest? (λ hp′ → CanRegisterVote+Action _ _ ⦃ hp′ ⦄ s)
                    ⦃ (λ {_}{hp′} → Dec-CanRegisterVote+Action ⦃ hp′ ⦄) ⦄
    ... | no ∄hon
      = no λ where
        (Stop-ProposedLocally _ _ lch _) → ¬lch lch
        (Continue-RegisterVote m∈ sb∉ s→ α≡) → let ∃lch = s→ ⊣ α≡ in
          ∄hon (-, hp⇒∈hon it , (-, m∈ , isVote , sb∉) , ∃lch)
    ... | yes (p′ , p∈′ , (m , m∈ , isVote , sb∉) , ∃lch@(s→ ⊣ α≡)) =
      let
        instance hp′ = ∈hon⇒hp p∈′
        s′ = registerVote′ s p′ ⦃ hp′ ⦄ m∈
      in
      yes $ Continue-RegisterVote m∈ sb∉ s→ α≡
  Dec-ValidAction {x = Vote p ch txs}{s} .dec
    with ¿ Honest p ¿
  ... | no ¬hp = no (¬hp ∘ ValidAction-Vote⇒Honest)
  ... | yes hp = QED ⦃ hp ⦄
    where
    _b = ⟨ ch ♯ , s .e-now , txs ⟩
    sᵖ = signBlock (epochLeader $ s .e-now) _b
    mᵖ = Propose sᵖ

    QED : ⦃ _ : Honest p ⦄ → Dec (∃Vote s ch txs p)
    QED
      with ¿ ValidChain (_b ∷ ch) ¿
    ... | no ¬vch = no (¬vch ∘ ValidAction-Vote⇒ValidChain)
    ... | yes vch
      with ¿ AnyFirst (mᵖ ≡_) ((s ＠ p) .inbox) ¿
    ... | no m∉ = no (m∉ ∘ ValidAction-Vote⇒m∈)
    ... | yes m∈
      with ¿ sᵖ ∈ map _∙signedBlock ((s ＠ p) .db) ¿
    ... | yes sb∈ = no ((_$ sb∈) ∘ ValidAction-Vote⇒sb∉)
    ... | no sb∉
      with (s ＠ p) .phase ≟ Ready
    ... | no ph≢ = no (ph≢ ∘ ValidAction-Vote⇒ph≡)
    ... | yes ph≡
      with p ≟ epochLeader (s .e-now)
    ... | yes p≡L = no ((_$ p≡L) ∘ ValidAction-Vote⇒p≢L)
    ... | no p≢L
      with ¿ ch longest-notarized-chain-∈ ((s ＠ p) .db) ¿
    ... | yes lch
      = yes $ Stop-VotedLocally m∈ sb∉ ph≡ p≢L lch vch
    ... | no ¬lch
      with ∃Honest? (λ hp′ → CanRegisterVote+Action _ _ ⦃ hp′ ⦄ s)
                    ⦃ (λ {_}{hp′} → Dec-CanRegisterVote+Action ⦃ hp′ ⦄) ⦄
    ... | no ∄hon
      = no λ where
        (Stop-VotedLocally _ _ _ _ lch _) → ¬lch lch
        (Continue-RegisterVote m∈ sb∉ s→ α≡) → let ∃lch = s→ ⊣ α≡ in
          ∄hon (-, hp⇒∈hon it , (-, m∈ , isVote , sb∉) , ∃lch)
    ... | yes (p′ , p∈′ , (m , m∈ , isVote , sb∉) , ∃lch@(s→ ⊣ α≡)) =
      let
        instance hp′ = ∈hon⇒hp p∈′
        s′ = registerVote′ s p′ ⦃ hp′ ⦄ m∈
      in
      yes $ Continue-RegisterVote m∈ sb∉ s→ α≡
  Dec-ValidAction {x = FinalizeBlock p ch b}{s} .dec
    with ¿ Honest p ¿
  ... | no ¬hp = no (¬hp ∘ ValidAction-Finalize⇒Honest)
  ... | yes hp
    = QED ⦃ hp ⦄
    where
    QED : ⦃ _ : Honest p ⦄ → Dec (∃FinalizedChain s ch b p)
    QED
      with ¿ ValidChain (b ∷ ch) ¿
    ... | no ¬vch = no (¬vch ∘ ValidAction-Finalize⇒ValidChain)
    ... | yes vch
      with ¿ FinalizedChain ((s ＠ p) .db) ch b ¿
    ... | yes fch
      = yes $ Stop-FinalizedLocally vch fch
    ... | no ¬fch
      with ∃Honest? (λ hp′ → CanRegisterVote+Action _ _ ⦃ hp′ ⦄ s)
                    ⦃ (λ {_}{hp′} → Dec-CanRegisterVote+Action ⦃ hp′ ⦄) ⦄
    ... | no ∄hon
      = no λ where
        (Stop-FinalizedLocally _ fch) → ¬fch fch
        (Continue-RegisterVote m∈ sb∉ s→ α≡) → let ∃fin = s→ ⊣ α≡ in
          ∄hon (-, hp⇒∈hon it , (-, m∈ , isVote , sb∉) , ∃fin)
    ... | yes (p′ , p∈′ , (m , m∈ , isVote , sb∉) , ∃fin@(s→ ⊣ α≡)) =
      let
        instance hp′ = ∈hon⇒hp p∈′
        s′ = registerVote′ s p′ ⦃ hp′ ⦄ m∈
      in
      yes $ Continue-RegisterVote m∈ sb∉ s→ α≡
  Dec-ValidAction {x = DishonestStep p m}{s} .dec
    with dec | dec
  ... | yes p | yes q
    = yes $ -, stop (DishonestLocalStep p q) , refl
  ... | no ¬p | _
    = no (¬p ∘ ValidAction-DishonestStep)
  ... | _ | no ¬p
    = no (¬p ∘ ValidAction-DishonestStep⇒NoForging)
  Dec-ValidAction {x = Deliver n}{s} .dec
    with index? n (s .networkBuffer)
  ... | yes (env , env∈ , refl)
    = yes $ -, stop (Deliver env∈) , refl
  ... | no ¬p
    = no (¬p ∘ ValidAction-Deliver n)
  Dec-ValidAction {x = Drop n}{s} .dec
    with index? n (s .networkBuffer)
  ... | yes (env , env∈ , refl)
    = yes $ -, stop (Drop env∈) , refl
  ... | no ¬p
    = no (¬p ∘ ValidAction-Drop n)
  Dec-ValidAction {x = AdvanceEpoch}{s} .dec
    = yes $ -, stop AdvanceEpoch , refl

-- ** termination based on decreasing total size of all replicas' inboxes
inboxSize : LocalState → ℕ
inboxSize = length ∘ inbox

registerVote-inboxSize≡ : ∀ (m∈ : m ∈ ls .inbox) →
  inboxSize ls ≡ 1 + inboxSize (registerVote ls m∈)
registerVote-inboxSize≡ {ls = ls} m∈ = L.length-removeAt′ (ls .inbox) (L.Any.index m∈)

∑ : ∀ {n} {A : Type} → (A → ℕ) → Vec A n → ℕ
∑ f = V.sum ∘ V.map f

open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _≡∎)

∑-incr : ∀ {n} {A : Type} (f : A → ℕ) {x} (xs : Vec A n) (i : Fin n) →
  f x ≡ 1 + f (V.lookup xs i) →
  ∑ f (xs V.[ i ]≔ x) ≡ 1 + ∑ f xs
∑-incr f {x} (x′ ∷ xs) fzero fx≡ =
  -- fx≡ : f x ≡ 1 + f x′
  begin≡
    f x + ∑ f xs
  ≡⟨ cong (_+ ∑ f xs) fx≡ ⟩
    1 + f x′ + ∑ f xs
  ≡∎
∑-incr f {x} (x′ ∷ xs) (fsuc i) fx≡ =
    f x′ + ∑ f (xs V.[ i ]≔ x)
  ≡⟨ (cong (f x′ +_) $ ∑-incr f xs i fx≡ ) ⟩
    f x′ + (1 + ∑ f xs)
  ≡⟨ Nat.+-suc _ _ ⟩
    1 + f x′ + ∑ f xs
  ≡∎

∑-decr : ∀ {n} {A : Type} (f : A → ℕ) {x} (xs : Vec A n) (i : Fin n) →
  f (V.lookup xs i) ≡ 1 + f x →
  ∑ f xs ≡ 1 + ∑ f (xs V.[ i ]≔ x)
∑-decr f {x} (x′ ∷ xs) fzero fx≡ =
  -- fx≡ : f x′ ≡ 1 + f x
  begin≡
    f x′ + ∑ f xs
  ≡⟨ cong (_+ ∑ f xs) fx≡ ⟩
    1 + f x + ∑ f xs
  ≡∎
∑-decr f {x} (x′ ∷ xs) (fsuc i) fx≡ = let xs′ = xs V.[ i ]≔ x in
    f x′ + ∑ f xs
  ≡⟨ (cong (f x′ +_) $ ∑-decr f xs i fx≡ ) ⟩
    f x′ + (1 + ∑ f xs′)
  ≡⟨ Nat.+-suc _ _ ⟩
    1 + f x′ + ∑ f xs′
  ≡∎

totalInboxSize : GlobalState → ℕ
totalInboxSize = ∑ inboxSize ∘ stateMap

registerVote-totalInboxSize≡ : ∀ ⦃ _ : Honest p ⦄ (m∈ : m ∈ (s ＠ p) .inbox) →
  totalInboxSize s ≡ 1 + totalInboxSize (registerVote′ s p m∈)
registerVote-totalInboxSize≡ {p}{m}{s} m∈ = let sm = s .stateMap in
  begin≡
    totalInboxSize s
  ≡⟨⟩
    ∑ inboxSize sm
  ≡⟨ ∑-decr inboxSize sm _ (registerVote-inboxSize≡ {ls = s ＠ p} m∈) ⟩
    1 + ∑ inboxSize (sm [ p ,· it ]≔ (registerVote (s ＠ p) m∈))
  ≡⟨⟩
    1 + ∑ inboxSize (registerVote′ s p m∈ .stateMap)
  ≡⟨⟩
    1 + totalInboxSize (registerVote′ s p m∈)
  ≡∎


-- ** evaluator

⟦_⟧ : ValidAction α s → GlobalState
⟦ (s′ , _) ⟧ = s′

-- ** soundness & completeness (by construction)

ValidAction-sound : (va : ValidAction α s) → s —→ᵉ ⟦ va ⟧
ValidAction-sound (_ , s→ , _) = s→

ValidAction-complete : (st : s —→ᵉ s′) → ValidAction (getLabel st) s
ValidAction-complete s→ = -, s→ , refl

-- ** valid traces

¬silent? : ∀ (st : s —→ s′) → Dec (¬Silent st)
¬silent? st with
  st
... | DishonestLocalStep _ _ = yes tt
... | Deliver _ = yes tt
... | Drop _ = yes tt
... | AdvanceEpoch = yes tt
... | LocalStep st
  with st
... | ProposeBlock _ _ _ _ = yes tt
... | VoteBlock _ _ _ _ _ _ = yes tt
... | FinalizeBlock _ _ _ _ = yes tt
... | RegisterVote _ _ = no λ ()

getLabelᵉ : (st : s —→ s′) → ¬Silent st → Action
getLabelᵉ st ¬sil = getLabel (stop st ⦃ ¬sil ⦄)

getLabel? : (s —→ s′) → Maybe Action
getLabel? st with ¬silent? st
... | yes ¬s = just (getLabelᵉ st ¬s)
... | no  _  = nothing

getLabels : (s′ —↠ s) → Actions
getLabels = λ where
  (_ ∎) → []
  (_ —→⟨ st ⟩ tr) → L.fromMaybe (getLabel? st) ++ getLabels tr

ValidTrace : Actions → GlobalState → Type
ValidTrace αs s = ∃ λ s′ → ∃ λ (st : s —↠ s′) → getLabels st ≡ αs

⟦_⟧∗ : ValidTrace αs s → GlobalState
⟦ s′ , _ ⟧∗ = s′

ValidTrace-sound : (vas : ValidTrace αs s) → s —↠ ⟦ vas ⟧∗
ValidTrace-sound (_ , s↠ , refl) = s↠

ValidTrace-complete : (st : s —↠ s′) → ValidTrace (getLabels st) s
ValidTrace-complete s↠ = -, s↠ , refl

mkSilentSteps : s —→ᵉ s′ → s —↠ s′
mkSilentSteps = λ where
  (silent s→ →s′) → _ —→⟨ s→ ⟩ mkSilentSteps →s′
  (stop s→) → _ —→⟨ s→ ⟩ _ ∎

open import Prelude.Closures _—→_ using (—↠-trans)

private
  getLabel≡ : (vα : ValidAction α s) → getLabel (ValidAction-sound vα) ≡ α
  getLabel≡ (_ , _ , α≡) = α≡

  getLabels≡ : (vαs : ValidTrace αs s) → getLabels (ValidTrace-sound vαs) ≡ αs
  getLabels≡ (_ , _ , refl) = refl

  getLabels≡-trans : (vα : ValidAction α s) (vαs : ValidTrace αs ⟦ vα ⟧) →
    getLabels (—↠-trans (mkSilentSteps $ ValidAction-sound vα) (ValidTrace-sound vαs))
    ≡ α ∷ αs
  getLabels≡-trans = λ where
    (silent (LocalStep (RegisterVote _ _)) st ⊣ α≡) → getLabels≡-trans (_ , st , α≡)
    (stop (LocalStep (ProposeBlock _ _ _ _)) ⊣ α≡) → cong₂ _∷_ α≡ ∘ getLabels≡
    (stop (LocalStep (VoteBlock _ _ _ _ _ _)) ⊣ α≡) → cong₂ _∷_ α≡ ∘ getLabels≡
    (stop (LocalStep (FinalizeBlock _ _ _ _)) ⊣ α≡) → cong₂ _∷_ α≡ ∘ getLabels≡
    (stop (DishonestLocalStep _ _) ⊣ α≡) → cong₂ _∷_ α≡ ∘ getLabels≡
    (stop (Deliver _) ⊣ α≡) → cong₂ _∷_ α≡ ∘ getLabels≡
    (stop AdvanceEpoch ⊣ α≡) → cong₂ _∷_ α≡ ∘ getLabels≡
    (stop (Drop _) ⊣ α≡) → cong₂ _∷_ α≡ ∘ getLabels≡

vα⇒ : ⦃ _ : Honest p ⦄ →
  (m∈ : Vote sb ∈ (s ＠ p) .inbox) →
  (sb∉ : sb ∉ map _∙signedBlock ((s ＠ p) .db)) →
  ValidAction α (registerVote′ s p m∈)
  ────────────────────────────────────
  ValidAction α s
vα⇒ m∈ sb∉ (_ , st , α≡) = Continue-RegisterVote m∈ sb∉ st α≡

vα⇒′ : ⦃ _ : Honest p ⦄ →
  (m∈ : Vote sb ∈ (s ＠ p) .inbox) →
  (sb∉ : sb ∉ map _∙signedBlock ((s ＠ p) .db)) →
  ValidTrace αs (registerVote′ s p m∈)
  ────────────────────────────────────
  ValidTrace αs s
vα⇒′ m∈ sb∉ (_ , st , α≡) = _ , (_ —→⟨ LocalStep $′ RegisterVote m∈ sb∉ ⟩ st) , α≡

ValidTrace-head :
  ValidTrace (α ∷ αs) s
  ─────────────────────
  ValidAction α s
ValidTrace-head = λ where
  ((_ —→⟨ st@(LocalStep (ProposeBlock _ _ _ _)) ⟩ tr) ⊣ refl) → -, stop st , refl
  ((_ —→⟨ st@(LocalStep (VoteBlock _ _ _ _ _ _)) ⟩ tr) ⊣ refl) → -, stop st , refl
  ((_ —→⟨ LocalStep (RegisterVote m∈ x) ⟩ tr) ⊣ α≡) → vα⇒ m∈ x $ ValidTrace-head (_ , tr , α≡)
  ((_ —→⟨ st@(LocalStep (FinalizeBlock _ _ _ _)) ⟩ tr) ⊣ refl) → -, stop st , refl
  ((_ —→⟨ st@(DishonestLocalStep _ _) ⟩ tr) ⊣ refl) → -, stop st , refl
  ((_ —→⟨ st@(Deliver _) ⟩ tr) ⊣ refl) → -, stop st , refl
  ((_ —→⟨ st@AdvanceEpoch ⟩ tr) ⊣ refl) → -, stop st , refl
  ((_ —→⟨ st@(Drop _) ⟩ tr) ⊣ refl) → -, stop st , refl

ValidTrace-tail :
  (vαs : ValidTrace (α ∷ αs) s) →
  ─────────────────────────────────────
  ValidTrace αs ⟦ ValidTrace-head vαs ⟧
ValidTrace-tail = λ where
  ((_ —→⟨ (LocalStep (ProposeBlock _ _ _ _)) ⟩ tr) ⊣ refl) → -, tr , refl
  ((_ —→⟨ (LocalStep (VoteBlock _ _ _ _ _ _)) ⟩ tr) ⊣ refl) → -, tr , refl
  ((_ —→⟨ LocalStep (RegisterVote m∈ x) ⟩ tr) ⊣ α≡) → ValidTrace-tail (_ , tr , α≡)
  ((_ —→⟨ (LocalStep (FinalizeBlock _ _ _ _)) ⟩ tr) ⊣ refl) → -, tr , refl
  ((_ —→⟨ (DishonestLocalStep _ _) ⟩ tr) ⊣ refl) → -, tr , refl
  ((_ —→⟨ (Deliver _) ⟩ tr) ⊣ refl) → -, tr , refl
  ((_ —→⟨ AdvanceEpoch ⟩ tr) ⊣ refl) → -, tr , refl
  ((_ —→⟨ (Drop _) ⟩ tr) ⊣ refl) → -, tr , refl

¬silent⇒s≡ :
  (s→s′ : s —→ s′) ⦃ _ : ¬Silent s→s′ ⦄
  (s→s″ : s —→ s″) ⦃ _ : ¬Silent s→s″ ⦄ →
  getLabelᵉ s→s′ it ≡ getLabelᵉ s→s″ it →
  s′ ≡ s″
¬silent⇒s≡ (LocalStep st) (DishonestLocalStep _ _) a≡ =
  ⊥-elim $ getLabel≢Dishonest _ st a≡
¬silent⇒s≡ (LocalStep st) (Deliver _) a≡ =
  ⊥-elim $ getLabel≢Deliver _ st a≡
¬silent⇒s≡ (LocalStep st) AdvanceEpoch a≡ =
  ⊥-elim $ getLabel≢Advance _ st a≡
¬silent⇒s≡ (LocalStep st) (Drop _) a≡ =
  ⊥-elim $ getLabel≢Drop _ st a≡
¬silent⇒s≡ (DishonestLocalStep _ _) (LocalStep st) a≡ =
  ⊥-elim $ getLabel≢Dishonest _ st (sym a≡)
¬silent⇒s≡ (DishonestLocalStep _ _) (DishonestLocalStep _ _) refl = refl
¬silent⇒s≡ (Deliver _) (LocalStep st) a≡ =
  ⊥-elim $ getLabel≢Deliver _ st (sym a≡)
¬silent⇒s≡ (Deliver env∈) (Deliver env∈′) a≡
  with i≡ ← Deliver-inj a≡
  with refl , refl ← index≡ _ _ env∈ i≡ env∈′ refl
  = refl
¬silent⇒s≡ AdvanceEpoch (LocalStep st) a≡ =
  ⊥-elim $ getLabel≢Advance _ st (sym a≡)
¬silent⇒s≡ AdvanceEpoch AdvanceEpoch refl = refl
¬silent⇒s≡ (Drop _) (LocalStep st) a≡ =
  ⊥-elim $ getLabel≢Drop _ st (sym a≡)
¬silent⇒s≡ (Drop env∈) (Drop env∈′) a≡
  with i≡ ← Drop-inj a≡
  with refl , refl ← index≡ _ _ env∈ i≡ env∈′ refl
  = refl
¬silent⇒s≡ (LocalStep (ProposeBlock _ _ _ _)) (LocalStep (ProposeBlock _ _ _ _)) refl = refl
¬silent⇒s≡ (LocalStep (VoteBlock m∈ _ _ _ _ _)) (LocalStep (VoteBlock m∈′ _ _ _ _ _)) refl
  rewrite AnyFirst-irrelevant ≡-irrelevant m∈ m∈′ = refl
¬silent⇒s≡ (LocalStep (FinalizeBlock _ _ _ _)) (LocalStep (FinalizeBlock _ _ _ _)) refl = refl

_≼db_ : GlobalState → GlobalState → Type
s ≼db s′ = ∀ {p} → ⦃ _ : Honest p ⦄ → (s ＠ p) .db ⊆ˢ (s′ ＠ p) .db

_≽db_ = flip _≼db_

_∪db_ : Op₂ GlobalState
s ∪db s′ = {!!}

postulate
  ∪-≼dbˡ : s  ≼db (s ∪db s′)
  ∪-≼dbʳ : s′ ≼db (s ∪db s′)

  -- vα≼ :
  --   ∙ s ≼db s′
  --   ∙ ValidAction α s
  --     ────────────────
  --     ValidAction α s′

  vαs≼ :
    ∙ s ≼db s′
    ∙ ValidTrace αs s
      ────────────────
      ValidTrace αs s′

  vαs≽ :
    ∙ s ≽db s′
    ∙ ValidTrace αs s
      ────────────────
      ValidTrace αs s′

{-
vas≼ {s}{s′} s≤ (_ , (_ ∎) , refl) = _ , (_ ∎) , refl
vas≼ {s}{s′}{as} s≤ (s″ , (_ —→⟨ AdvanceEpoch ⟩ ⋯→s″) , refl) = {!ValidTrace _  ∋ _ , ⋯→s″ , refl!}
vas≼ {s}{s′} s≤ (s″ , (_ —→⟨ s→⋯ ⟩ ⋯→s″) , αs≡)
--   with ¬silent? s→⋯
-- ... | yes ¬sil
--   = {!αs≡!}
-- ... | no sil
--   = {!αs≡!}
  with s→⋯
... | LocalStep (RegisterVote m∈ sb∉)
  = {!!}
... | LocalStep _
  = {!!}
... | AdvanceEpoch
  = {!!}
-}

{-
vα⇐ : ⦃ _ : Honest p ⦄ →
  (m∈ : Vote sb ∈ (s ＠ p) .inbox) →
  (sb∉ : sb ∉ map _∙signedBlock ((s ＠ p) .db)) →
  ValidAction α s
  ────────────────────────────────────
  ValidAction α (registerVote′ s p m∈)
vα⇐ {p}{sb} m∈ sb∉ (silent (LocalStep {p = p′} (RegisterVote m∈′ sb∉′)) st ⊣ α≡)
  with p ≟ p′
... | no p≢
  = {!!}
... | yes refl
  = {!!}
vα⇐ m∈ sb∉ (stop (LocalStep (ProposeBlock x x₁ x₂ x₃)) ⊣ refl) = {!!}
vα⇐ m∈ sb∉ (stop (LocalStep (VoteBlock m∈₁ x x₁ x₂ x₃ x₄)) ⊣ α≡) = {!!}
vα⇐ m∈ sb∉ (stop (LocalStep (FinalizeBlock ch b x x₁)) ⊣ refl) = stop (LocalStep (FinalizeBlock ch b x {!!})) ⊣ refl
vα⇐ m∈ sb∉ (stop (DishonestLocalStep x x₁) ⊣ α≡) = {!!}
vα⇐ m∈ sb∉ (stop (Deliver env∈) ⊣ α≡) = {!!}
vα⇐ m∈ sb∉ (stop AdvanceEpoch ⊣ refl) = stop AdvanceEpoch ⊣ refl
vα⇐ m∈ sb∉ (stop (Drop env∈) ⊣ α≡) = {!!}

vαs⇐ : ⦃ _ : Honest p ⦄ →
  (m∈ : Vote sb ∈ (s ＠ p) .inbox) →
  (sb∉ : sb ∉ map _∙signedBlock ((s ＠ p) .db)) →
  ValidTrace αs s
  ────────────────────────────────────
  ValidTrace αs (registerVote′ s p m∈)
vαs⇐ = {!!}
-}

vαs⇒ : (vα vα′ : ValidAction α s) →
  ValidTrace αs ⟦ vα ⟧ → ValidTrace αs ⟦ vα′ ⟧
vαs⇒ {a} {s} {αs} va@(s′ , _ , _) va'@(s″ , _ , _) vas =
  let
    s‴ = s′ ∪db s″

    vas‴ : ValidTrace αs s‴
    vas‴ = vαs≼ {s′}{s‴} (∪-≼dbˡ {s′}{s″}) vas

    vas″ : ValidTrace αs s″
    vas″ = vαs≽ {s‴}{s″} (∪-≼dbʳ {s″}{s′}) vas‴
  in
    vas″

-- ** case analysis on `αs`
-- vαs⇒ {a} {s} {[]} va va' vas = _ , (_ ∎) , refl
-- vαs⇒ {a0} {s} {a ∷ as} va va' (s' , (_ —→⟨ LocalStep st ⟩ tr) , a≡) = {!!}
-- vαs⇒ {a0} {s} {a ∷ as} va va' (s' , (_ —→⟨ DishonestLocalStep x x₁ ⟩ tr) , a≡) = {!!}
-- vαs⇒ {a0} {s} {a ∷ as} va va' (s' , (_ —→⟨ Deliver env∈ ⟩ tr) , a≡) = {!!}
-- vαs⇒ {a0} {s} {a ∷ as} va va' (s' , (_ —→⟨ Drop env∈ ⟩ tr) , a≡) = {!!}
-- vαs⇒ {a0} {s} {a ∷ as} va va' (s' , (_ —→⟨ AdvanceEpoch ⟩ tr) , a≡) = {!!}

-- ** case analysis on `α`

-- vαs⇒ {Propose x x₁ x₂} {s} {as} va va' vas = {!!}
-- vαs⇒ {Vote x x₁ x₂} {s} {as} va va' vas = {!!}
-- vαs⇒ {FinalizeBlock x x₁ x₂} {s} {as} va va' vas = {!!}
-- vαs⇒ {DishonestStep x x₁} {s} {as} va va' vas = {!!}
-- vαs⇒ {Deliver x} {s} {as} va va' vas = {!!}
-- vαs⇒ {Drop x} {s} {as} va va' vas = {!!}
-- vαs⇒ {AdvanceEpoch} {s} {as} va va' vas = {!!}

{-
vαs⇒ {a}{s}{as} (s' , silent (LocalStep {p} (RegisterVote m∈ sb∉)) ⋯→s' , eq) va' vas
  = vas'
  where
  -- s→⋯ : s —→ registerVote s ...
  -- ⋯→s' : registerVote s ... —→ᵉ s'
  -- eq : getLabel ⋯→s'' ≡ a

  vaa : ValidAction a (registerVote′ s p m∈)
  vaa = s' , ⋯→s' , eq

  -- va' : ValidAction a s

  vaa' : ValidAction a (registerVote′ s p m∈)
  vaa' = vα⇐ m∈ sb∉ va'

  -- vas : ValidTrace as s'

  vaas' : ValidTrace as ⟦ vaa' ⟧
  vaas' = vαs⇒ vaa vaa' vas

  vas' : ValidTrace as ⟦ va' ⟧
  vas' = {! vaas'!}
vαs⇒ {a}{s}{as} (s' , silent s→⋯ ⋯→s' , eq) (s'' , silent s→⋯' ⋯→s'' , eq') vas
  = vas'
  where
  -- s→⋯ : s —→ registerVote s ...
  -- ⋯→s' : registerVote s ... —→ᵉ s'
  -- eq : getLabel ⋯→s'' ≡ a

  -- vaa : ValidAction a (registerVote′ s p m∈)
  -- vaa = s' , ⋯→s' , eq

  -- s→s'' : s —→ s''

  -- vas : ValidTrace as s'

  vas' : ValidTrace as s''
  vas' = {!!}
vαs⇒ {a}{s}{as} (s' , silent s→⋯ ⋯→s' , eq) (s'' , stop s→s'' , eq') vas
  = vas'
  where
  -- s→⋯ : s —→ registerVote s ...
  -- ⋯→s' : registerVote s ... —→ᵉ s'
  -- eq : getLabel ⋯→s'' ≡ a

  -- vaa : ValidAction a (registerVote′ s p m∈)
  -- vaa = s' , ⋯→s' , eq

  -- s→s'' : s —→ s''

  -- vas : ValidTrace as s'

  vas' : ValidTrace as s''
  vas' = {!!}
vαs⇒ {a}{s}{as} (s' , stop s→s' , eq) (s'' , silent s→⋯ ⋯→s'' , eq') vas = QED
  where
  -- s→s' : s —→ s'
  -- eq : getLabel s→s' ≡ a
  -- s→⋯ : s —→ registerVote s ...
  -- ⋯→s'' : registerVote s ... —→ᵉ s''
  -- eq' : getLabel ⋯→s'' ≡ a
  -- vas : ValidTrace as s'

  QED : ValidTrace as s''
  QED = {!!}
vαs⇒ {a}{s}{as} (s' , stop s→s' , eq) (s'' , stop s→s'' , eq') vas = QED
  where
  -- s→s' : s —→ s'
  -- eq : getLabel s→s' ≡ a
  -- s→s'' : s —→ s''
  -- eq' : getLabel s→s'' ≡ a
  -- vas : ValidTrace as s'

  s≡ : s' ≡ s''
  s≡ = ¬silent⇒s≡ s→s' s→s'' (trans eq (sym eq'))

  QED : ValidTrace as s''
  QED = subst (ValidTrace _) s≡ vas
-}

{-
vαs⇒ vα vα′ = λ where
  ((_ —→⟨ (LocalStep (ProposeBlock _ _ _ _)) ⟩ tr) ⊣ refl) → {!!}
  ((_ —→⟨ (LocalStep (VoteBlock _ _ _ _ _ _)) ⟩ tr) ⊣ refl) → {!!}
  ((_ —→⟨ LocalStep (RegisterVote m∈ x) ⟩ tr) ⊣ α≡) → {!!}
  ((_ —→⟨ (LocalStep (FinalizeBlock _ _ _ _)) ⟩ tr) ⊣ refl) → {!!}
  ((_ —→⟨ (DishonestLocalStep _ _) ⟩ tr) ⊣ refl) → {!!}
  ((_ —→⟨ (Deliver _) ⟩ tr) ⊣ refl) → {!!}
  ((_ —→⟨ AdvanceEpoch ⟩ tr) ⊣ refl) → {!!}
  -- _ , (_ —→⟨ AdvanceEpoch ⟩ {!tr!}) , refl
      -- vαs⇒ (-, stop AdvanceEpoch , refl) {!-, stop AdvanceEpoch , refl!} (_ , tr , {!!})
  ((_ —→⟨ (Drop _) ⟩ tr) ⊣ refl) → {!!}
-}

instance
  Dec-ValidTrace : ValidTrace ⁇²
  Dec-ValidTrace {x = tr}{s} .dec with tr
  ... | [] = yes (-, (_ ∎) , refl)
  ... | α ∷ αs
    with ¿ ValidAction α s ¿
  ... | no ¬vα = no (¬vα ∘ ValidTrace-head)
  ... | yes vα
    with ¿ ValidTrace αs ⟦ vα ⟧ ¿
  ... | no ¬vαs
    = no λ vαs → ¬vαs $ vαs⇒ (ValidTrace-head vαs) vα (ValidTrace-tail vαs)
  ... | yes vαs
    = yes (-, —↠-trans (mkSilentSteps $ ValidAction-sound vα) (ValidTrace-sound vαs)
            , getLabels≡-trans vα vαs)
-- -}
-- -}
-- -}
-- -}
-- -}
