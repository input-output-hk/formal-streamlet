-- {-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.TraceVerifier.Intrinsic (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Decidability ⋯

-- * verifying a whole trace

data Action : Type where
  Propose Vote  : Pid → Chain → List Transaction → Action
  RegisterVote  : Pid → ℕ → Action
  FinalizeBlock : Pid → Chain → Block → Action
  DishonestStep : Pid → Message → Action
  Deliver Drop  : ℕ → Action
  AdvanceEpoch  : Action

Actions = List Action

private variable
  α α′ : Action
  αs αs′ : Actions

-- ** labels

private
  toℕ : ∀ {A : Type} {x} {xs : List A} → x ∈ xs → ℕ
  toℕ = Fi.toℕ ∘ L.Any.index

getLabel : (s —→ s′) → Action
getLabel {s}{s′} = λ where
  (LocalStep {p = p} {mm = mm} st) → case st of λ where
    (ProposeBlock {ch = ch} {txs = txs} _ _ _ _) → Propose p ch txs
    (VoteBlock {ch = ch} {txs = txs} _ _ _ _ _ _) → Vote p ch txs
    (RegisterVote m∈ _) → RegisterVote p (toℕ m∈)
    (FinalizeBlock ch b _ _) → FinalizeBlock p ch b
  (DishonestLocalStep {p = p} {m = m} _ _) → DishonestStep p m
  (Deliver env∈) → Deliver (toℕ env∈)
  (Drop env∈) → Drop (toℕ env∈)
  AdvanceEpoch → AdvanceEpoch

private
  getLabel≢Deliver : ∀ {n} ⦃ _ : Honest p ⦄ s (st : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    getLabel (LocalStep {s = s} st) ≢ Deliver n
  getLabel≢Deliver _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (RegisterVote _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

  getLabel≢Drop : ∀ {n} ⦃ _ : Honest p ⦄ s (st : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    getLabel (LocalStep {s = s} st) ≢ Drop n
  getLabel≢Drop _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (RegisterVote _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

  getLabel≢Dishonest : ∀ ⦃ _ : Honest p ⦄ s (st : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    getLabel (LocalStep {s = s} st) ≢ DishonestStep p′ m
  getLabel≢Dishonest _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (RegisterVote _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

  getLabel≢Advance : ∀ ⦃ _ : Honest p ⦄ s (st : p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′) →
    getLabel (LocalStep {s = s} st) ≢ AdvanceEpoch
  getLabel≢Advance _ = λ where
    (ProposeBlock _ _ _ _) → λ ()
    (VoteBlock _ _ _ _ _ _) → λ ()
    (RegisterVote _ _) → λ ()
    (FinalizeBlock _ _ _ _) → λ ()

getLabels : (s′ ↞— s) → Actions
getLabels = λ where
  (_ ∎) → []
  (_ ⟨ st ⟩←— tr) → getLabel st ∷ getLabels tr

-- ** validity of actions

ValidAction : Action → GlobalState → Type
ValidAction α s = ∃ λ s′ → ∃ λ (st : s —→ s′) → getLabel st ≡ α

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

instance
  Dec-ValidAction : ValidAction ⁇²
  Dec-ValidAction {x = Propose p ch txs}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (_ , LocalStep ⦃ hp ⦄ (ProposeBlock _ _ _ _) , refl) → ¬hp hp
  ... | yes hp
    with dec | dec | dec | dec
  ... | no ¬p | _ | _ | _
    = no λ where (_ , LocalStep (ProposeBlock p _ _ _) , refl) → ¬p p
  ... | _ | no ¬p | _ | _
    = no λ where (_ , LocalStep (ProposeBlock _ p _ _) , refl) → ¬p p
  ... | _ | _ | no ¬p | _
    = no λ where (_ , LocalStep (ProposeBlock _ _ p _) , refl) → ¬p p
  ... | _ | _ | _ | no ¬p
    = no λ where (_ , LocalStep (ProposeBlock _ _ _ p) , refl) → ¬p p
  ... | yes _p | yes q | yes w | yes x
    = yes $ -, LocalStep ⦃ hp ⦄ (ProposeBlock _p q w x) , refl
  Dec-ValidAction {x = Vote p ch txs}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (_ , LocalStep ⦃ hp ⦄ (VoteBlock _ _ _ _ _ _) , refl) → ¬hp hp
  ... | yes hp
    with dec | dec | dec | dec | dec | dec
  ... | no ¬p | _ | _ | _ | _ | _
    = no λ where (_ , LocalStep (VoteBlock p _ _ _ _ _) , refl) → ¬p p
  ... | _ | no ¬p | _ | _ | _ | _
    = no λ where (_ , LocalStep (VoteBlock _ p _ _ _ _) , refl) → ¬p p
  ... | _ | _ | no ¬p | _ | _ | _
    = no λ where (_ , LocalStep (VoteBlock _ _ p _ _ _) , refl) → ¬p p
  ... | _ | _ | _ | no ¬p | _ | _
    = no λ where (_ , LocalStep (VoteBlock _ _ _ p _ _) , refl) → ¬p p
  ... | _ | _ | _ | _ | no ¬p | _
    = no λ where (_ , LocalStep (VoteBlock _ _ _ _ p _) , refl) → ¬p p
  ... | _ | _ | _ | _ | _ | no ¬p
    = no λ where (_ , LocalStep (VoteBlock _ _ _ _ _ p) , refl) → ¬p p
  ... | yes _p | yes q | yes w | yes x | yes y | yes z
    = yes $ -, LocalStep ⦃ hp ⦄ (VoteBlock _p q w x y z) , refl
  Dec-ValidAction {x = RegisterVote p n}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (_ , LocalStep ⦃ hp ⦄ (RegisterVote _ _) , refl) → ¬hp hp
  ... | yes hp
    with index? n ((s ＠ p) ⦃ hp ⦄ .inbox)
  ... | no ¬p
    = no λ where (_ , LocalStep (RegisterVote p q) , refl) → ¬p (-, p , refl)
  ... | yes (m , m∈ , n≡)
    with m
  ... | Propose sb
    = no λ where
    (_ , LocalStep (RegisterVote m∈′ _) , refl) →
      contradict $ index≡ _ ((s ＠ p) ⦃ hp ⦄ .inbox) m∈ n≡ m∈′ refl .proj₁
  ... | Vote sb
    with ¿ sb ∈ map _∙signedBlock ((s ＠ p) ⦃ hp ⦄ .db) ¿
  ... | yes sb∈
    = no λ where
    (_ , LocalStep (RegisterVote m∈′ sb∉) , refl) →
      sb∉ $
        subst (_∈ _)
              (Vote-inj $ index≡ _ ((s ＠ p) ⦃ hp ⦄ .inbox) m∈ n≡ m∈′ refl .proj₁)
              sb∈
  ... | no sb∉
    = yes $ -, LocalStep ⦃ hp ⦄ (RegisterVote m∈ sb∉) , cong (RegisterVote p) n≡
  Dec-ValidAction {x = FinalizeBlock p ch b}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (_ , LocalStep ⦃ hp ⦄ (FinalizeBlock _ _ _ _) , refl) → ¬hp hp
  ... | yes hp
    with dec | dec
  ... | no ¬p | _
    = no λ where (_ , LocalStep (FinalizeBlock _ _ p _) , refl) → ¬p p
  ... | _ | no ¬p
    = no λ where (_ , LocalStep (FinalizeBlock _ _ _ p) , refl) → ¬p p
  ... | yes _p | yes q
    = yes $ -, LocalStep ⦃ hp ⦄ (FinalizeBlock _ _ _p q) , refl
  Dec-ValidAction {x = DishonestStep p m}{s} .dec
    with dec | dec
  ... | no ¬p | _
    = no λ where (_ , DishonestLocalStep p _ , refl) → ¬p p
                 (_ , LocalStep st , l≡) → ⊥-elim $ getLabel≢Dishonest s st l≡
  ... | _ | no ¬p
    = no λ where (_ , DishonestLocalStep _ p , refl) → ¬p p
                 (_ , LocalStep st , l≡) → ⊥-elim $ getLabel≢Dishonest s st l≡
  ... | yes p | yes q
    = yes $ -, DishonestLocalStep p q , refl
  Dec-ValidAction {x = Deliver n}{s} .dec
    with index? n (s .networkBuffer)
  ... | no ¬p
    = no λ where (_ , Deliver p , refl) → ¬p (-, p , refl)
                 (_ , LocalStep st , l≡) → ⊥-elim $ getLabel≢Deliver s st l≡
  ... | yes (env , env∈ , refl)
    = yes $ -, Deliver env∈ , refl
  Dec-ValidAction {x = Drop n}{s} .dec
    with index? n (s .networkBuffer)
  ... | no ¬p
    = no λ where (_ , Drop p , refl) → ¬p (-, p , refl)
                 (_ , LocalStep st , l≡) → ⊥-elim $ getLabel≢Drop s st l≡
  ... | yes (env , env∈ , refl)
    = yes $ -, Drop env∈ , refl
  Dec-ValidAction {x = AdvanceEpoch}{s} .dec = yes $ -, AdvanceEpoch , refl

⟦_⟧ : ValidAction α s → GlobalState
⟦ (s′ , _) ⟧ = s′

-- We're sound & complete by construction!
ValidAction-sound : (va : ValidAction α s) → s —→ ⟦ va ⟧
ValidAction-sound (_ , s→ , _) = s→

ValidAction-complete : (st : s —→ s′) → ValidAction (getLabel st) s
ValidAction-complete s→ = -, s→ , refl

ValidTrace : Actions → GlobalState → Type
ValidTrace αs s = ∃ λ s′ → ∃ λ (st : s′ ↞— s) → getLabels st ≡ αs

⟦_⟧∗ : ValidTrace αs s → GlobalState
⟦ s′ , _ ⟧∗ = s′

ValidTrace-sound : (vas : ValidTrace αs s) → ⟦ vas ⟧∗ ↞— s
ValidTrace-sound (_ , s↠ , refl) = s↠

ValidTrace-complete : (st : s′ ↞— s) → ValidTrace (getLabels st) s
ValidTrace-complete s↠ = -, s↠ , refl

private
  variable
    A : Type
    x y : A
    xs ys : List A

  ∷-inj : (List A ∋ x ∷ xs) ≡ (y ∷ ys) → (x ≡ y) × (xs ≡ ys)
  ∷-inj refl = refl , refl

  record _≡∈_ (x∈ : x ∈ xs) (y∈ : y ∈ xs) : Type where
    constructor _⊢_
    field x≡  : x ≡ y
          x∈≈ : x∈ ≡ subst˘ (_∈ _) x≡ y∈

  index≡∈ : {x∈ : x ∈ xs} {y∈ : y ∈ xs} → x∈ ≡∈ y∈ → L.Any.index x∈ ≡ L.Any.index y∈
  index≡∈ (refl ⊢ refl) = refl

  index-injective : (x∈ x∈′ : x ∈ xs) → L.Any.index x∈ ≡ L.Any.index x∈′ → x∈ ≡ x∈′
  index-injective (here refl) (here refl) _ = refl
  index-injective (there x∈) (there x∈′) i≡ =
    cong there $ index-injective x∈ x∈′ (Fi.suc-injective i≡)

  index-injective≈ : (x∈ : x ∈ xs) (y∈ : y ∈ xs) → L.Any.index x∈ ≡ L.Any.index y∈ → x∈ ≡∈ y∈
  index-injective≈ (here refl) (here refl) _ = refl ⊢ refl
  index-injective≈ (there x∈) (there y∈) i≡
    with refl ⊢ x∈≈y∈ ← index-injective≈ x∈ y∈ (Fi.suc-injective i≡)
    = refl ⊢ cong there x∈≈y∈

  toℕ-injective : (x∈ x∈′ : x ∈ xs) → toℕ x∈ ≡ toℕ x∈′ → x∈ ≡ x∈′
  toℕ-injective x∈ x∈′ = index-injective x∈ x∈′ ∘ Fi.toℕ-injective

  toℕ-injective≈ : (x∈ : x ∈ xs) (y∈ : y ∈ xs) → toℕ x∈ ≡ toℕ y∈ → x∈ ≡∈ y∈
  toℕ-injective≈ x∈ y∈ = index-injective≈ x∈ y∈ ∘ Fi.toℕ-injective

  variable
    env∈ : env ∈ envs
    env∈′ : env′ ∈ envs

  Drop-inj : ∀ {n m : ℕ} → Drop n ≡ Drop m → n ≡ m
  Drop-inj refl = refl

  Deliver-inj : ∀ {n m : ℕ} → Deliver n ≡ Deliver m → n ≡ m
  Deliver-inj refl = refl

  dropMsg≈ : env∈ ≡∈ env∈′ → dropMsg s env∈ ≡ dropMsg s env∈′
  dropMsg≈ (refl ⊢ refl) = refl

  deliverMsg≈ : env∈ ≡∈ env∈′ → deliverMsg s env∈ ≡ deliverMsg s env∈′
  deliverMsg≈ (refl ⊢ refl) = refl

  Propose-inj : Propose p ch txs ≡ Propose p′ ch′ txs′ →
    (p ≡ p′) × (ch ≡ ch′) × (txs ≡ txs′)
  Propose-inj refl = refl , refl , refl

  VoteAction-inj : Vote p ch txs ≡ Vote p′ ch′ txs′ →
    (p ≡ p′) × (ch ≡ ch′) × (txs ≡ txs′)
  VoteAction-inj refl = refl , refl , refl

  Register-inj : ∀ {p p′ : Pid} {n m : ℕ} → RegisterVote p n ≡ RegisterVote p′ m →
    (p ≡ p′) × (n ≡ m)
  Register-inj refl = refl , refl

vαs≡ : (vαs vαs′ : ValidTrace αs s) → ⟦ vαs ⟧∗ ≡ ⟦ vαs′ ⟧∗
vαs≡ {αs = αs} (_ , tr , αs≡₀) (_ , tr′ , αs≡)
  with tr | tr′
... | _ ∎ | _ ∎ = refl
... | _ ∎ | _ ⟨ _ ⟩←— _ = ⊥-elim $ case trans αs≡₀ (sym αs≡) of λ ()
... | _ ⟨ _ ⟩←— _ | _ ∎ = ⊥-elim $ case trans αs≡₀ (sym αs≡) of λ ()
... | ≫s ⟨ st ∣ s ⟩←— tr | ≫s′ ⟨ st′ ∣ s′ ⟩←— tr′
  with α ∷ αs ← αs
  with IH ← (λ αs≡ αs≡′ → vαs≡ {αs = αs} (_ , tr , αs≡) (_ , tr′ , αs≡′))
  with refl ← αs≡₀
  with α≡ , αs≡ ← ∷-inj αs≡
  with st | st′
... | LocalStep st | DishonestLocalStep _ _ = ⊥-elim $ getLabel≢Dishonest s st (sym α≡)
... | LocalStep st | Deliver _ = ⊥-elim $ getLabel≢Deliver s st (sym α≡)
... | LocalStep st | AdvanceEpoch = ⊥-elim $ getLabel≢Advance s st (sym α≡)
... | LocalStep st | Drop _ = ⊥-elim $ getLabel≢Drop s st (sym α≡)
... | DishonestLocalStep _ _ | LocalStep st = ⊥-elim $ getLabel≢Dishonest s′ st α≡
... | Deliver _ | LocalStep st = ⊥-elim $ getLabel≢Deliver s′ st α≡
... | AdvanceEpoch | LocalStep st = ⊥-elim $ getLabel≢Advance s′ st α≡
... | Drop _ | LocalStep st = ⊥-elim $ getLabel≢Drop s′ st α≡
... | AdvanceEpoch | AdvanceEpoch
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  = refl
... | DishonestLocalStep _ _ | DishonestLocalStep _ _
  with refl ← α≡
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  = refl
... | Deliver env∈ | Deliver env∈′
  with i≡ ← Deliver-inj α≡
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  with refl ⊢ refl ← toℕ-injective≈ env∈′ env∈ i≡
  = refl
... | Drop env∈ | Drop env∈′
  with i≡ ← Drop-inj α≡
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  with refl ⊢ refl ← toℕ-injective≈ env∈′ env∈ i≡
  = refl
... | LocalStep st | LocalStep st′
  with st | st′
... | ProposeBlock _ _ _ _ | ProposeBlock _ _ _ _
  with refl , refl , refl ← Propose-inj α≡
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  = refl
... | VoteBlock m∈ _ _ _ _ _ | VoteBlock m∈′ _ _ _ _ _
  with refl , refl , refl ← VoteAction-inj α≡
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  with refl ← AnyFirst-irrelevant (λ where refl refl → refl) m∈ m∈′
  = refl
... | RegisterVote m∈ _ | RegisterVote m∈′ _
  with refl , i≡ ← Register-inj α≡
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  with refl ⊢ refl ← toℕ-injective≈ m∈′ m∈ i≡
  = refl
... | FinalizeBlock _ _ _ _ | FinalizeBlock _ _ _ _
  with refl ← α≡
  with refl ← (s ≡ s′) ∋ IH refl (∷-inj αs≡ .proj₂)
  = refl

vα⇒ : (vαs vαs′ : ValidTrace αs s) →
  ValidAction α ⟦ vαs ⟧∗ → ValidAction α ⟦ vαs′ ⟧∗
vα⇒ vαs vαs′ = subst (ValidAction _) (vαs≡ vαs vαs′)

private
  getLabel≡ : (vα : ValidAction α s) → getLabel (ValidAction-sound vα) ≡ α
  getLabel≡ (_ , _ , α≡) = α≡

  getLabels≡ : (vαs : ValidTrace αs s) → getLabels (ValidTrace-sound vαs) ≡ αs
  getLabels≡ (_ , _ , refl) = refl

instance
  Dec-ValidTrace : ValidTrace ⁇²
  Dec-ValidTrace {x = tr}{s} .dec with tr
  ... | [] = yes (-, (_ ∎) , refl)
  ... | α ∷ αs
    with ¿ ValidTrace αs s ¿
  ... | no ¬vαs = no λ where
    (_ , (_ ⟨ st ⟩←— tr ) , refl) → ¬vαs (-, tr , refl)
  ... | yes vαs
    with ¿ ValidAction α ⟦ vαs ⟧∗ ¿
  ... | no ¬vα = no λ where
    (_ , (_ ⟨ st ∣ s′ ⟩←— tr) , refl) →
      ¬vα $ vα⇒ (ValidTrace-complete tr) vαs (ValidAction-complete st)
  ... | yes vα
    = yes $ -, (_ ⟨ ValidAction-sound vα ⟩←— ValidTrace-sound vαs)
            , cong₂ _∷_ (getLabel≡ vα) (getLabels≡ vαs)
