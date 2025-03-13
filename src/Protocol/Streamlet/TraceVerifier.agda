{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.TraceVerifier (⋯ : _) (open Assumptions ⋯) where

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

private
  toℕ : ∀ {A : Type} {x} {xs : List A} → x ∈ xs → ℕ
  toℕ = Fi.toℕ ∘ L.Any.index

data ValidAction : Action → GlobalState → Type where
  Vote : ⦃ _ : Honest p ⦄ →
    let ls = (s ＠ p); open ∣VoteBlock∣ p s ch txs in
    ∀ (m∈ : AnyFirst (Mᵖ ≡_) (ls .inbox)) →
    .(SBᵖ ∉ map _∙signedBlock (ls .db)) →
    .(ls .phase ≡ Ready) →
    .(p ≢ L) →
    .(ch longest-notarized-chain-∈ ls .db) →
    .(ValidChain (B ∷ ch)) →
      ValidAction (Vote p ch txs) s

  Propose : ⦃ _ : Honest p ⦄ →
    let ls = (s ＠ p); open ∣ProposeBlock∣ p s ch txs in
    .(ls .phase ≡ Ready) →
    .(p ≡ L) →
    .(ch longest-notarized-chain-∈ ls .db) →
    .(ValidChain (B ∷ ch)) →
      ValidAction (Propose p ch txs) s

  RegisterVote : ∀ {n} → ⦃ _ : Honest p ⦄ →
    let ls = (s ＠ p) in
    ∀ (m∈ : Vote sb ∈ ls .inbox) →
      toℕ m∈ ≡ n →
    .(sb ∉ map _∙signedBlock (ls .db)) →
      ValidAction (RegisterVote p n) s

  FinalizeBlock : ⦃ _ : Honest p ⦄ →
    let ls = (s ＠ p) in
    .(ValidChain (b ∷ ch)) →
    .(FinalizedChain (ls .db) ch b) →
      ValidAction (FinalizeBlock p ch b) s

  DishonestStep :
    .(Dishonest p) →
    .(Honest (m ∙pid) → m ∈ s .history) →
      ValidAction (DishonestStep p m) s

  Deliver : ∀ {n} →
    ∀ (env∈ : env ∈ s .networkBuffer) →
      (toℕ env∈ ≡ n) →
      ValidAction (Deliver n) s

  Drop : ∀ {n} →
    ∀ (env∈ : env ∈ s .networkBuffer) →
      (toℕ env∈ ≡ n) →
      ValidAction (Drop n) s

  AdvanceEpoch :
      ValidAction AdvanceEpoch s

⟦_⟧ : ValidAction α s → GlobalState
⟦_⟧ {α}{s} = λ where
  (Vote {p = p} {ch = ch} {txs = txs} m∈ _ _ _ _ _) →
    let ls = s ＠ p; open ∣VoteBlock∣ p s ch txs in
    broadcast p (just M) $ updateLocal p (voteBlock ls m∈ M) s
  (Propose {p = p} {ch = ch} {txs = txs} _ _ _ _) →
    let ls = s ＠ p; open ∣ProposeBlock∣ p s ch txs in
    broadcast p (just M) $ updateLocal p (proposeBlock ls M) s
  (RegisterVote {p = p} {sb = sb} m∈ _ _) →
    let ls = s ＠ p in
    updateLocal p (registerVote ls m∈) s
  (FinalizeBlock {p = p} {ch = ch} _ _) →
    let ls = s ＠ p in
    updateLocal p (finalize ch ls) s
  (DishonestStep {p}{m} _ _) →
    broadcast p (just m) s
  (Deliver env∈ _) →
    deliverMsg s env∈
  (Drop env∈ _) →
    dropMsg s env∈
  AdvanceEpoch →
    advanceEpoch s

private
  ⟦⟧-subst :
    (vα : ValidAction α s) →
    (s≡ : s ≡ s′) →
    ⟦ subst (ValidAction α) s≡ vα ⟧ ≡ ⟦ vα ⟧
  ⟦⟧-subst _ refl = refl

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
  Dec-ValidAction {RegisterVote p n}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (RegisterVote ⦃ hp ⦄ _ _ _) → ¬hp hp
  ... | yes hp
    with index? n ((s ＠ p) ⦃ hp ⦄ .inbox)
  ... | no ¬p
    = no λ where (RegisterVote p q _) → ¬p (-, p , q)
  ... | yes (m , m∈ , n≡)
    with m
  ... | Propose sb
    = no λ where
    (RegisterVote m∈′ n≡′ _) →
      contradict $ index≡ _ ((s ＠ p) ⦃ hp ⦄ .inbox) m∈ n≡ m∈′ n≡′ .proj₁
  ... | Vote sb
    with ¿ sb ∈ map _∙signedBlock ((s ＠ p) ⦃ hp ⦄ .db) ¿
  ... | yes sb∈
    = no λ where
    (RegisterVote m∈′ n≡′ sb∉) →
      toRelevant sb∉ $
        subst (_∈ _) (Vote-inj $
          index≡ _ ((s ＠ p) ⦃ hp ⦄ .inbox) m∈ n≡ m∈′ n≡′ .proj₁) sb∈
  ... | no sb∉
    = yes $ RegisterVote ⦃ hp ⦄ m∈ n≡ sb∉
  Dec-ValidAction {Propose p ch txs}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (Propose ⦃ hp ⦄ _ _ _ _) → ¬hp hp
  ... | yes hp
    with dec | dec | dec | dec
  ... | no ¬p | _ | _ | _
    = no λ where (Propose p _ _ _) → ¬p (toRelevant p)
  ... | _ | no ¬p | _ | _
    = no λ where (Propose _ p _ _) → ¬p (toRelevant p)
  ... | _ | _ | no ¬p | _
    = no λ where (Propose _ _ p _) → ¬p (toRelevant p)
  ... | _ | _ | _ | no ¬p
    = no λ where (Propose _ _ _ p) → ¬p (toRelevant p)
  ... | yes _p | yes q | yes w | yes x
    = yes $ Propose ⦃ hp ⦄ _p q w x
  Dec-ValidAction {Vote p ch txs}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (Vote ⦃ hp ⦄ _ _ _ _ _ _) → ¬hp hp
  ... | yes hp
    with dec | dec | dec | dec | dec | dec
  ... | no ¬p | _ | _ | _ | _ | _
    = no λ where (Vote p _ _ _ _ _) → ¬p (toRelevant p)
  ... | _ | no ¬p | _ | _ | _ | _
    = no λ where (Vote _ p _ _ _ _) → ¬p (toRelevant p)
  ... | _ | _ | no ¬p | _ | _ | _
    = no λ where (Vote _ _ p _ _ _) → ¬p (toRelevant p)
  ... | _ | _ | _ | no ¬p | _ | _
    = no λ where (Vote _ _ _ p _ _) → ¬p (toRelevant p)
  ... | _ | _ | _ | _ | no ¬p | _
    = no λ where (Vote _ _ _ _ p _) → ¬p (toRelevant p)
  ... | _ | _ | _ | _ | _ | no ¬p
    = no λ where (Vote _ _ _ _ _ p) → ¬p (toRelevant p)
  ... | yes _p | yes q | yes w | yes x | yes y | yes z
    = yes $ Vote ⦃ hp ⦄ _p q w x y z
  Dec-ValidAction {FinalizeBlock p ch b}{s} .dec
    with honest? p
  ... | no ¬hp
    = no λ where (FinalizeBlock ⦃ hp ⦄ _ _) → ¬hp hp
  ... | yes hp
    with dec | dec
  ... | no ¬p | _
    = no λ where (FinalizeBlock p _) → ¬p (toRelevant p)
  ... | _ | no ¬p
    = no λ where (FinalizeBlock _ p) → ¬p (toRelevant p)
  ... | yes _p | yes q
    = yes $ FinalizeBlock ⦃ hp ⦄ _p q
  Dec-ValidAction {DishonestStep p m}{s} .dec
    with dec | dec
  ... | no ¬p | _
    = no λ where (DishonestStep p _) → ¬p (toRelevant p)
  ... | _ | no ¬p
    = no λ where (DishonestStep _ p) → ¬p (toRelevant p)
  ... | yes p | yes q
    = yes $ DishonestStep p q
  Dec-ValidAction {Deliver n}{s} .dec
    with index? n (s .networkBuffer)
  ... | no ¬p
    = no λ where (Deliver p q) → ¬p (-, p , q)
  ... | yes (env , env∈ , n≡)
    = yes $ Deliver env∈ n≡
  Dec-ValidAction {Drop n}{s} .dec
    with index? n (s .networkBuffer)
  ... | no ¬p = no λ where (Drop p q) → ¬p (-, p , q)
  ... | yes (env , env∈ , n≡)
    = yes $ Drop env∈ n≡
  Dec-ValidAction {AdvanceEpoch}{s} .dec
    = yes AdvanceEpoch

-- TODO: consider starting from non-initial state (c.f. Test/TraceVerifier2)
mutual
  data ValidTrace : Actions → Type where
    [] :
      ─────────────
      ValidTrace []

    _∷_⊣_ : ∀ α →
      ∀ (tr : ValidTrace αs) →
      ∙ ValidAction α ⟦ tr ⟧∗
        ───────────────────
        ValidTrace (α ∷ αs)

  ⟦_⟧∗ : ValidTrace αs → GlobalState
  ⟦_⟧∗ [] = initGlobalState
  ⟦_⟧∗ (_ ∷ _ ⊣ vα) = ⟦ vα ⟧

Irr-ValidAction : Irrelevant (ValidAction α s)
Irr-ValidAction (Propose ⦃ hp ⦄ _ _ _ _) (Propose ⦃ hp′ ⦄ _ _ _ _)
  rewrite Honest-irr hp hp′
  = refl
Irr-ValidAction (Vote ⦃ hp ⦄ m∈ _ _ _ _ _) (Vote ⦃ hp′ ⦄ m∈′ _ _ _ _ _)
  rewrite AnyFirst-irrelevant ≡-irrelevant m∈ m∈′
        | Honest-irr hp hp′
  = refl
Irr-ValidAction {s = s} (RegisterVote {p = p} ⦃ hp ⦄ m∈ eq _) (RegisterVote ⦃ hp′ ⦄ m∈′ eq′ _)
  rewrite Honest-irr hp hp′
  with refl , refl ← index≡ _ ((s ＠ p) .inbox) m∈ eq m∈′ eq′
  rewrite ≡-irrelevant eq eq′
  = refl
Irr-ValidAction (FinalizeBlock ⦃ hp ⦄ _ _) (FinalizeBlock ⦃ hp′ ⦄ _ _)
  rewrite Honest-irr hp hp′
  = refl
Irr-ValidAction (DishonestStep _ _) (DishonestStep _ _)
  = refl
Irr-ValidAction {s = s} (Deliver env∈ eq) (Deliver env∈′ eq′)
  with refl , refl ← index≡ _ (s .networkBuffer) env∈ eq env∈′ eq′
  = cong (Deliver env∈) (≡-irrelevant eq eq′)
Irr-ValidAction {s = s} (Drop env∈ eq) (Drop env∈′ eq′)
  with refl , refl ← index≡ _ (s .networkBuffer) env∈ eq env∈′ eq′
  = cong (Drop env∈) (≡-irrelevant eq eq′)
Irr-ValidAction AdvanceEpoch AdvanceEpoch
  = refl

Irr-ValidTrace : Irrelevant (ValidTrace αs)
Irr-ValidTrace [] [] = refl
Irr-ValidTrace (α ∷ vαs ⊣ vα) (.α ∷ vαs′ ⊣ vα′)
  rewrite Irr-ValidTrace vαs vαs′ | Irr-ValidAction vα vα′
  = refl

instance
  Dec-ValidTrace : ValidTrace ⁇¹
  Dec-ValidTrace {tr} .dec with tr
  ... | []     = yes []
  ... | α ∷ αs
    with ¿ ValidTrace αs ¿
  ... | no ¬vαs = no λ where (_ ∷ vαs ⊣ _) → ¬vαs vαs
  ... | yes vαs
    with ¿ ValidAction α ⟦ vαs ⟧∗ ¿
  ... | no ¬vα = no λ where
    (_ ∷ tr ⊣ vα) → ¬vα
                  $ subst (ValidAction α) (cong ⟦_⟧∗ $ Irr-ValidTrace tr vαs) vα
  ... | yes vα = yes $ _ ∷ vαs ⊣ vα

-- * via labels

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

getLabels : (s ↞— s′) → Actions
getLabels = λ where
  (_ ∎) → []
  (_ ⟨ st ⟩←— tr) → getLabel st ∷ getLabels tr

ValidAction-sound :
  (va : ValidAction α s) →
  s —→ ⟦ va ⟧
ValidAction-sound = λ where
  (Vote m∈ x x₁ x₂ x₃ x₄) → LocalStep $
    VoteBlock m∈ (toRelevant x) (toRelevant x₁) (toRelevant x₂) (toRelevant x₃) (toRelevant x₄)
  (Propose x x₁ x₂ x₃) → LocalStep $
    ProposeBlock (toRelevant x) (toRelevant x₁) (toRelevant x₂) (toRelevant x₃)
  (RegisterVote m∈ _ x) → LocalStep $ RegisterVote m∈ (toRelevant x)
  (FinalizeBlock x x₁) → LocalStep $ FinalizeBlock _ _ (toRelevant x) (toRelevant x₁)
  (DishonestStep x x₁) → DishonestLocalStep (toRelevant x) (toRelevant x₁)
  (Deliver env∈ _) → Deliver env∈
  (Drop env∈ _) → Drop env∈
  AdvanceEpoch → AdvanceEpoch

ValidAction-complete :
  (st : s —→ s′) →
  ValidAction (getLabel st) s
ValidAction-complete = λ where
  (LocalStep (ProposeBlock x x₁ x₂ x₃)) → Propose x x₁ x₂ x₃
  (LocalStep (VoteBlock m∈ x x₁ x₂ x₃ x₄)) → Vote m∈ x x₁ x₂ x₃ x₄
  (LocalStep (RegisterVote m∈ x)) → RegisterVote m∈ refl x
  (LocalStep (FinalizeBlock _ _ x x₁)) → FinalizeBlock x x₁
  (DishonestLocalStep x x₁) → DishonestStep x x₁
  (Deliver env∈) → Deliver env∈ refl
  (Drop env∈) → Drop env∈ refl
  AdvanceEpoch → AdvanceEpoch

ValidAction-⟦⟧ : (st : s —→ s′) → ⟦ ValidAction-complete st ⟧ ≡ s′
ValidAction-⟦⟧ = λ where
  (LocalStep (ProposeBlock _ _ _ _)) → refl
  (LocalStep (VoteBlock _ _ _ _ _ _)) → refl
  (LocalStep (RegisterVote _ _)) → refl
  (LocalStep (FinalizeBlock _ _ _ _)) → refl
  (DishonestLocalStep _ _) → refl
  (Deliver _) → refl
  AdvanceEpoch → refl
  (Drop _) → refl

ValidTrace-sound :
  (tr : ValidTrace αs) →
  ⟦ tr ⟧∗ ↞— initGlobalState
ValidTrace-sound [] = _ ∎
ValidTrace-sound (α ∷ tr ⊣ vα) = _ ⟨ ValidAction-sound vα ⟩←— ValidTrace-sound tr

mutual

  ValidTrace-complete :
    (st : s ↞— initGlobalState) →
    ∃ λ (tr : ValidTrace (getLabels st)) →
      ⟦ tr ⟧∗ ≡ s
  ValidTrace-complete (_ ∎) = [] , refl
  ValidTrace-complete {s = s} (_ ⟨ st ⟩←— tr)
    =
    let
      vtr , ≡s = ValidTrace-complete tr

      α  = getLabel st
      vα = ValidAction-complete st

      open ≡-Reasoning
    in
      (_ ∷ vtr ⊣ subst (ValidAction _) (sym ≡s) (ValidAction-complete st)) ,
      (≡-Reasoning.begin
        ⟦ subst (ValidAction α) (sym ≡s) vα ⟧
      ≡⟨  ⟦⟧-subst vα (sym ≡s) ⟩
        ⟦ vα ⟧
      ≡⟨ ValidAction-⟦⟧ st ⟩
        s
      ≡-Reasoning.∎)
