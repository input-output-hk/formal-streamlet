# Invariants related to the global history.

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants.History (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
  hiding (ls′)
```
-->

```agda
-- ** all messages in history are actually sent
HistorySound : StateProperty
HistorySound s = ∀ {p m} ⦃ _ : Honest p ⦄ →
  ∙ m ∈ s .history
  ∙ p ≡ m ∙pid
    ───────────────
    m ∈ (s ＠ p) .db

historySound : Invariant HistorySound
historySound = Step⇒Invariant (λ where refl ()) historySound→
  where
  historySound→ : StepPreserved HistorySound
  historySound→ {s}{s′} s→
    IH₀ {p}{m} ⦃ hp ⦄ m∈ p≡
    with IH ← (λ (m∈ : m ∈ s .history) → IH₀ m∈ p≡)
    with s→
  ... | Deliver {env = [ p′ ∣ m′ ⟩} env∈
    rewrite let open ∣Deliver∣ p s env∈ in db≡
    = IH m∈
  ... | AdvanceEpoch
    rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
    = IH m∈
  ... | Drop _
    = IH m∈
  ... | LocalStep {p = p′}{mm}{ls′} ls→
    = QED
    where
    open ∣LocalStep∣ p p′ s mm ls′

    QED : m ∈ (s′ ＠ p) .db
    QED
      with ⟫ ls→
    QED | ⟫ ProposeBlock {ch = ch} {txs = txs} _ refl _ _
      with ⟫ m∈
    ... | ⟫ here refl rewrite p≡ | lookup✓ = here refl
    ... | ⟫ there m∈
      with ih ← IH m∈
      with p ≟ p′
    ... | yes refl rewrite lookup✓ = there ih
    ... | no  p≢   rewrite lookup✖ p≢ = ih
    QED | ⟫ VoteBlock {txs = txs} M∈ _ _ _ _ _
      with ⟫ m∈
    ... | ⟫ here refl rewrite p≡ | lookup✓ = here refl
    ... | ⟫ there m∈
      with ih ← IH m∈
      with p ≟ p′
    ... | yes refl rewrite lookup✓ = there $′ there ih
    ... | no  p≢   rewrite lookup✖ p≢ = ih
    QED | ⟫ RegisterVote {sb = sb} M∈ M∉
      with ih ← IH m∈
      with p ≟ p′
    ... | yes refl rewrite lookup✓ = there ih
    ... | no  p≢   rewrite lookup✖ p≢ = ih
    QED | ⟫ FinalizeBlock ch _ _ _
      with ih ← IH m∈
      with p ≟ p′
    ... | yes refl rewrite lookup✓ = ih
    ... | no p≢ rewrite lookup✖ p≢ = ih
  ... | DishonestLocalStep ¬hp′ h⇒m∈
    = QED
    where
    ≪m∈ : m ∈ s .history
    ≪m∈ with ⟫ m∈
    ... | ⟫ here refl = h⇒m∈ $ subst Honest p≡ it
    ... | ⟫ there m∈  = m∈

    QED : m ∈ (s′ ＠ p) .db
    QED = IH ≪m∈

-- ** all messages sent on the network are recorded in history
NetworkComplete : StateProperty
NetworkComplete s = ∀ {p m} →
  [ p ∣ m ⟩ ∈ s .networkBuffer
  ────────────────────────────
  m ∈ s .history

networkComplete : Invariant NetworkComplete
networkComplete = Step⇒Invariant (λ where refl ()) networkComplete→
  where
  networkComplete-broadcast : ∀ s p mm →
    NetworkComplete s
    ──────────────────────────────────
    NetworkComplete (broadcast p mm s)
  networkComplete-broadcast s _ nothing  IH = IH
  networkComplete-broadcast s p (just m) IH m∈
    with L.Mem.∈-++⁻ (s .networkBuffer) m∈
  ... | inj₁ m∈ = there $ IH m∈
  ... | inj₂ m∈
    with _ , m∈ , refl ← L.Mem.∈-map⁻ [_∣ m ⟩ m∈
    with m∈ , _ ← L.Mem.∈-filter⁻ (p ≢?_) {xs = allPids} m∈
    = here refl

  networkComplete→ : StepPreserved NetworkComplete
  networkComplete→ {s} = let H = networkComplete-broadcast s in λ where
    (LocalStep (ProposeBlock _ _ _ _))          → H _ (just _)
    (LocalStep (VoteBlock _ _ _ _ _ _))         → H _ (just _)
    (LocalStep {p = p} (RegisterVote _ _))      → H p nothing
    (LocalStep {p = p} (FinalizeBlock _ _ _ _)) → H p nothing
    (DishonestLocalStep {m = m} _ _)            → networkComplete-broadcast s _ (just m)
    (Deliver _)  → _∘ ∈-removeAt⁻ _
    AdvanceEpoch → id
    (Drop _)     → _∘ ∈-removeAt⁻ _

-- ** honest participants′ inboxes are completely recorded in history
InboxCompleteHonest : StateProperty
InboxCompleteHonest s = ∀ {p} ⦃ _ : Honest p ⦄ →
  ────────────────────────────
  (s ＠ p) .inbox ⊆ˢ s .history

inboxCompleteHonest : Invariant InboxCompleteHonest
inboxCompleteHonest (_ , refl , (_ ∎)) {p} m∈
  rewrite let open ∣Base∣ p in lookup✓
  = case m∈ of λ ()
inboxCompleteHonest {s′} (_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p} {m} m∈
  with Rs ← -, refl , tr
  with IH ← inboxCompleteHonest Rs ⦃ it ⦄
  with s→
... | Deliver {env = [ p′ ∣ m′ ⟩} env∈
  = QED
  where
  open ∣Deliver∣ p s env∈

  QED : m ∈ s′ .history
  QED
    with honest? p′
  ... | no _ = IH m∈
  ... | yes hp′
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ ⦃ hp′ ⦄ p≢ = IH m∈
  ... | yes refl rewrite lookup✓ ⦃ it ⦄
    with ∈-∷ʳ⁻ m∈
  ... | inj₁ m∈   = IH m∈
  ... | inj₂ refl = networkComplete Rs env∈
... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH m∈
... | Drop _
  = IH m∈
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′

  QED : m ∈ s′ .history
  QED
    with ⟫ ls→
  QED | ⟫ ProposeBlock {ch = ch} {txs = txs} _ refl _ _
    with p ≟ p′
  ... | yes refl rewrite lookup✓    = there $ IH m∈
  ... | no  p≢   rewrite lookup✖ p≢ = there $ IH m∈
  QED | ⟫ VoteBlock {txs = txs} M∈ _ _ _ _ _
    with p ≟ p′
  ... | yes refl rewrite lookup✓    = there $′ IH (∈-removeAt⁻ _ m∈)
  ... | no  p≢   rewrite lookup✖ p≢ = there $′ IH m∈
  QED | ⟫ RegisterVote {sb = sb} M∈ M∉
    with p ≟ p′
  ... | yes refl rewrite lookup✓    = IH (∈-removeAt⁻ _ m∈)
  ... | no  p≢   rewrite lookup✖ p≢ = IH m∈
  QED | ⟫ FinalizeBlock ch _ _ _
    with p ≟ p′
  ... | yes refl rewrite lookup✓ = IH m∈
  ... | no p≢ rewrite lookup✖ p≢ = IH m∈
... | DishonestLocalStep _ _
  = there $ IH m∈

-- ** honest participants′ message databases are completely recorded in history
HistoryComplete : StateProperty
HistoryComplete s = ∀ {p} ⦃ _ : Honest p ⦄ →
  ─────────────────────────
  (s ＠ p) .db ⊆ˢ s .history

historyComplete : Invariant HistoryComplete
historyComplete (_ , refl , (_ ∎)) {p} m∈
  rewrite let open ∣Base∣ p in lookup✓
  = case m∈ of λ ()
historyComplete {s′} (_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p} ⦃ hp ⦄ {m} m∈
  with Rs ← -, refl , tr
  with IH ← historyComplete Rs ⦃ it ⦄
  with s→
... | Deliver {env = [ p′ ∣ m′ ⟩} env∈
  = IH $ subst (_ ∈_) db≡ m∈
  where
  open ∣Deliver∣ p s env∈

... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH m∈
... | Drop _
  = IH m∈
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′

  QED : m ∈ s′ .history
  QED with ⟫ ls→
  QED | ⟫ ProposeBlock {ch = ch} {txs = txs} _ refl _ _
    with p ≟ p′
  ... | no  p≢   rewrite lookup✖ p≢ = there $ IH m∈
  ... | yes refl rewrite lookup✓
    with ⟫ m∈
  ... | ⟫ here refl = here refl
  ... | ⟫ there m∈ = there $ IH m∈
  QED | ⟫ VoteBlock {txs = txs} M∈ _ _ _ _ _
    with p ≟ p′
  ... | no  p≢   rewrite lookup✖ p≢ = there $ IH m∈
  ... | yes refl rewrite lookup✓
    with ⟫ m∈
  ... | ⟫ here refl = here refl
  ... | ⟫ there (here refl) = there P∈
    where
    P∈ : _ ∈ s .history
    P∈ = inboxCompleteHonest Rs ⦃ hp ⦄ $ AnyFirst⇒Any M∈
  ... | ⟫ there (there m∈) = there $ IH m∈
  QED | ⟫ RegisterVote {sb = sb} M∈ M∉
    with p ≟ p′
  ... | no  p≢   rewrite lookup✖ p≢ = IH m∈
  ... | yes refl rewrite lookup✓
    with ⟫ m∈
  ... | ⟫ here refl = inboxCompleteHonest Rs ⦃ hp ⦄ M∈
  ... | ⟫ there m∈  = IH m∈
  QED | ⟫ FinalizeBlock ch _ _ _
    with p ≟ p′
  ... | yes refl rewrite lookup✓ = IH m∈
  ... | no p≢ rewrite lookup✖ p≢ = IH m∈
... | DishonestLocalStep _ _
  = there $ IH m∈
