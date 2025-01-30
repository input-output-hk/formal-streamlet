<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants.TraceInvariants (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Invariants.History ⋯
open import Protocol.Streamlet.Invariants.Votes ⋯
open import Protocol.Streamlet.Invariants.VotedOnlyOnce ⋯
```
-->

```agda
blockVoted : (p ▷ e ⊢ ls —[ mm ]→ ls′) → Maybe (Block × Chain)
blockVoted {e = e} = λ where
  (VoteBlock {H = H} {txs = txs} {ch = ch} _ _ _ _ _ _) → just (⟨ H , e , txs ⟩ , ch)
  (ProposeBlock {ch = ch} {txs = txs} _ _ _ _) → just (⟨ ch ♯ , e , txs ⟩ , ch)
  _ → nothing

≡[_▷_] : Pid → Block × Chain → LocalStepProperty
≡[ p ▷ b , ch ] ((p′ , e′ , _) ⊢ st)
  = (p ≡ p′)
  × (b .epoch ≡ e′)
  × Any ((b , ch) ≡_) (blockVoted st)

HasVoted˘ : TraceProperty
HasVoted˘ tr@(s , _) = ∀ {p b ch} →
  tr ∋⋯ ≡[ p ▷ b , ch ]
  ──────────────────────────
  p ∈ voteIds (s .history) b

hasVoted˘ : TraceInvariant HasVoted˘
hasVoted˘ (_ , refl , (_ ∎)) ()
hasVoted˘ {s′} (_ , init , (_ ⟨ st ∣ s ⟩←— tr))
  {p}{b}{ch} st∈
  with IH ← hasVoted˘ (_ , init , tr)
  with st
... | Deliver _ = IH st∈
... | AdvanceEpoch = IH st∈
... | Drop _ = IH st∈
... | LocalStep {p = p′} ls→
  = QED
  where
  QED : p ∈ voteIds (s′ .history) b
  QED with ⟫ ls→ | ⟫ st∈
  QED | ⟫ FinalizeBlock _ _ _ _ | ⟫ there st∈ = IH st∈
  QED | ⟫ RegisterVote _ _ | ⟫ there st∈ = IH st∈
  QED | ⟫ ProposeBlock {ch = ch↓} {txs = txs} _ refl _ (_ ∷ _ ⊣ B↝)
      | ⟫ here (refl , refl , M.Any.just refl)
      = voteIds-here {m = M} refl refl
      where open ∣ProposeBlock∣ p′ s ch↓ txs
  QED | ⟫ ProposeBlock {ch = ch↓} {txs = txs} _ refl _ _
      | ⟫ there st∈
      = voteIds-there b $ IH st∈
  QED | ⟫ VoteBlock {H = H} {txs = txs} {ch = ch↓} _ _ _ _ _ _
      | ⟫ there st∈
      = ≪QED
    where
    open ∣VoteBlock∣ p′ s H txs

    ≪QED : p ∈ voteIds (M ∷ s .history) b
    ≪QED with b ≟ B
    ... | no  _ = IH st∈
    ... | yes _ = there $ IH st∈
  QED | ⟫ VoteBlock {H = H} {txs = txs} _ _ _ _ _ _
      | ⟫ here (refl , refl , M.Any.just refl)
      = voteIds-here {m = M} refl refl
      where open ∣VoteBlock∣ p′ s H txs
... | DishonestLocalStep _ _
  = voteIds-there b $ IH st∈

HasVoted : TraceProperty
HasVoted tr@(s , _) = ∀ {p b ch} ⦃ _ : Honest p ⦄ →
  ∙ b -connects-to- ch
  ∙ p ∈ voteIds (s .history) b
    ──────────────────────────
    tr ∋⋯ ≡[ p ▷ b , ch ]

hasVoted : TraceInvariant HasVoted
hasVoted (_ , refl , (_ ∎)) _ ()
hasVoted {s′} (_ , init , (_ ⟨ st ∣ s ⟩←— tr))
  {p}{b}{ch} b↝ p∈
  with IH ← hasVoted (_ , init , tr) {p}{b}{ch} b↝
  with st
... | Deliver _ = IH p∈
... | AdvanceEpoch = IH p∈
... | Drop _ = IH p∈
... | LocalStep (FinalizeBlock _ _ _ _)
  = there $ IH p∈
... | LocalStep (RegisterVote _ _)
  = there $ IH p∈
... | LocalStep s→@(ProposeBlock {ch = ch↓} {txs = txs} _ _ _ (_ ∷ _ ⊣ B↝))
  = QED
  where
  open ∣ProposeBlock∣ p s ch↓ txs

  QED : Any ≡[ p ▷ b , ch ] ((_ ⊢ s→) ∷ allLocalSteps tr)
  QED
    with b ≟ B
  ... | no _ = there $ IH p∈
  ... | yes refl
    with ⟫ p∈
  ... | ⟫ there p∈
    = there $ IH p∈
  ... | ⟫ here refl
    = here $′ refl , refl , just bch≡
      where
      bch≡ : (b , ch) ≡ (B , ch↓)
      bch≡ = cong (_ ,_) $ connects-to≡ b↝ B↝
... | LocalStep s→@(VoteBlock {H = H} {txs = txs} {ch = ch↓} _ _ _ _ _ (_ ∷ _ ⊣ B↝))
  = QED
  where
  open ∣VoteBlock∣ p s H txs

  QED : Any ≡[ p ▷ b , ch ] ((_ ⊢ s→) ∷ allLocalSteps tr)
  QED
    with b ≟ B
  ... | no _ = there $ IH p∈
  ... | yes refl
    with ⟫ p∈
  ... | ⟫ there p∈
    = there $ IH p∈
  ... | ⟫ here refl
    = here $′ refl , refl , just bch≡
      where
      bch≡ : (b , ch) ≡ (B , ch↓)
      bch≡ = cong (_ ,_) $ connects-to≡ b↝ B↝
... | DishonestLocalStep {p = p′}{m} ¬hp′ h⇒m∈
  = QED
  where
  open ∣DishonestLocalStep∣ p p′ ¬hp′ s m

  ≪p∈ : p ∈ voteIds (s .history) b
  ≪p∈ with m ∙block ≟ b
  ... | no ≢b = voteIds-∷˘′ ≢b p∈
  ... | yes refl
    with m ∙pid ≟ p
  ... | no  ≢p = voteIds-∷˘ {ms = s .history} ≢p p∈
  ... | yes refl = voteIds-accept∈ (h⇒m∈ it) refl refl

  QED : Any ≡[ p ▷ b , ch ] (allLocalSteps tr)
  QED = IH ≪p∈

HasVotedInbox : TraceProperty
HasVotedInbox tr@(s , _) = ∀ {p m ch} ⦃ _ : Honest p ⦄ ⦃ _ : Honest (m ∙pid) ⦄ →
  let ls = s ＠ p in
  ∙ m ∙block -connects-to- ch
  ∙ m ∈ ls .inbox
    ─────────────────────────────────
    tr ∋⋯ ≡[ m ∙pid ▷ m ∙block , ch ]

hasVotedInbox : TraceInvariant HasVotedInbox
hasVotedInbox {s} Rs {p}{m}{ch} b↝ m∈ = hasVoted Rs b↝ p∈
  where
  m∈′ : m ∈ s .history
  m∈′ = inboxCompleteHonest Rs m∈

  p∈ : m ∙pid ∈ voteIds (s .history) (m ∙block)
  p∈ = L.Mem.∈-map⁺ _∙pid
     $ L.Mem.∈-filter⁺ (((m ∙block ≟_) ∘ _∙block)) m∈′ refl

Notarized∈ : TraceProperty
Notarized∈ tr@(s , _) = ∀ {p b ch} ⦃ _ : Honest p ⦄ →
  tr ∋⋯ ≡[ p ▷ b , ch ]
  ────────────────────────────────
  ch notarized-chain-∈ (s ＠ p) .db

notarized∈ : TraceInvariant Notarized∈
notarized∈ (_ , refl , (_ ∎)) ()
notarized∈ {s′} (_ , init , (_ ⟨ st ∣ s ⟩←— tr))
  {p}{b}{ch} st∈
  with IH ← notarized∈ (_ , init , tr) {p}{b}{ch} ⦃ it ⦄
  with st
... | Deliver {env = [ p′ ∣ m′ ⟩} env∈
  = QED
  where
  open ∣Deliver∣ p s env∈

  QED : ch notarized-chain-∈ (s′ ＠ p) .db
  QED
    with honest? p′
  ... | no _ = IH st∈
  ... | yes hp′
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ ⦃ hp′ ⦄ p≢ = IH st∈
  ... | yes refl rewrite lookup✓ ⦃ it ⦄ = IH st∈
... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH st∈
... | Drop _ = IH st∈
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′

  QED : ch notarized-chain-∈ (s′ ＠ p) .db
  QED with ⟫ ls→ | ⟫ st∈
  QED | ⟫ FinalizeBlock ch↓ _ _ _ | ⟫ there st∈
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ p≢ = IH st∈
  ... | yes refl rewrite lookup✓ = IH st∈
  QED | ⟫ RegisterVote {sb = sb} M∈ M∉ | ⟫ there st∈
    with p ≟ p′
  ... | yes refl rewrite lookup✓ = notarized-chain-∈-∷ $ IH st∈
  ... | no p≢ rewrite lookup✖ p≢ = IH st∈
  QED | ⟫ ProposeBlock {ch = ch↓} {txs = txs} _ refl _ _ | ⟫ there st∈
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ p≢ = IH st∈
  ... | yes refl rewrite lookup✓ = notarized-chain-∈-∷ $ IH st∈
  QED | ⟫ ProposeBlock {ch = ch↓} {txs = txs} _ refl (nch∈ , _) _
      | ⟫ here (refl , refl , just refl)
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ p≢ = nch∈
  ... | yes refl rewrite lookup✓ = notarized-chain-∈-∷ nch∈
  QED | ⟫ VoteBlock {H = H} {txs = txs} {ch = ch↓} M∈ _ _ _ _ _ | ⟫ there st∈
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ p≢ = IH st∈
  ... | yes refl rewrite lookup✓ = notarized-chain-∈-∷ $ notarized-chain-∈-∷ $ IH st∈
  QED | ⟫ VoteBlock {H = H} {txs = txs} {ch = ch↓} M∈ _ _ _ (nch∈ , _) _
      | ⟫ here (refl , refl , just refl)
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ p≢ = nch∈
  ... | yes refl rewrite lookup✓ = notarized-chain-∈-∷ $ notarized-chain-∈-∷ nch∈
... | DishonestLocalStep {p = p′}{mm} ¬hp′ h⇒m∈
  = subst (_ notarized-chain-∈_) db≡ $ IH st∈
  where
  open ∣DishonestLocalStep∣ p p′ ¬hp′ s mm

IncreasingEpochs⋯ : TraceProperty
IncreasingEpochs⋯ tr = ∀ {p b ch b′ ch′} →
  ∙ length ch < length ch′
  ∙ tr ∋⋯ ≡[ p ▷ b  , ch  ]
  ∙ tr ∋⋯ ≡[ p ▷ b′ , ch′ ]
    ────────────────────────────
    b .epoch ≤ b′ .epoch

private pattern HERE = here (refl , refl , just refl)

increasingEpochs⋯ : TraceInvariant IncreasingEpochs⋯
increasingEpochs⋯ (_ , refl , (_ ∎)) _ ()
increasingEpochs⋯ {s′} (_ , init , (_ ⟨ st ∣ s ⟩←— tr))
  {p}{b}{ch}{b′}{ch′} len< st∈ st∈′
  with IH ← increasingEpochs⋯ (_ , init , tr) {p}{b}{ch}{b′}{ch′} len<
  with IH-noFutVot ← noFutureVotes≤ (_ , init , tr) {p}
  with IH-hasVot ← hasVoted˘ (_ , init , tr) {p}
  with IH-not∈ ← notarized∈ (_ , init , tr)
  with st
... | Deliver _ = IH st∈ st∈′
... | AdvanceEpoch = IH st∈ st∈′
... | Drop _ = IH st∈ st∈′
... | LocalStep ls→
  = QED
  where
  QED : b .epoch ≤ b′ .epoch
  QED with ⟫ ls→ | ⟫ st∈ | ⟫ st∈′
  QED | ⟫ FinalizeBlock _ _ _ _ | ⟫ there st∈ | ⟫ there st∈′ = IH st∈ st∈′
  QED | ⟫ RegisterVote _ _ | ⟫ there st∈ | ⟫ there st∈′ = IH st∈ st∈′
  QED | ⟫ ProposeBlock _ _ _ _ | ⟫ there st∈ | ⟫ there st∈′ = IH st∈ st∈′
  QED | ⟫ ProposeBlock _ _ _ _ | ⟫ HERE | ⟫ HERE
    = ⊥-elim $ Nat.<-irrefl refl len<
  QED | ⟫ ProposeBlock {ch = ch↓} {txs = txs} _ _ (_ , mkLongest∈ lch) _
      | ⟫ HERE | ⟫ there st∈′
    = ⊥-elim $ Nat.<⇒≱ len< len≥
    where
    open ∣ProposeBlock∣ p s ch↓ txs

    ch∈′ : ch′ notarized-chain-∈ ((s ＠ p) .db)
    ch∈′ = IH-not∈ st∈′

    len≥ : length ch↓ ≥ length ch′
    len≥ = lch ch∈′
  QED | ⟫ ProposeBlock {ch = ch↓} {txs = txs} _ refl _ _ | ⟫ there st∈ | ⟫ HERE
    = IH-noFutVot p∈
    where
    open ∣ProposeBlock∣ p s ch↓ txs

    p∈ : L ∈ voteIds (s .history) b
    p∈ = IH-hasVot st∈
  QED | ⟫ VoteBlock {H = H} _ _ _ _ _ _ | ⟫ there st∈ | ⟫ there st∈′ = IH st∈ st∈′
  QED | ⟫ VoteBlock _ _ _ _ _ _ | ⟫ HERE | ⟫ HERE
    = ⊥-elim $ Nat.<-irrefl refl len<
  QED | ⟫ VoteBlock {H = H} {txs = txs} {ch = ch↓} _ _ _ _ (_ , mkLongest∈ lch) _ | ⟫ HERE | ⟫ there st∈′
    = ⊥-elim $ Nat.<⇒≱ len< len≥
    where
    open ∣VoteBlock∣ p s H txs

    ch∈′ : ch′ notarized-chain-∈ ((s ＠ p) .db)
    ch∈′ = IH-not∈ st∈′

    len≥ : length ch↓ ≥ length ch′
    len≥ = lch ch∈′
  QED | ⟫ VoteBlock {H = H} {txs = txs} _ _ _ _ _ _ | ⟫ there st∈ | ⟫ HERE
    = IH-noFutVot p∈
    where
    open ∣VoteBlock∣ p s H txs

    p∈ : p ∈ voteIds (s .history) b
    p∈ = IH-hasVot st∈
... | DishonestLocalStep _ _ = IH st∈ st∈′
```
