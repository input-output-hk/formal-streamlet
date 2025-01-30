<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants.IncreasingEpochs (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
  hiding (vch; vch′)
open import Protocol.Streamlet.Invariants.Unforgeability ⋯
open import Protocol.Streamlet.Invariants.VotedOnlyOnce ⋯
open import Protocol.Streamlet.Invariants.Votes ⋯
open import Protocol.Streamlet.Invariants.TraceInvariants ⋯
```
-->

```agda
IncreasingEpochs′ : StateProperty
IncreasingEpochs′ s = ∀ {p p′ b ch b′ ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let ms = (s ＠ p) .db in
  ∙ p′ ∈ voteIds ms b
  ∙ ch notarized-chain-∈ ms
  ∙ b -connects-to- ch

  ∙ p′ ∈ voteIds ms b′
  ∙ ch′ notarized-chain-∈ ms
  ∙ b′ -connects-to- ch′

  ∙ length ch < length ch′
    ────────────────────────
    b .epoch < b′ .epoch

increasingEpochs′ : Invariant IncreasingEpochs′
increasingEpochs′ (_ , refl , (_ ∎)) {p} p∈
  rewrite let open ∣Base∣ p in lookup✓
  = case p∈ of λ ()
increasingEpochs′ {s′} Rs₀@(_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p}{p′}{b}{ch}{b′}{ch′} ⦃ hp ⦄ p∈ ch∈ b↝ p∈′ ch∈′ b↝′ len<
  with Rs ← -, refl , tr
  with IH ← (λ p∈ ch∈ p∈′ ch∈′ →
    increasingEpochs′ Rs {p}{p′}{b}{ch}{b′}{ch′} p∈ ch∈ b↝ p∈′ ch∈′ b↝′ len<)
  with s→
... | Deliver {env = [ p″ ∣ M ⟩} env∈
  = QED
  where
  open ∣Deliver∣ p s env∈

  QED : b .epoch < b′ .epoch
  QED
    with honest? p″
  ... | no _ = IH p∈ ch∈ p∈′ ch∈′
  ... | yes hp′
    with p ≟ p″
  ... | no p≢ rewrite lookup✖ ⦃ hp′ ⦄ p≢ = IH p∈ ch∈ p∈′ ch∈′
  ... | yes refl rewrite lookup✓ ⦃ it ⦄ = IH p∈ ch∈ p∈′ ch∈′
... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH p∈ ch∈ p∈′ ch∈′
... | Drop _
  = IH p∈ ch∈ p∈′ ch∈′
... | LocalStep {p = p″}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p″ s mm ls′

  QED : b .epoch < b′ .epoch
  QED with ⟫ ls→
  QED | ⟫ ProposeBlock {ch = ch↓} {txs = txs} ph≡ refl (_ , mkLongest∈ lch) (_ ∷ _ ⊣ B↝)
    = ≪QED
    where
    open ∣ProposeBlock∣ p″ s ch↓ txs

    E≡ : b .epoch ≡ b′ .epoch → b ≡ b′
    E≡ = votedOnlyOncePerEpoch Rs₀ p∈ p∈′

    b≢b′ : b ≢ b′
    b≢b′ refl = Nat.<-irrefl refl len<≡
      where
      ch≡ : ch ≡ ch′
      ch≡ = connects-to≡ b↝ b↝′

      len<≡ : length ch < length ch
      len<≡ = subst (length ch <_) (sym $ cong length ch≡) len<

    E≢ : b .epoch ≢ b′ .epoch
    E≢ = b≢b′ ∘ E≡

    vch  = notarized-chain-∈⇒Valid ch∈
    vch′ = notarized-chain-∈⇒Valid ch∈′

    E< : B ∈ ch → E < b .epoch
    E< B∈ = connects-to-epoch< vch B∈ b↝

    E<′ : B ∈ ch′ → E < b′ .epoch
    E<′ B∈ = connects-to-epoch< vch′ B∈ b↝′

    ≪QED : b .epoch < b′ .epoch
    ≪QED
      with b ∈? ch′
    ... | yes b∈ch′
      = connects-to-epoch< (notarized-chain-∈⇒Valid ch∈′) b∈ch′ b↝′
    ... | no b∉ch′
      with p ≟ L
    -- * p ≠ L
    ... | no  p≢ rewrite lookup✖ p≢
      = IH p∈ ch∈ p∈′ ch∈′
    -- * p = L
    ... | yes refl rewrite lookup✓
      -- p∈′ : p′ ∈ voteIds (M ∷ ≪db) b′
      with b ≟ B | b′ ≟ B
    -- * b = b′ = B
    ... | yes refl | yes refl
      = ⊥-elim $ b≢b′ refl
    -- * b ≠ b′ ≠ B
    ... | no b≢ | no b′≢
      = IH p∈ ≪ch∈ p∈′ ≪ch∈′
      where
      ≪ch∈ : ch notarized-chain-∈ ≪db
      ≪ch∈ = notarized-chain-∉ B∉ ch∈
        where
        ≤E : b .epoch ≤ E
        ≤E = noFutureVotes≤ Rs (voteIdsComplete Rs ⦃ hp ⦄ p∈)

        B∉ : B ∉ ch
        B∉ B∈ = Nat.<⇒≱ (E< B∈) ≤E

      ≪ch∈′ : ch′ notarized-chain-∈ ≪db
      ≪ch∈′ = notarized-chain-∉ B∉ ch∈′
        where
        ≤E : b′ .epoch ≤ E
        ≤E = noFutureVotes≤ Rs (voteIdsComplete Rs ⦃ hp ⦄ p∈′)

        B∉ : B ∉ ch′
        B∉ B∈ = Nat.<⇒≱ (E<′ B∈) ≤E
    -- * b = B, b′ ≠ B
    ... | yes refl | no b′≢
      = ⊥-elim $ Nat.<⇒≱ len< len≥
      where
      ≪ch∈′ : ch′ notarized-chain-∈ ≪db
      ≪ch∈′ = notarized-chain-∉ b∉ch′ ch∈′

      ch↓≡ : ch↓ ≡ ch
      ch↓≡ = connects-to≡ B↝ b↝

      len≥ : length ch ≥ length ch′
      len≥ = subst (_≥ _) (cong length ch↓≡) (lch ≪ch∈′)
    -- * b ≠ B, b′ = B
    ... | no b≢ | yes refl
      = Nat.≤∧≢⇒< QED≤ E≢
      where
      ≪p∈ : p′ ∈ voteIds (s .history) b
      ≪p∈ = voteIdsComplete Rs ⦃ hp ⦄ p∈

      QED≤ : b .epoch ≤ E
      QED≤ = noFutureVotes≤ Rs ≪p∈
  QED | ⟫ VoteBlock {H = H} {txs = txs} {ch = ch↓} M∈ _ ph≡ p″≢L (_ , mkLongest∈ lch) (_ ∷ _ ⊣ B↝)
    = ≪QED
    where
    open ∣VoteBlock∣ p″ s H txs

    E≡ : b .epoch ≡ b′ .epoch → b ≡ b′
    E≡ = votedOnlyOncePerEpoch Rs₀ p∈ p∈′

    b≢b′ : b ≢ b′
    b≢b′ refl = Nat.<-irrefl refl len<≡
      where
      ch≡ : ch ≡ ch′
      ch≡ = connects-to≡ b↝ b↝′

      len<≡ : length ch < length ch
      len<≡ = subst (length ch <_) (sym $ cong length ch≡) len<

    E≢ : b .epoch ≢ b′ .epoch
    E≢ = b≢b′ ∘ E≡

    vch  = notarized-chain-∈⇒Valid ch∈
    vch′ = notarized-chain-∈⇒Valid ch∈′

    E< : B ∈ ch → E < b .epoch
    E< B∈ = connects-to-epoch< vch B∈ b↝

    E<′ : B ∈ ch′ → E < b′ .epoch
    E<′ B∈ = connects-to-epoch< vch′ B∈ b↝′

    ≪QED : b .epoch < b′ .epoch
    ≪QED
      with b ∈? ch′
    ... | yes b∈ch′
      = connects-to-epoch< vch′ b∈ch′ b↝′
    ... | no b∉ch′

      with p ≟ p″
    -- * p ≠ p″
    ... | no  p≢ rewrite lookup✖ p≢
      = IH p∈ ch∈ p∈′ ch∈′
    -- * p = p″
    ... | yes refl rewrite lookup✓

      with b ≟ B | b′ ≟ B
    -- * b = b′ = B
    ... | yes refl | yes refl
      = ⊥-elim $ b≢b′ refl

    -- * b ≠ b′ ≠ B
    ... | no b≢ | no b′≢
      with p∈  ← voteIds-∷˘′ (Eq.≢-sym b≢)  p∈
      with p∈′ ← voteIds-∷˘′ (Eq.≢-sym b′≢) p∈′
      = IH p∈ ≪ch∈ p∈′ ≪ch∈′
      where
      ≪ch∈ : ch notarized-chain-∈ ≪db
      ≪ch∈ = notarized-chain-∉ B∉ $ notarized-chain-∉ B∉ ch∈
        where
        ≤E : b .epoch ≤ E
        ≤E = noFutureVotes≤ Rs (voteIdsComplete Rs ⦃ hp ⦄ p∈)

        B∉ : B ∉ ch
        B∉ B∈ = Nat.<⇒≱ (E< B∈) ≤E

      ≪ch∈′ : ch′ notarized-chain-∈ ≪db
      ≪ch∈′ = notarized-chain-∉ B∉ $ notarized-chain-∉ B∉ ch∈′
        where
        ≤E : b′ .epoch ≤ E
        ≤E = noFutureVotes≤ Rs (voteIdsComplete Rs ⦃ hp ⦄ p∈′)

        B∉ : B ∉ ch′
        B∉ B∈ = Nat.<⇒≱ (E<′ B∈) ≤E

    -- * b = B, b′ ≠ B
    ... | yes refl | no b′≢
      = ⊥-elim $ Nat.<⇒≱ len< len≥
      where
      ≪ch∈′ : ch′ notarized-chain-∈ ≪db
      ≪ch∈′ = notarized-chain-∉ b∉ch′ $ notarized-chain-∉ b∉ch′ ch∈′

      ch↓≡ : ch↓ ≡ ch
      ch↓≡ = connects-to≡ B↝ b↝

      len≥ : length ch ≥ length ch′
      len≥ = subst (_≥ _) (cong length ch↓≡) (lch ≪ch∈′)

    -- * b ≠ B, b′ = B
    ... | no b≢ | yes refl
      with p∈ ← voteIds-∷˘′ (Eq.≢-sym b≢) p∈
      = Nat.≤∧≢⇒< QED≤ E≢
      where
      ≪p∈ : p′ ∈ voteIds (s .history) b
      ≪p∈ = voteIdsComplete Rs ⦃ hp ⦄ p∈

      QED≤ : b .epoch ≤ E
      QED≤ = noFutureVotes≤ Rs ≪p∈
  QED | ⟫ RegisterVote {sb = sb} M∈ M∉
    = ≪QED
    where
    open ∣RegisterVote∣ p″ s sb

    pᴮ≢ : Pᴮ ≢ p″
    pᴮ≢ Mp≡ = M∉ $ L.Mem.∈-map⁺ _∙signedBlock (unforgeability Rs M∈ (sym Mp≡))

    b≢b′ : b ≢ b′
    b≢b′ refl = Nat.<-irrefl refl len<≡
      where
      ch≡ : ch ≡ ch′
      ch≡ = connects-to≡ b↝ b↝′

      len<≡ : length ch < length ch
      len<≡ = subst (length ch <_) (sym $ cong length ch≡) len<

    E≢ : b .epoch ≢ b′ .epoch
    E≢ = b≢b′ ∘ E≡
      where
      E≡ : b .epoch ≡ b′ .epoch → b ≡ b′
      E≡ = votedOnlyOncePerEpoch Rs₀ p∈ p∈′

    vch  = notarized-chain-∈⇒Valid ch∈
    vch′ = notarized-chain-∈⇒Valid ch∈′

    ≪QED : b .epoch < b′ .epoch
    ≪QED
      with p ≟ p″
    -- * p ≠ p″
    ... | no p≢ rewrite lookup✖ p≢
      = IH p∈ ch∈ p∈′ ch∈′
    -- * p = p″
    ... | yes refl rewrite lookup✓

        with b ∈? ch′
    ... | yes b∈ch′
      = connects-to-epoch< vch′ b∈ch′ b↝′
    ... | no b∉ch′

      with b ≟ B | b′ ≟ B
    -- * b = b′ = B
    ... | yes refl | yes refl
      = ⊥-elim $ b≢b′ refl

    -- * b ≠ b′, b ≠ B
    ... | no b≢ | no b′≢
      = Nat.≤∧≢⇒< QED≤ E≢
      where
      QED≤ : b .epoch ≤ b′ .epoch
      QED≤ = increasingEpochs⋯ Rs len< H₁ H₂
        where
        H₁ = hasVoted Rs b↝  (voteIdsComplete Rs ⦃ hp ⦄ p∈)
        H₂ = hasVoted Rs b↝′ (voteIdsComplete Rs ⦃ hp ⦄ p∈′)

    -- * b = B, b′ ≠ B
    ... | yes refl | no b′≢
      = ≪≪QED
      where
      ≪≪QED : Eᴮ < b′ .epoch
      ≪≪QED
        with B ∈? ch′
      ... | yes B∈
        = connects-to-epoch< vch′ B∈ b↝′
      ... | no B∉

        with ⟫ p∈
      ... | ⟫ there p∈
        -- * p∈′ : pᴮ ∈ voteIds ≪db
        = IH p∈ ≪ch∈ p∈′ ≪ch∈′
        where
        ≪ch∈ : ch notarized-chain-∈ ≪db
        ≪ch∈ = notarized-chain-∉ (connects-to∉ vch b↝) ch∈

        ≪ch∈′ : ch′ notarized-chain-∈ ≪db
        ≪ch∈′ = notarized-chain-∉ B∉ ch∈′
      ... | ⟫ here refl
        -- * p′ = pᴮ
        = Nat.≤∧≢⇒< QED≤ E≢
        where
        ≪p∈ : Pᴮ ∈ voteIds (s .history) b′
        ≪p∈ = voteIdsComplete Rs ⦃ hp ⦄ p∈′

        QED≤ : Eᴮ ≤ b′ .epoch
        QED≤ = increasingEpochs⋯ Rs len< H₁ H₂
          where
          H₁ = hasVotedInbox Rs ⦃ hp ⦄ b↝ M∈
          H₂ = hasVoted Rs b↝′ ≪p∈

    -- * b ≠ B, b′ = B
    ... | no b≢ | yes refl

      with ⟫ p∈′
    ... | ⟫ there p∈′
      -- * p∈′ : pᴮ ∈ voteIds ≪db
      = IH p∈ ≪ch∈ p∈′ ≪ch∈′
      where
      -- ch∈ : ch notarized-chain-∈ (M ∷ ≪db)
      ≪ch∈ : ch notarized-chain-∈ ≪db
      ≪ch∈ = notarized-chain-∉ B∉ ch∈
        where
        B∉ : B ∉ ch
        B∉ B∈ = Nat.<⇒≱ len< len≥
          where
          len≥ : length ch′ ≤ length ch
          len≥ = connect-to∈ vch vch′ B∈ b↝′

      ≪ch∈′ : ch′ notarized-chain-∈ ≪db
      ≪ch∈′ = notarized-chain-∉ (connects-to∉ vch′ b↝′) ch∈′

    ... | ⟫ here refl
      -- * p′ = pᴮ
      = Nat.≤∧≢⇒< QED≤ E≢
      where
      ≪p∈ : Pᴮ ∈ voteIds (s .history) b
      ≪p∈ = voteIdsComplete Rs ⦃ hp ⦄ p∈

      QED≤ : b .epoch ≤ Eᴮ
      QED≤ = increasingEpochs⋯ Rs len< H₁ H₂
        where
        H₁ = hasVoted Rs b↝ ≪p∈
        H₂ = hasVotedInbox Rs ⦃ hp ⦄ b↝′ M∈
  QED | ⟫ FinalizeBlock ch _ _ _
   with p ≟ p″
  ... | yes refl rewrite lookup✓ = IH p∈ ch∈ p∈′ ch∈′
  ... | no p≢ rewrite lookup✖ p≢ = IH p∈ ch∈ p∈′ ch∈′
... | DishonestLocalStep {p = p′}{mm} ¬hp′ h⇒m∈
  = IH ≪p∈ ≪ch∈ ≪p∈′ ≪ch∈′
  where
  open ∣DishonestLocalStep∣ p p′ ¬hp′ s mm

  ≪p∈   = subst (λ ◆ → _ ∈ voteIds ◆ _) (sym db≡) p∈
  ≪p∈′  = subst (λ ◆ → _ ∈ voteIds ◆ _) (sym db≡) p∈′
  ≪ch∈  = subst (_ notarized-chain-∈_)  (sym db≡) ch∈
  ≪ch∈′ = subst (_ notarized-chain-∈_)  (sym db≡) ch∈′
```

## Global version of increasing epochs

```agda
IncreasingEpochs : StateProperty
IncreasingEpochs s = ∀ {p p′ p″ b ch b′ ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ ⦃ _ : Honest p″ ⦄ →
  let ms  = (s ＠ p) .db
      ms′ = (s ＠ p′) .db
  in
  ∙ p″ ∈ voteIds ms b
  ∙ b -connects-to- ch

  ∙ p″ ∈ voteIds ms′ b′
  ∙ b′ -connects-to- ch′

  ∙ length ch < length ch′
    ────────────────────────
    b .epoch < b′ .epoch

increasingEpochs : Invariant IncreasingEpochs
increasingEpochs {s} Rs {p}{p′}{p″}{b}{ch}{b′}{ch′} p∈ b↝ p∈′ b↝′ len< =
  let
    _p∈ : p″ ∈ voteIds ((s ＠ p″) .db) b
    _p∈  = messageSharing Rs p∈

    _p∈′ : p″ ∈ voteIds ((s ＠ p″) .db) b′
    _p∈′ = messageSharing Rs p∈′

    ch∈ : ch notarized-chain-∈ ((s ＠ p″) .db)
    ch∈ = notarized∈ Rs $ hasVoted Rs b↝ $ voteIdsComplete Rs _p∈

    ch∈′ : ch′ notarized-chain-∈ ((s ＠ p″) .db)
    ch∈′ = notarized∈ Rs $ hasVoted Rs b↝′ $ voteIdsComplete Rs _p∈′

  in increasingEpochs′ Rs {p″}{p″} _p∈ ch∈ b↝ _p∈′ ch∈′ b↝′ len<
```
