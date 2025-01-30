# Invariants related to the global history.

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants.Votes (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Invariants.History ⋯
```
-->

```agda
VotesComplete : StateProperty
VotesComplete s = ∀ {p b} ⦃ _ : Honest p ⦄ →
  ─────────────────────────────────────────────
  votes ((s ＠ p) .db) b ⊆ˢ votes (s .history) b

votesComplete : Invariant VotesComplete
votesComplete {s} Rs {p}{b} m∈? =
  let m∈ , b≡ = L.Mem.∈-filter⁻ ((b ≟_) ∘ _∙block) m∈?
  in L.Mem.∈-filter⁺ ((b ≟_) ∘ _∙block) (historyComplete Rs m∈) b≡

VoteIdsComplete : StateProperty
VoteIdsComplete s = ∀ {p b} ⦃ _ : Honest p ⦄ →
  ─────────────────────────────────────────────────
  voteIds ((s ＠ p) .db) b ⊆ˢ voteIds (s .history) b

voteIdsComplete : Invariant VoteIdsComplete
voteIdsComplete Rs p∈
  with _ , m∈ , refl ← L.Mem.∈-map⁻ _∙pid p∈
  = L.Mem.∈-map⁺ _∙pid $ votesComplete Rs m∈

MessageSharing : StateProperty
MessageSharing s = ∀ {p p′ b} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  p′ ∈ voteIds ((s ＠ p)  .db) b
  ─────────────────────────────
  p′ ∈ voteIds ((s ＠ p′) .db) b

messageSharing : Invariant MessageSharing
messageSharing {s} Rs {p}{p′}{b} p∈ =
  let
    m , m∈? , p≡ = L.Mem.∈-map⁻ _∙pid p∈
    m∈ , m≡  = L.Mem.∈-filter⁻ ((b ≟_) ∘ _∙block) {xs = (s ＠ p) .db} m∈?

    m∈′ : m ∈ (s ＠ p′) .db
    m∈′ = historySound Rs (historyComplete Rs m∈) p≡

    QED : p′ ∈ voteIds ((s ＠ p′) .db) b
    QED = subst (_∈ _) (sym p≡)
        $ L.Mem.∈-map⁺ _∙pid
        $ L.Mem.∈-filter⁺ ((b ≟_) ∘ _∙block) {xs = (s ＠ p′) .db} m∈′ m≡
  in
    QED

Chain∈-Complete : StateProperty
Chain∈-Complete s = ∀ {p ch} ⦃ _ : Honest p ⦄ →
  ch chain-∈ (s ＠ p) .db
  ──────────────────────
  ch chain-∈ s .history

chain∈-complete : Invariant Chain∈-Complete
chain∈-complete Rs = ⊆-ch∈ (historyComplete Rs)

NoFutureVotes≤ : StateProperty
NoFutureVotes≤ s = ∀ {p b} ⦃ _ : Honest p ⦄ →
  p ∈ voteIds (s .history) b
  ──────────────────────────
  b .epoch ≤ s .e-now

noFutureVotes≤ : Invariant NoFutureVotes≤
noFutureVotes≤ (_ , refl , (_ ∎)) ()
noFutureVotes≤ {s′} (_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p}{b} p∈
  with Rs ← -, refl , tr
  with IH ← noFutureVotes≤ Rs {b = b} ⦃ it ⦄
  with s→
... | Deliver _ = IH p∈
... | AdvanceEpoch = Nat.m≤n⇒m≤1+n $ IH p∈
... | Drop _ = IH p∈
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′

  QED : b .epoch ≤ s′ .e-now
  QED with ⟫ ls→
  QED | ⟫ ProposeBlock {ch = ch} {txs = txs} _ refl _ _
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ p≢
    = IH p∈′
    where
    p∈′ : p ∈ voteIds (s .history) b
    p∈′ = voteIds-∷˘ {ms = s .history} (Eq.≢-sym p≢) p∈
  ... | yes refl rewrite lookup✓
    with b ≟ ⟨ ch ♯ , s .e-now , txs ⟩
  ... | yes refl = Nat.≤-refl
  ... | no  _    = IH p∈
  QED | ⟫ VoteBlock {H = H} {txs = txs} M∈ _ _ _ _ _
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ p≢
    = IH p∈′
    where
    p∈′ : p ∈ voteIds (s .history) b
    p∈′ = voteIds-∷˘ {ms = s .history} (Eq.≢-sym p≢) p∈
  ... | yes refl rewrite lookup✓
    with b ≟ ⟨ H , s .e-now , txs ⟩
  ... | yes refl = Nat.≤-refl
  ... | no  _    = IH p∈
  QED | ⟫ RegisterVote _ _ = IH p∈
  QED | ⟫ FinalizeBlock _ _ _ _ = IH p∈
... | DishonestLocalStep {p = p′}{m} ¬hp′ h⇒m∈
  = QED
  where
  QED : b .epoch ≤ s′ .e-now
  QED with m ∙block ≟ b
  ... | no b≢
    = IH $ voteIds-∷˘′ b≢ p∈
  ... | yes refl
    with m ∙pid ≟ p
  ... | no p≢
    = IH $ voteIds-∷˘ {ms = s .history} p≢ p∈
  ... | yes refl
    = IH $ voteIds-accept∈ (h⇒m∈ it) refl refl

NoFutureVotes≢ : StateProperty
NoFutureVotes≢ s = ∀ {p b} ⦃ _ : Honest p ⦄ →
  ∙ p ∈ voteIds (s .history) b
  ∙ (s ＠ p) .phase ≡ Ready
    ──────────────────────────
    b .epoch ≢ s .e-now

noFutureVotes≢ : Invariant NoFutureVotes≢
noFutureVotes≢ (_ , refl , (_ ∎)) ()
noFutureVotes≢ {s′} (_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p}{b} p∈ ph≡
  with Rs ← -, refl , tr
  with IH ← noFutureVotes≢ Rs {b = b} ⦃ it ⦄
  with s→
... | Deliver {env = [ p′ ∣ m′ ⟩} env∈
  = IH p∈ $ subst (_≡ _) ＠ph≡ ph≡
  where
  open ∣Deliver∣ p s env∈
... | AdvanceEpoch
  = Nat.<⇒≢ $ Nat.s≤s QED
  where
  QED : b .epoch ≤ s .e-now
  QED = noFutureVotes≤ Rs p∈
... | Drop _ = IH p∈ ph≡
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′

  QED : b .epoch ≢ s′ .e-now
  QED with ⟫ ls→
  QED | ⟫ ProposeBlock {ch = ch} {txs = txs} ph≡′ refl _ _
    with p ≟ p′
  ... | yes refl rewrite lookup✓
    = ⊥-elim (case ph≡ of λ ())
  ... | no p≢ rewrite lookup✖ p≢
    = IH p∈′ ph≡
    where
    p∈′ : p ∈ voteIds (s .history) b
    p∈′ = voteIds-∷˘ {ms = s .history} (Eq.≢-sym p≢) p∈
  QED | ⟫ VoteBlock {H = H} {txs = txs} M∈ _ _ _ _ _
    with p ≟ p′
  ... | yes refl rewrite lookup✓
    = ⊥-elim (case ph≡ of λ ())
  ... | no p≢ rewrite lookup✖ p≢
    = IH p∈′ ph≡
    where
    p∈′ : p ∈ voteIds (s .history) b
    p∈′ = voteIds-∷˘ {ms = s .history} (Eq.≢-sym p≢) p∈
  QED | ⟫ RegisterVote m∈ _
    = IH p∈ ph≡′
    where
    ＠ph≡ : (s′ ＠ p) .phase ≡ (s ＠ p) .phase
    ＠ph≡ with p ≟ p′
    ... | no p≢ rewrite lookup✖ p≢ = refl
    ... | yes refl rewrite lookup✓ = refl

    ph≡′ : (s ＠ p) .phase ≡ Ready
    ph≡′ = subst (_≡ _) ＠ph≡ ph≡
  QED | ⟫ FinalizeBlock ch _ _ _
      = IH p∈ ph≡′
      where
      ＠ph≡ : (s′ ＠ p) .phase ≡ (s ＠ p) .phase
      ＠ph≡ with p ≟ p′
      ... | no p≢ rewrite lookup✖ p≢ = refl
      ... | yes refl rewrite lookup✓ = refl

      ph≡′ : (s ＠ p) .phase ≡ Ready
      ph≡′ = subst (_≡ _) ＠ph≡ ph≡
... | DishonestLocalStep {p = p′}{m} ¬hp′ h⇒m∈
  = QED
  where
  QED : b .epoch ≢ s′ .e-now
  QED with m ∙block ≟ b
  ... | no b≢
    = IH (voteIds-∷˘′ b≢ p∈) ph≡
  ... | yes refl
    with m ∙pid ≟ p
  ... | no p≢
    = IH (voteIds-∷˘ {ms = s .history} p≢ p∈) ph≡
  ... | yes refl
    = IH (voteIds-accept∈ (h⇒m∈ it) refl refl) ph≡

NoFutureVotes< : StateProperty
NoFutureVotes< s = ∀ {p b} ⦃ _ : Honest p ⦄ →
  ∙ p ∈ voteIds (s .history) b
  ∙ (s ＠ p) .phase ≡ Ready
    ──────────────────────────
    b .epoch < s .e-now

noFutureVotes< : Invariant NoFutureVotes<
noFutureVotes< Rs p∈ ph≡ =
  Nat.≤∧≢⇒< (noFutureVotes≤ Rs p∈) (noFutureVotes≢ Rs p∈ ph≡)

NoFutureOwnVotes : StateProperty
NoFutureOwnVotes s = ∀ {p m} ⦃ _ : Honest p ⦄ →
  ∙ (m ∙block) .epoch ≡ s .e-now
  ∙ (s ＠ p) .phase ≡ Ready
  ∙ p ≡ m ∙pid
    ──────────────────────────────
    m ∉ (s ＠ p) .db

noFutureOwnVotes : Invariant NoFutureOwnVotes
noFutureOwnVotes (_ , refl , (_ ∎)) {p} bₑ≡e-now ready refl
  rewrite let open ∣Base∣ p in lookup✓
  = L.Any.¬Any[]
noFutureOwnVotes Rs@(_ , refl , (s ⟨ _ ⟩←— _))
  {p} {m} bₑ≡enow ready refl m∈db
  = Nat.<⇒≢ bₑ<enow bₑ≡enow
  where
    B = m ∙block

    m∈ : m ∈ s .history
    m∈ = historyComplete Rs m∈db

    p∈ : p ∈ voteIds (s .history) B
    p∈ = voteIds-accept∈ m∈ refl refl

    bₑ<enow : B .epoch < s .e-now
    bₑ<enow =  noFutureVotes< Rs {p} {B} p∈ ready
```
