# Global properties of the whole Streamlet protocol

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude hiding (ℓ)
open import Hash
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Consistency (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
  hiding (vch; vch′; ls; ms; ms′)

open import Protocol.Streamlet.Decidability ⋯
open import Protocol.Streamlet.Invariants ⋯
```
-->

## Global invariants

We characterize the invariants that hold for global states
obtained from valid executions.

All honest nodes should have valid local states,
in addition to global invariants that relate different participants:

- *Message sharing:*
a participant always stores their own messages in their local message state
(even if observed by another participant).

- *Increasing epochs:*
partipants cannot vote for a block of a previous epoch,
i.e. the epochs of blocks being voted on is *monotonic*.

### Honest intersection

The intersection of two quorums (unique votes from a majority of at least 2n/3 nodes)
contains at least one honest node.

```agda
honest-intersection : ∀ {vs vs′ : List Pid} →
  ∙ Unique vs
  ∙ Unique vs′
  ∙ IsMajority vs
  ∙ IsMajority vs′
    ─────────────────────────────────────────
    Σ Pid (λ p → Honest p × p ∈ vs × p ∈ vs′)
honest-intersection {vs}{vs′} u u′ maj maj′ =
  let
    vs∩ = vs ∩ vs′

    u∩ : Unique vs∩
    u∩ = Unique-∩ u

    len≥n/3 : 3 * length vs∩ ≥ nodes
    len≥n/3 = let open Nat; open ≤-Reasoning in
      ≤-Reasoning.begin
        nodes
      ≡˘⟨ *-identityˡ _ ⟩
        1 * nodes
      ≡⟨ *-distribʳ-∸ nodes 4 3 ⟩
        4 * nodes ∸ 3 * nodes
      ≡⟨ cong (_∸ 3 * nodes) $ *-distribʳ-+ nodes 2 2 ⟩
        (2 * nodes + 2 * nodes) ∸ 3 * nodes
      ≤⟨ ∸-monoˡ-≤ (3 * nodes)
       $ ≤-Reasoning.begin
           2 * nodes + 2 * nodes
         ≤⟨ +-monoʳ-≤ (2 * nodes) maj′  ⟩
           2 * nodes + 3 * length vs′
         ≤⟨ +-monoˡ-≤ _ maj ⟩
           3 * length vs + 3 * length vs′
         ≡˘⟨ *-distribˡ-+ 3 (length vs) _ ⟩
           3 * (length vs + length vs′)
         ≤-Reasoning.∎
       ⟩
        3 * (length vs + length vs′) ∸ 3 * nodes
      ≡˘⟨ *-distribˡ-∸ 3 _ nodes ⟩
        3 * (length vs + length vs′ ∸ nodes)
      ≤⟨ *-mono-≤ {x = 3} ≤-refl $ length-∩ u u′ ⟩
        3 * length vs∩
      ≤-Reasoning.∎

    ∃p : Any Honest vs∩
    ∃p = honestFromMajority u∩ len≥n/3

    p , p∈vs , hp = L.Mem.find ∃p
    p∈ , p∈′ = ∈-∩⁻ p vs vs′ p∈vs
  in
    p , hp , p∈ , p∈′
```

### Unique Notarization per epoch

** Paper statement **
Suppose that f < n/3. Then, for each epoch e,
there can be at most one notarized block for epoch e in honest view.

In honest view, there can only be a unique notarization per epoch.
That is, there cannot be two different notarized blocks for the same epoch.

```agda
-- Lemma 1 (≈ Lemma 10)
UniqueNotarization : StateProperty
UniqueNotarization s = ∀ {p p′ b b′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let ms = (s ＠ p) .db ; ms′ = (s ＠ p′) .db in
  ∙ NotarizedBlock ms b
  ∙ NotarizedBlock ms′ b′
  ∙ b .epoch ≡ b′ .epoch
    ────────────────────
    b ≡ b′
```

** Proof **
Suppose that two blocks B and B′, both of epoch e, are notarized in honest view.
It must be that at least 2n/3 nodes, denoted the set S, signed the block B, and
at least 2n/3 nodes, denoted the set S′, signed the block B′.
Since there are only n nodes in total, S ∩ S′ must have size at least n/3, and thus
at least one honest node is in S ∩ S′. According to our protocol, every honest node
votes for at most one block per epoch. This means that B = B′. ∎

```agda
uniqueNotarization : Invariant UniqueNotarization
uniqueNotarization (_ , refl , (_ ∎)) {p} {b} {b′} nb nb′ e≡
  rewrite let open ∣Base∣ p in lookup✓
  = ⊥-elim $ Nat.1+n≰n (votesNonempty nb)
uniqueNotarization Rs′@(_ , refl , (s′ ⟨ _ ⟩←— _)) {p} {p′} {b} {b′} nb nb′ e≡
    with b ≟ b′
... | yes b≡ = b≡
... | no  b≢ = ⊥-elim QED
    where
      QED : ⊥
      QED =
        let
          ms = (s′ ＠ p) .db
          ms′ = (s′ ＠ p′) .db

          vs  = voteIds ms b
          vs′ = voteIds ms′ b′

          uvs : ∀ {b} → Unique $ voteIds ms b
          uvs {b} = uniqueVoteIds Rs′

          uvs′ : ∀ {b} → Unique $ voteIds ms′ b
          uvs′ {b} = uniqueVoteIds Rs′

          mvs  : IsMajority vs
          mvs  = enoughVoteIds nb

          mvs′ : IsMajority vs′
          mvs′ = enoughVoteIds nb′

          p″ , hp″ , p∈ , p∈′ = honest-intersection uvs uvs′ mvs mvs′
          instance _ = hp″

          b≡ : b ≡ b′
          b≡ = votedOnlyOncePerEpoch Rs′ (messageSharing Rs′ p∈) (messageSharing Rs′ p∈′) e≡
        in
          b≢ b≡
```

### Main Consistency Lemma

** Paper statement **
If some honest node sees a notarized chain with three adjacent blocks B0 , B1 , B2
with consecutive epoch numbers e, e + 1, and e + 2,
then there cannot be a conflicting block B ≠ B1 that also gets notarized
in honest view at the same length as B1.
ADDENDUM: B derives its length from its parent chain (assuming a valid chain sequence)

```agda
-- Lemma 2 (≈ Lemma 14)
ConsistencyLemma : StateProperty
ConsistencyLemma s = ∀ {p p′ b b′ b″ ch ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let
    ms  = (s ＠ p)  .db
    ms′ = (s ＠ p′) .db
  in
  ∙ (b″ ∷ b ∷ ch) chain-∈ ms
  ∙ FinalizedChain ms (b ∷ ch) b″

  -- NB: this is actually sufficient
  -- ∙ (b′ ∷ ch′) chain-∈ ms
  -- ∙ NotarizedBlock (ls .db) b′

  ∙ (b′ ∷ ch′) notarized-chain-∈ ms′
  ∙ length ch′ ≡ length ch
    ──────────────────────────────
    b ≡ b′
```

** Paper proof **
Essentially the same as the argument above, but with generalized parameters rather than
6, 7, and 8. We defer the proof to the Appendix, in Section B Lemma 14.

```agda
consistencyLemma : Invariant ConsistencyLemma
consistencyLemma (_ , refl , (_ ∎)) {p} (m∈ ∷ _ ⊣ _) _ _ _
  rewrite let open ∣Base∣ p in lookup✓
  = case m∈ of λ ()
consistencyLemma Rs@(_ , refl , (s ⟨ _ ⟩←— _)) {p} {p′} {B₁} {B} {B₂} {ch@(B₀ ∷ ch₀)} {ch′}
  ch∈@(_ ∷ ch₁∈@(_ ∷ (_ ∷ _ ⊣ B₀connects) ⊣ _) ⊣ B₂connects)
  fch@(Finalize nch@(nB₂ ∷ nB₁ ∷ nB₀ ∷ _) e₂≡ e₁≡)
  nc∈′@(ch∈′@(B∈ ∷ ch′∈ ⊣ Bconnects) , (nB ∷ _))
  len≡
  with B₁ ≟ B
... | yes B₁≡B = B₁≡B
... | no  B₁≢B = ⊥-elim QED
  where
  open Nat
  -- * messages
  ms  = (s ＠ p) .db
  ms′ = (s ＠ p′) .db

  -- * epochs
  eᴮ = B  .epoch
  e₀ = B₀ .epoch
  e₁ = B₁ .epoch
  e₂ = B₂ .epoch

  -- * lengths
  ch₁ = B₁ ∷ ch
  ch₂ = B₂ ∷ ch₁

  ℓ-1 = length ch₀
  ℓ   = length ch
  ℓ+1 = length ch₁
  ℓ+2 = length ch₂
  ℓᴮ  = length (B ∷ ch′)

  ℓᴮ≡ : ℓᴮ ≡ ℓ+1
  ℓᴮ≡ = cong suc len≡

  -- * validity
  vch₂ : ValidChain ch₂
  vch₂ = chain-∈⇒Valid ch∈

  vch : ValidChain ch
  vch = uncons-vc $ uncons-vc vch₂

  vch′ : ValidChain (B ∷ ch′)
  vch′ = chain-∈⇒Valid ch∈′

  ch∈₀ : ch chain-∈ ms
  ch∈₀ = uncons-ch∈ $ uncons-ch∈ ch∈

  nch∈′ : ch′ notarized-chain-∈ ms′
  nch∈′ = notarized-chain-∈-tail nc∈′

  nch∈₁ : ch₁ notarized-chain-∈ ms
  nch∈₁ = ch₁∈ , L.All.tail nch

  nch∈₀ : ch₀ notarized-chain-∈ ms
  nch∈₀ = notarized-chain-∈-tail $ notarized-chain-∈-tail nch∈₁

  -- B ∉ {B₀, B₁, B₂}
  B₀≢B : B₀ ≢ B
  B₀≢B = ∣ch∣≢→b≢ vch vch′ (subst (_ ≢_) (sym len≡) $ Eq.≢-sym $ 1+n≢n)
  B₂≢B : B₂ ≢ B
  B₂≢B = ∣ch∣≢→b≢ (chain-∈⇒Valid ch∈) vch′
       $ subst (_ ≢_) (sym len≡) 1+n≢n

  -- honest intersection
  vsᴮ vsᴮ⁰ vsᴮ² : List Pid
  vsᴮ  = voteIds ms′ B
  vsᴮ⁰ = voteIds ms B₀
  vsᴮ² = voteIds ms B₂

  vsᴮ′ vsᴮ⁰′ vsᴮ²′ : List Pid
  vsᴮ′  = voteIds ms′ B
  vsᴮ⁰′ = voteIds ms′ B₀
  vsᴮ²′ = voteIds ms′ B₂

  uvs : ∀ {b} → Unique $ voteIds ms b
  uvs {b} = uniqueVoteIds Rs

  uvs′ : ∀ {b} → Unique $ voteIds ms′ b
  uvs′ {b} = uniqueVoteIds Rs

  mvsᴮ  : IsMajority vsᴮ′
  mvsᴮ  = enoughVoteIds nB
  mvsᴮ⁰ : IsMajority vsᴮ⁰
  mvsᴮ⁰ = enoughVoteIds nB₀
  mvsᴮ² : IsMajority vsᴮ²
  mvsᴮ² = enoughVoteIds nB₂

  B∩B₀ : ∃ λ p′ → Honest p′ × p′ ∈ vsᴮ × p′ ∈ vsᴮ⁰
  B∩B₀ = honest-intersection uvs′ uvs mvsᴮ mvsᴮ⁰

  B∩B₂ : ∃ λ p′ → Honest p′ × p′ ∈ vsᴮ × p′ ∈ vsᴮ²
  B∩B₂ = honest-intersection uvs′ uvs mvsᴮ mvsᴮ²

  QED : ⊥
  QED
    with eᴮ ≤? e₂ | ⟫ e₂≡ | ⟫ e₁≡
  ... | no eᴮ≰e₂ | _ | _
    -- Case (2): eᴮ > e + 2
    = ≤⇒≯ e₂≤eᴮ e₂>eᴮ
    where
    e₂≤eᴮ : e₂ ≤ eᴮ
    e₂≤eᴮ = ≮⇒≥ (≰⇒≮ eᴮ≰e₂)

    e₂>eᴮ : e₂ > eᴮ
    e₂>eᴮ =
      let
        p″ , hp″ , p∈′ , p∈ = B∩B₂
        instance _ = hp″

        len< : length ch′ < length ch₁
        len< = subst (_< _) (sym len≡)  (n<1+n ℓ)
      in
        increasingEpochs Rs p∈′ Bconnects p∈ B₂connects len<
  ... | yes e> | ⟫ e₂≡ | ⟫ e₁≡
    with ≤⇒≤′ e>
  ... | ≤′-refl
    = B₂≢B $ uniqueNotarization Rs nB₂ nB refl
  ... | ≤′-step ≤′-refl
    with e≡ ← suc-injective e₂≡
    = B₁≢B $ uniqueNotarization Rs nB₁ nB (sym e≡)
  ... | ≤′-step (≤′-step ≤′-refl)
    with e≡ ← suc-injective e₂≡
    = B₀≢B $ uniqueNotarization Rs nB₀ nB e≡′
    where e≡′ : e₀ ≡ eᴮ
          e≡′ = sym $ suc-injective $ trans e≡ e₁≡
  ... | ≤′-step (≤′-step eᴮ≤′)
    -- Case (1): eᴮ < e
    = ≤⇒≯ eᴮ≤e₀ eᴮ>e₀
    where
    eᴮ≤e₀ : eᴮ ≤ e₀
    eᴮ≤e₀ = subst (_ ≤_)
                  (suc-injective $ subst (_ ≡_) e₁≡ $ suc-injective e₂≡)
                  (≤′⇒≤ eᴮ≤′)

    eᴮ>e₀ : eᴮ > e₀
    eᴮ>e₀ =
      let
        p″ , hp″ , p∈′ , p∈ = B∩B₀
        instance _ = hp″

        len< : length ch₀ < length ch′
        len< = subst (_ <_) (sym len≡) (n<1+n ℓ-1)
      in
        increasingEpochs Rs p∈ B₀connects p∈′ Bconnects len<
```

### Consistency (a.k.a. safety)

** Paper statement **
Suppose that chain and chain' are two notarized chains in honest view
/both/ ending at three blocks with consecutive epoch numbers.
Denote the length of chain as ℓ, and the length of chain' as ℓ'.
Moreover, suppose that ℓ ≤ ℓ'. It must be that chain[: ℓ - 1] ≼ chain'[: ℓ' - 1].

** Strengthened version **
Suppose that chain and chain' are two notarized chains in honest view
/and the former/ ending at three blocks with consecutive epoch numbers.
Denote the length of chain as ℓ, and the length of chain' as ℓ'.
Moreover, suppose that ℓ ≤ ℓ'. It must be that chain[: ℓ - 1] ≼ chain'[: ℓ' - 1].

```agda
-- Theorem 3' (restricted version only for ≡)
ConsistencyEqualLen : StateProperty
ConsistencyEqualLen s = ∀ {p p′ b ch ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let
    ms  = (s ＠ p)  .db
    ms′ = (s ＠ p′) .db
  in
  ∙ (b ∷ ch) chain-∈ ms
  ∙ ch′ notarized-chain-∈ ms′
  ∙ FinalizedChain ms ch b
  ∙ length ch ≡ length ch′
    ──────────────────────────────
    ch ≡ ch′
```

** Proof **
Suppose that chain and chain' are two finalized chains in honest view.
Denote the length of chain as ℓ, and the length of chain' as ℓ', and ℓ ≤ ℓ'.
It must be that chain[: ℓ - 1] ≼ chain'[: ℓ' - 1]. ∎

```agda
consistencyEqualLen : Invariant ConsistencyEqualLen
consistencyEqualLen (_ , refl , (_ ∎)) {p} (b∈ ∷ _ ⊣ _) _ _ _
  rewrite let open ∣Base∣ p in lookup✓
  = case b∈ of λ ()
consistencyEqualLen
  Rs@(_ , refl , (_ ⟨ x ⟩←— tr)) {p}{ch = ch} {ch′}
  b∷ch∈@(_ ∷ ch∈ ⊣ _) nch∈′@(ch∈′ , nch′) fch len≡
  = ch≡
  where
  ch≡ : ch ≡ ch′
  ch≡ with ch ≟ ch′
  ... | yes ch≡ = ch≡
  ... | no  ch≢
    with ⟫ B  ∷ _ ← ⟫ ch
    with ⟫ ch′    | ⟫ nch′
  ... | ⟫ B′  ∷ _ | ⟫ nB′ ∷ _
    = QED
    where
    vch : ValidChain ch
    vch = chain-∈⇒Valid ch∈

    vch′ : ValidChain ch′
    vch′ = chain-∈⇒Valid ch∈′

    b≢ : B ≢ B′
    b≢ b≡@refl = ch≢ $ cong (_ ∷_) (b≡→ch≡ vch vch′ b≡)

    b≡ : B ≡ B′
    b≡ = consistencyLemma Rs b∷ch∈ fch nch∈′ (sym $ Nat.suc-injective len≡)

    QED : _
    QED = ⊥-elim $ b≢ b≡
```

```agda
-- Theorem 3
Consistency : StateProperty
Consistency s = ∀ {p p′ b ch ch′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let
    ms  = (s ＠ p)  .db
    ms′ = (s ＠ p′) .db
  in
  ∙ (b ∷ ch) chain-∈ ms
  ∙ FinalizedChain ms ch b
  ∙ ch′ notarized-chain-∈ ms′
  ∙ length ch ≤ length ch′
    ──────────────────────────────
    ch ≼ ch′
```

** Paper proof **
Suppose chain[: ℓ − 1] is not a prefix of or equal to chain'[: ℓ' − 1].
Then it must be that chain[ℓ − 1] ≠ chain'[ℓ − 1];
in other words, they have different blocks at length ℓ − 1.
However, Lemma 2 precludes both of chain[ℓ − 1] and chain'[ℓ − 1]
from getting notarized in honest view. ∎

```agda
consistency : Invariant Consistency
consistency (_ , refl , (_ ∎)) {p} (b∈ ∷ _ ⊣ _) fch nch∈′ len≤
  rewrite let open ∣Base∣ p in lookup✓
  = case b∈ of λ ()
consistency Rs@(_ , refl , (_ ⟨ x ⟩←— tr)) {p} {ch = ch} {ch′} ch∈ fch nch∈′ len≤
  = QED
  where
  n   = length ch′ ∸ length ch
  ch″ = L.drop n ch′

  len≡ : length ch ≡ length ch″
  len≡ = sym $ ≡-Reasoning.begin
    length ch″     ≡⟨ L.length-drop n ch′ ⟩
    length ch′ ∸ n ≡⟨ Nat.m∸[m∸n]≡n len≤ ⟩
    length ch      ≡-Reasoning.∎ where open ≡-Reasoning

  nch∈″ : ch″ notarized-chain-∈ _
  nch∈″ = Suffix-nch∈ (Suffix-drop n) nch∈′

  QED′ : ch ≼ ch″
  QED′ = ≡⇒Suffix $ consistencyEqualLen Rs ch∈ nch∈″ fch len≡

  QED : ch ≼ ch′
  QED = L.Suf.trans trans QED′ (Suffix-drop n)
```
