<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants.Uniqueness (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯

open import Protocol.Streamlet.Invariants.Votes ⋯
```
-->

```agda
UniqueVotes : StateProperty
UniqueVotes s = ∀ {p} ⦃ _ : Honest p ⦄ →
  ────────────────────────────────────────
  Unique $ map _∙signedBlock ((s ＠ p) .db)

uniqueVotes : Invariant UniqueVotes
uniqueVotes (_ , refl , (_ ∎)) {p}
  rewrite let open ∣Base∣ p in lookup✓
  = []
uniqueVotes {s′} (_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p} ⦃ hp ⦄
  with Rs ← -, refl , tr
  with IH ← uniqueVotes Rs ⦃ it ⦄
  with s→
... | Deliver  {env = [ p′ ∣ m′ ⟩} env∈
  = QED
  where
  open ∣Deliver∣ p s env∈

  QED : Unique $ map _∙signedBlock ((s′ ＠ p) .db)
  QED rewrite db≡ = IH
... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH
... | Drop _
  = IH
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′
  ≪db = (s ＠ p) .db

  QED : Unique $ map _∙signedBlock ((s′ ＠ p) .db)
  QED with p ≟ p′
  QED | no p≢ rewrite lookup✖′ p≢ = IH
  QED | yes refl
    with ⟫ ls→
  QED | yes refl | ⟫ ProposeBlock {ch} {txs} ready refl _ _
    rewrite lookup✓
    = L.All.¬Any⇒All¬ _ SB∉ ∷ IH
    where
    open ∣ProposeBlock∣ p′ ⦃ hp ⦄ s ch txs hiding (M; ≪db)
    Mᵖ = Propose SB
    M  = Vote    SB

    mp∉   : Mᵖ ∉ ≪db
    mp∉   = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

    mv∉   : M ∉ ≪db
    mv∉   = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

    SB∉ : SB ∉ map _∙signedBlock ≪db
    SB∉  SB∈ with L.Mem.∈-map⁻ _∙signedBlock SB∈
    ... | Propose _ , m∈≪db , refl = mp∉ m∈≪db
    ... | Vote _ , m∈≪db , refl = mv∉ m∈≪db
  QED | yes refl | ⟫ VoteBlock {H} {txs} _ sp∉ ready ¬L _ _
    rewrite lookup✓
    = L.All.¬Any⇒All¬ _ sv∉∷
    ∷ L.All.¬Any⇒All¬ _ sp∉
    ∷ IH
    where
    open ∣VoteBlock∣ p ⦃ hp ⦄ s H txs hiding (≪db)

    mv∉ : M ∉ ≪db
    mv∉ = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

    mvp∉ : Propose SB ∉ ≪db
    mvp∉ = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

    sv∉ : SB ∉ map _∙signedBlock ≪db
    sv∉ sv∈ with L.Mem.∈-map⁻ _∙signedBlock sv∈
    ... | Propose _ , m∈≪db , refl = mvp∉ m∈≪db
    ... | Vote _    , m∈≪db , refl = mv∉ m∈≪db

    sv∉∷ : SB ∉ SBᵖ ∷ map _∙signedBlock ≪db
    sv∉∷ = sv∉ ∘ L.Any.tail (¬L ∘ cong _∙pid)
  QED | yes refl | ⟫ RegisterVote {sb} m∈inbox sb∉db
    rewrite lookup✓ = L.All.¬Any⇒All¬ _ sb∉db ∷ IH
  QED | yes refl | ⟫ FinalizeBlock ch _ _ _
    rewrite lookup✓ = IH
... | DishonestLocalStep {p = p′}{mm} ¬hp′ h⇒m∈
  = subst (Unique ∘ map _∙signedBlock) db≡ IH
  where
  open ∣DishonestLocalStep∣ p p′ ¬hp′ s mm
```

## Unique Vote Ids

```
UniqueVoteIds : StateProperty
UniqueVoteIds s = ∀ {p b} ⦃ _ : Honest p ⦄ →
  ────────────────────────────────
  Unique $ voteIds ((s ＠ p) .db) b

uniqueVoteIds : Invariant UniqueVoteIds
uniqueVoteIds (_ , refl , (_ ∎)) {p}
  rewrite let open ∣Base∣ p in lookup✓
  = []
uniqueVoteIds {s′} (_ , refl ,  (_ ⟨ s→ ∣ s ⟩←— tr))
  {p}{b} ⦃ hp ⦄
  with Rs ← -, refl , tr
  with IH ← uniqueVoteIds Rs {b = b} ⦃ it ⦄
  with s→
... | Deliver {env = [ p′ ∣ m′ ⟩} env∈
  = QED
  where
  open ∣Deliver∣ p s env∈

  QED :  Unique $ voteIds ((s′ ＠ p) .db) b
  QED rewrite db≡ = IH
... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH
... | Drop env∈
  = IH
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′
  ≪db = (s ＠ p) .db

  voteIds-lemma : ∀ b p {ms} →
    b signed-by p ∉ map _∙signedBlock ms
    ────────────────────────────────────
    p ∉ voteIds ms b
  voteIds-lemma b p {ms} sb∉ p∈ =
    let m , m∈ , eq = voteIds⁻ {ms = ms} {b = b} p∈
    in  sb∉ $ subst (_∈ _) eq (L.Mem.∈-map⁺ _∙signedBlock m∈)

  QED : Unique $ voteIds ((s′ ＠ p) .db) b
  QED
    with p ≟ p′
  QED | no  p≢ rewrite lookup✖′ p≢ = IH
  QED | yes refl
    with ⟫ ls→
  QED | yes refl | ⟫ ProposeBlock {ch} {txs} ready refl _ _
    rewrite lookup✓
    = QED′
    where
    open ∣ProposeBlock∣ p′ ⦃ hp ⦄ s ch txs hiding (≪db)

    QED′ : Unique $ voteIds (M ∷ ≪db) b
    QED′
      with B ≟ b
    ... | yes refl
      rewrite votes-accept M ≪db refl
      = L.All.¬Any⇒All¬ _ L∉
      ∷ IH
      where
      mv∉ : Vote SB ∉ ≪db
      mv∉ = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

      mp∉ : M ∉ ≪db
      mp∉ = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

      SB∉ : SB ∉ map _∙signedBlock ≪db
      SB∉ svp∈ with L.Mem.∈-map⁻ _∙signedBlock svp∈
      ... | Propose _ , m∈≪db , refl = mp∉ m∈≪db
      ... | Vote    _ , m∈≪db , refl = mv∉ m∈≪db

      L∉ : L ∉ voteIds ≪db B
      L∉ = voteIds-lemma B L SB∉
    ... | no ¬q
      rewrite votes-reject M ≪db ¬q
      = IH
  QED | yes refl | ⟫ VoteBlock {H} {txs} m∈ sb∉ ready ¬L _ _
    rewrite lookup✓
    = QED′
    where
    open ∣VoteBlock∣ p′ ⦃ hp ⦄ s H txs hiding (≪db)
    Mᵖ′ = Propose SB

    QED′ : Unique $ voteIds (M ∷ Mᵖ ∷ ≪db) b
    QED′ with B ≟ b
    ... | yes refl
      rewrite votes-accept M (Mᵖ ∷ ≪db) refl | votes-accept Mᵖ ≪db refl
      = L.All.¬Any⇒All¬ _ p∉∷ ∷ L.All.¬Any⇒All¬ _ L∉ ∷ IH
      where
      mv∉ : M ∉ ≪db
      mv∉ = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

      mp∉∷ : M ∉ Mᵖ ∷ ≪db
      mp∉∷ (there mv∈) = mv∉ mv∈

      mp∉ : Mᵖ′ ∉ ≪db
      mp∉ = noFutureOwnVotes Rs ⦃ hp ⦄ refl ready refl

      SB∉ : SB ∉ map _∙signedBlock ≪db
      SB∉ svp∈ with L.Mem.∈-map⁻ _∙signedBlock svp∈
      ... | Propose _ , m∈≪db , refl = mp∉ m∈≪db
      ... | Vote _ , m∈≪db , refl = mv∉ m∈≪db

      p∉ : p ∉ voteIds ≪db B
      p∉ = voteIds-lemma B p SB∉

      p∉∷ : p ∉ L ∷ voteIds ≪db B
      p∉∷ (here p≡L) = ⊥-elim (¬L p≡L)
      p∉∷ (there p∈) = ⊥-elim (p∉ p∈)

      L∉ : L ∉ voteIds ≪db B
      L∉ = voteIds-lemma B L {≪db} sb∉
    ... | no ¬q
      rewrite votes-reject M (Mᵖ ∷ ≪db) ¬q | votes-reject Mᵖ ≪db ¬q
      = IH
  QED | yes refl | ⟫ RegisterVote {sb} m∈inbox sb∉db
    rewrite lookup✓
    with sb ∙block ≟ b
  ... | yes refl
    rewrite votes-accept (Vote sb) ≪db refl
    = L.All.¬Any⇒All¬ _ p∉
    ∷ IH
    where
    p∉ : _ ∉ voteIds ≪db (sb .block)
    p∉ = voteIds-lemma _ _ sb∉db
  ... | no ¬q
    rewrite votes-reject (Vote sb) ≪db ¬q
    = IH
  QED | yes refl | ⟫ FinalizeBlock ch _ _ _
    rewrite lookup✓
    = IH
... | DishonestLocalStep {p = p′}{mm} ¬hp′ _
  = subst (λ ◆ → Unique $ voteIds ◆ b) db≡ IH
  where
  open ∣DishonestLocalStep∣ p p′ ¬hp′ s mm
```
