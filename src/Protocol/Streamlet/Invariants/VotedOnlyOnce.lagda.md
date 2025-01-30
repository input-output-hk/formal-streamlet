<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants.VotedOnlyOnce (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯

open import Protocol.Streamlet.Invariants.Unforgeability ⋯
open import Protocol.Streamlet.Invariants.Votes ⋯
```
-->

```agda
VotedOnlyOncePerEpoch¹ : StateProperty
VotedOnlyOncePerEpoch¹ s = ∀ {p} ⦃ _ : Honest p ⦄ → let ms = (s ＠ p) .db in
  ∀ {b b′} →
  ∙ p ∈ voteIds ms b
  ∙ p ∈ voteIds ms b′
  ∙ b .epoch ≡ b′ .epoch
    ────────────────────
    b ≡ b′

votedOnlyOncePerEpoch¹ : Invariant VotedOnlyOncePerEpoch¹
votedOnlyOncePerEpoch¹ (_ , refl , (_ ∎)) {p} p∈ _ _
  rewrite let open ∣Base∣ p in lookup✓
  = case p∈ of λ ()
votedOnlyOncePerEpoch¹ {s′} (_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p} ⦃ hp ⦄ {b} {b′} p∈ p∈′ refl
  with Rs ← -, refl , tr
  with IH ← votedOnlyOncePerEpoch¹ Rs {p}{b}{b′}
  with s→
... | Deliver {env = [ p′ ∣ m′ ⟩} env∈
  = uncurry IH ≪p∈ refl
  where
  open ∣Deliver∣ p s env∈

  ≪p∈ : p ∈ voteIds ((s ＠ p) .db) b
      × p ∈ voteIds ((s ＠ p) .db) b′
  ≪p∈ rewrite db≡ = p∈ , p∈′
... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH p∈ p∈′ refl
... | Drop _
  = IH p∈ p∈′ refl
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′

  nfo = noFutureOwnVotes Rs

  QED : b ≡ b′
  QED with p ≟ p′
  QED | no p≢ = IH p∈✖ p∈′✖ refl
    where
    p∈✖ : p ∈ voteIds ((s ＠ p) .db) b
    p∈✖ with ⟫ mm
    ... | ⟫ just _  rewrite lookup✖ p≢ = p∈
    ... | ⟫ nothing rewrite lookup✖ p≢ = p∈

    p∈′✖ : p ∈ voteIds ((s ＠ p) .db) b′
    p∈′✖ with ⟫ mm
    ... | ⟫ just _  rewrite lookup✖ p≢ = p∈′
    ... | ⟫ nothing rewrite lookup✖ p≢ = p∈′
  QED | yes refl
    rewrite lookup✓
    with ⟫ ls→
  QED | yes refl | ⟫ ProposeBlock {ch} {txs} ready pLeader _ _
    rewrite lookup✓
    with s .e-now ≟ b .epoch
  ... | no b≢
    = IH (voteIds-∷˘′ {b = b}  (b≢ ∘ cong epoch) p∈)
         (voteIds-∷˘′ {b = b′} (b≢ ∘ cong epoch) p∈′)
         refl
  ... | yes refl =
    let ≡b  , _ = voteIds-head b  p∉  p∈
        ≡b′ , _ = voteIds-head b′ p∉′ p∈′
    in trans (sym ≡b) ≡b′
    where
    open ∣ProposeBlock∣ p ⦃ hp ⦄ s ch txs

    m∉ : ∀ {m} → m ∙block ≡ b → p ≡ m ∙pid → m ∉ ≪db
    m∉ refl p≡ = nfo ⦃ hp ⦄ refl ready p≡

    m∉′ : ∀ {m} → m ∙block ≡ b′ → p ≡ m ∙pid → m ∉ ≪db
    m∉′ refl p≡ = nfo ⦃ hp ⦄ refl ready p≡

    findMessage : ∀ {b} → p ∈ voteIds ≪db b →
      ∃ λ m → m ∙block ≡ b × p ≡ m ∙pid × m ∈ ≪db
    findMessage p∈b
      with mᵇ , m∈filter , refl ← L.Mem.∈-map⁻ _∙pid p∈b
      with m∈ , q ← L.Mem.∈-filter⁻ _ m∈filter
      = mᵇ , sym q , refl ,  m∈

    p∉ : p ∉ voteIds ≪db b
    p∉ p∈
      with m , refl , refl , m∈ ← findMessage p∈
      = ⊥-elim $ m∉ refl refl m∈

    p∉′ : p ∉ voteIds ≪db b′
    p∉′ p∈
      with m , refl , refl , m∈ ← findMessage p∈
      = ⊥-elim $ m∉′ refl refl m∈
  QED | yes refl | ⟫ VoteBlock {H} {txs} _ _ ready ¬L _ _
    rewrite lookup✓
    with s .e-now ≟ b .epoch
  ... | no b≢
    = IH ( voteIds-∷˘  {b = b}  (Eq.≢-sym ¬L)
         $ voteIds-∷˘′ {b = b}  (b≢ ∘ cong epoch) p∈)
         ( voteIds-∷˘  {b = b′} (Eq.≢-sym ¬L)
         $ voteIds-∷˘′ {b = b′} (b≢ ∘ cong epoch) p∈′)
         refl
  ... | yes refl =
    let ≡b  , _ = voteIds-head b  p∉  p∈
        ≡b′ , _ = voteIds-head b′ p∉′ p∈′
    in trans (sym ≡b) ≡b′
    where
    open ∣VoteBlock∣ p ⦃ hp ⦄ s H txs

    m∉ : ∀ {m} → m ∙block ≡ b → p ≡ m ∙pid → m ∉ ≪db
    m∉ refl p≡ = nfo ⦃ hp ⦄ refl ready p≡

    m∉′ : ∀ {m} → m ∙block ≡ b′ → p ≡ m ∙pid → m ∉ ≪db
    m∉′ refl p≡ = nfo ⦃ hp ⦄ refl ready p≡

    findMessage : ∀ {b} → p ∈ voteIds ≪db b →
      ∃ λ m → m ∙block ≡ b × p ≡ m ∙pid × m ∈ ≪db
    findMessage p∈b
      with mᵇ , m∈filter , refl ← L.Mem.∈-map⁻ _∙pid p∈b
      with m∈ , q ← L.Mem.∈-filter⁻ _ m∈filter
      = mᵇ , sym q , refl ,  m∈

    p∉b : p ∉ voteIds ≪db b
    p∉b p∈b
      with m , refl , refl , m∈ ← findMessage p∈b
      = ⊥-elim $ m∉ refl refl m∈

    p∉b′ : p ∉ voteIds ≪db b′
    p∉b′ p∈
      with m , refl , refl , m∈ ← findMessage p∈
      = ⊥-elim $ m∉′ refl refl m∈

    p∉ : p ∉ voteIds (Mᵖ ∷ ≪db) b
    p∉ p∈ = ⊥-elim $ p∉b $ voteIds-∷˘ {b = b} (Eq.≢-sym ¬L) p∈

    p∉′ : p ∉ voteIds (Mᵖ ∷ ≪db) b′
    p∉′ p∈ = ⊥-elim $ p∉b′ $ voteIds-∷˘ {b = b′} (Eq.≢-sym ¬L) p∈
  QED | yes refl | ⟫ RegisterVote {sb} m∈inbox sb∉db
    rewrite lookup✓
    = IH (voteIds-∷˘ {b = b}  p≢ p∈)
         (voteIds-∷˘ {b = b′} p≢ p∈′)
         refl
    where
    m∉ : Vote sb ∉ (s ＠ p′) .db
    m∉ m∈ = sb∉db (L.Mem.∈-map⁺ _∙signedBlock m∈)

    p≢ : (Vote sb) ∙pid ≢ p
    p≢ with sb ∙pid ≟ p
    ... | yes p≡ = ⊥-elim $ m∉ $ unforgeability Rs ⦃ hp ⦄ m∈inbox $ sym p≡
    ... | no  p≢ = p≢
  QED | yes refl | ⟫ FinalizeBlock ch b x x₁
    rewrite lookup✓
    = IH p∈ p∈′ refl
... | DishonestLocalStep {p = p′}{mm} ¬hp′ h⇒m∈
  = uncurry IH ≪p∈ refl
  where
  open ∣DishonestLocalStep∣ p p′ ¬hp′ s mm

  ≪p∈ : p ∈ voteIds ((s ＠ p) .db) b
      × p ∈ voteIds ((s ＠ p) .db) b′
  ≪p∈ rewrite db≡ = p∈ , p∈′
```


```agda
VotedOnlyOncePerEpoch : StateProperty
VotedOnlyOncePerEpoch s = ∀ {p p′} ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
  let ms = (s ＠ p) .db in
  ∀ {b b′} →
  ∙ p′ ∈ voteIds ms b
  ∙ p′ ∈ voteIds ms b′
  ∙ b .epoch ≡ b′ .epoch
    ────────────────────
    b ≡ b′

votedOnlyOncePerEpoch : Invariant VotedOnlyOncePerEpoch
votedOnlyOncePerEpoch Rs p∈ p∈′ =
  votedOnlyOncePerEpoch¹ Rs (messageSharing Rs p∈) (messageSharing Rs p∈′)
```
