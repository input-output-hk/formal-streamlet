<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants.Unforgeability (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯

open import Protocol.Streamlet.Invariants.History ⋯
```
-->

Messages in the inbox of an honest participant signed by themselves
are in that participants′ local database.

```agda
Unforgeability : StateProperty
Unforgeability s = ∀ {p m} ⦃ _ : Honest p ⦄ →
  ∙ m ∈ (s ＠ p) .inbox
  ∙ p ≡ m ∙pid
    ────────────────────
    m ∈ (s ＠ p) .db

unforgeability : Invariant Unforgeability
unforgeability (_ , refl , (._ ∎)) {p} m∈ refl
  rewrite let open ∣Base∣ p in lookup✓
  = case m∈ of λ ()
unforgeability {s′} (_ , refl , (_ ⟨ s→ ∣ s ⟩←— tr))
  {p} {m} m∈ refl
  with Rs ← -, refl , tr
  with IH ← (λ (m∈ : m ∈ (s ＠ p) .inbox) → unforgeability Rs m∈)
  with s→
... | Deliver {[ p′ ∣ m′ ⟩} env∈
  = QED
  where
  open ∣Deliver∣ p s env∈

  QED : m ∈ (s′ ＠ p) .db
  QED
    with honest? p′
  ... | no _ = IH m∈ refl
  ... | yes hp′
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ ⦃ hp′ ⦄ p≢ = IH m∈ refl
  ... | yes refl rewrite lookup✓ ⦃ it ⦄
    with m ≟ m′
  ... | yes refl = historySound Rs (networkComplete Rs env∈) refl
  ... | no m≢
    with ∈-∷ʳ⁻ m∈
  ... | inj₁ m∈ = IH m∈ refl
  ... | inj₂ m≡ = ⊥-elim $ m≢ m≡
... | AdvanceEpoch
  rewrite let open ∣AdvanceEpoch∣ p s in lookup✓
  = IH m∈ refl
... | Drop _
  = IH m∈ refl
... | LocalStep {p = p′}{mm}{ls′} ls→
  = QED
  where
  open ∣LocalStep∣ p p′ s mm ls′

  QED : m ∈ (s′ ＠ p) .db
  QED with p ≟ p′
  QED | no p≢ rewrite lookup✖′ p≢ = IH m∈inbox✖ refl
    where
    m∈inbox✖ : m ∈ (s ＠ m ∙pid) .inbox
    m∈inbox✖ rewrite sym $ lookup✖′ p≢ = m∈
  QED | yes refl rewrite lookup✓′ =
   case ls→ of λ where
    (ProposeBlock _ _ _ _) →
        let
          m∈db :  m ∈ (s ＠ p) .db
          m∈db = IH (m∈inbox✓ refl) refl
        in there m∈db
    (VoteBlock m∈ _ _ _ _ _) →
      let m∈inbox = ∈-─⁻ (AnyFirst⇒Any m∈) (m∈inbox✓ refl)
      in there $′ there $ IH m∈inbox refl
    (RegisterVote m∈ _) →
      let m∈inbox = ∈-─⁻ m∈ (m∈inbox✓ refl)
      in there $ IH m∈inbox refl
    (FinalizeBlock _ _ _ _) →
      IH (m∈inbox✓ refl) refl
   where
    m∈inbox✓ : p ≡ p′ → m ∈ ls′ .inbox
    m∈inbox✓ refl rewrite sym lookup✓′ = m∈
... | DishonestLocalStep _ _
  = IH m∈ refl
```
