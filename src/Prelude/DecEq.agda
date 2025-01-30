{-# OPTIONS --safe #-}
module Prelude.DecEq where

open import Prelude.Init

record DecEq (A : Type) : Type where
  field _≟_ : DecidableEquality A

  _==_ : A → A → Bool
  _==_ = ⌊_⌋ ∘₂ _≟_

  _≠_ : A → A → Bool
  x ≠ y = not (x == y)

  ≟-refl : ∀ (x : A) → (x ≟ x) ≡ yes refl
  ≟-refl x with refl , p ← dec-yes (x ≟ x) refl = p

  _≢?_ = ¬? ∘₂ _≟_

  infix 4 _≟_ _==_ _≠_ _≢?_

  open import Data.List.Membership.DecPropositional _≟_ public
    using (_∈?_; _∉?_)
open DecEq ⦃...⦄ public

private variable
  n : ℕ
  A B : Type

instance
  DecEq-⊤ : DecEq ⊤
  DecEq-⊤ ._≟_ _ _ = yes refl

  DecEq-Bool : DecEq Bool
  DecEq-Bool = record {BP}
    where import Data.Bool.Properties as BP

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ = record {Nat}

  DecEq-Fin : DecEq (Fin n)
  DecEq-Fin = record {Fi}

  DecEq-List : ⦃ DecEq A ⦄ → DecEq (List A)
  DecEq-List ._≟_ = L.≡-dec _≟_

  DecEq-Bin : DecEq Bitstring
  DecEq-Bin = record {Bin}

  DecEq-Maybe : ∀{A} → ⦃ DecEq A ⦄ → DecEq (Maybe A)
  DecEq-Maybe ._≟_ nothing  nothing  = yes refl
  DecEq-Maybe ._≟_ (just _) nothing  = no (λ where ())
  DecEq-Maybe ._≟_ nothing  (just _) = no (λ where ())
  DecEq-Maybe ._≟_ (just x) (just y) with x ≟ y
  ... | yes refl = yes refl
  ... | no ¬p    = no (λ where refl → ¬p refl)

  DecEq-Sum :  ⦃ DecEq A ⦄ →  ⦃ DecEq B ⦄ → DecEq (A ⊎ B)
  DecEq-Sum ._≟_ (inj₁ x) (inj₁ y) with x ≟ y
  ... | yes refl = yes refl
  ... | no ¬p = no (λ where refl → ¬p refl)
  DecEq-Sum ._≟_ (inj₁ x) (inj₂ y) = no (λ where ())
  DecEq-Sum ._≟_ (inj₂ x) (inj₁ y) = no (λ where ())
  DecEq-Sum ._≟_ (inj₂ x) (inj₂ y) with x ≟ y
  ... | yes refl = yes refl
  ... | no ¬p = no (λ where refl → ¬p refl)

DecEq-× :  ⦃ DecEq A ⦄ →  ⦃ DecEq B ⦄ → DecEq (A × B)
DecEq-× ._≟_ (x , y) (x′ , y′) with x ≟ x′ | y ≟ y′
... | yes refl | yes refl = yes refl
... | no ¬eq | _ = no λ where refl → ¬eq refl
... | _ | no ¬eq = no λ where refl → ¬eq refl
