{-# OPTIONS --safe #-}
open import Prelude.Init
open import Prelude.Decidable

-- Vectors of all (bounded) natural numbers satisfying a predicate.
-- TODO: consider alternative using `Vec.Bounded.Vec≤`?
module Prelude.PVec {n} (P : Pred (Fin n) ℓ) ⦃ _ : P ⁇¹ ⦄ where

open import Prelude.PFin public
  using (pweaken)
  renaming (pweaken-injective to ↑-injective)

pFins : List (Fin n)
pFins = filter ¿ P ¿¹ (L.allFin n)

PVec : Type ℓ → Type ℓ
PVec A = Vec A (length pFins)

PIndex = ∃· P
↑_ = pweaken {P = P}

private variable A : Type ℓ

pLookup : PVec A → PIndex → A
pLookup vs i = V.lookup vs (↑ i)

module _ {A : Type ℓ} i ⦃ _ : P i ⦄ where
  pLookup-replicate = V.lookup-replicate {A = A} (↑ (i ,· it))
  pLookup∘updateAt = V.lookup∘updateAt {A = A} (↑ (i ,· it))
  module _ j ⦃ _ : P j ⦄ where
    pLookup∘updateAt′ = V.lookup∘updateAt′ {A = A} (↑ (i ,· it)) (↑ (j ,· it))
  module _ {B : Type ℓ′} where
    pLookup-map = V.lookup-map {A = A} {B = B} (↑ (i ,· it))

infixl 6 _[_]%=_ _[_]≔_

_[_]%=_ : PVec A → Fin n → (A → A) → PVec A
xs [ i ]%= f =
  case ¿ P i ¿ of λ where
    (yes p) → xs V.[ ↑ (i ,· p) ]%= f
    (no ¬p) → xs

_[_]≔_ : PVec A → PIndex → A → PVec A
xs [ i ]≔ y = xs V.[ ↑ i ]≔ y
