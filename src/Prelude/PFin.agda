{-# OPTIONS --safe #-}
-- List of all (bounded) natural numbers that satisfy a predicate.
module Prelude.PFin where

open import Prelude.Init
open import Prelude.Decidable
open import Prelude.Lists

private module _ {n} {P : Pred (Fin (suc n)) ℓ} ⦃ _ : P ⁇¹ ⦄ where
  len≡ = let open ≡-Reasoning in
    begin
      length (filter ¿ P ∘ fsuc ¿¹ (L.allFin n))
    ≡˘⟨ L.length-map fsuc (filter ¿ _ ¿¹ (L.allFin n)) ⟩
      length (map fsuc $ filter ¿ P ∘ fsuc ¿¹ $ L.tabulate id)
    ≡˘⟨ cong length $ filter-map {P = P} fsuc (L.tabulate id) ⟩
      length (filter ¿ P ¿¹ $ map fsuc $ L.tabulate id)
    ≡⟨ (cong (length ∘ filter ¿ P ¿¹) $ L.map-tabulate id fsuc) ⟩
      length (filter ¿ P ¿¹ $ L.tabulate (fsuc ∘ id))
    ∎

pweaken : ∀ {n} {P : Pred (Fin n) ℓ} ⦃ _ : P ⁇¹ ⦄
  → ∃· P
  → Fin (length $ filter ¿ P ¿¹ (L.allFin n))
pweaken {P = P} (fzero ,· p)
  rewrite dec-yes ¿ P fzero ¿ (toRelevant p) .proj₂
  = fzero
pweaken {n = suc n} {P = P} (fsuc fn ,· p)
  with f′ ← subst Fin (len≡ {P = P})
          $ pweaken {n = n} {P = P ∘ fsuc} (fn ,· p)
  with ¿ P fzero ¿
... | no  _ = f′
... | yes _ = fsuc f′

pweaken-injective : ∀ {n} {P : Pred (Fin n) ℓ} ⦃ _ : P ⁇¹ ⦄
  → {∃p ∃p′ : ∃· P}
  → pweaken ∃p ≡ pweaken ∃p′
  → ∃p .fst ≡ ∃p′ .fst
pweaken-injective {P = P} {fzero ,· p} {fzero ,· p′} eq
  rewrite dec-yes ¿ P fzero ¿ (toRelevant p) .proj₂
  = refl
pweaken-injective {P = P} {fzero ,· p} {fsuc fn′ ,· p′} eq
  rewrite dec-yes ¿ P fzero ¿ (toRelevant p) .proj₂
  = case eq of λ ()
pweaken-injective {P = P} {fsuc fn ,· p} {fzero ,· p′} eq
  rewrite dec-yes ¿ P fzero ¿ (toRelevant p′) .proj₂
  = case eq of λ ()
pweaken-injective {n = suc n} {P = P} {fsuc fn ,· p} {fsuc fn′ ,· p′} eq
  with ¿ P fzero ¿
... | no _
  = cong fsuc
  $ pweaken-injective
  $ Eq.subst-injective (len≡ {P = P}) eq
... | yes _
  = cong fsuc
  $ pweaken-injective
  $ Eq.subst-injective (len≡ {P = P}) (Fi.suc-injective eq)
