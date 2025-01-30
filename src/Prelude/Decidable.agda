{-# OPTIONS --safe #-}
module Prelude.Decidable where

open import Prelude.Init

record _⁇ (P : Type ℓ) : Type ℓ where
  constructor ⁇_
  field dec : Dec P

  auto : ⦃ True dec ⦄ → P
  auto ⦃ pr ⦄ = toWitness pr

  contradict : ∀ {X : Type} {pr : False dec} → P → X
  contradict {pr = pr} = ⊥-elim ∘ toWitnessFalse pr

  contra : ¬ ¬ P → P
  contra ¬¬p with dec
  ... | yes p = p
  ... | no ¬p = ⊥-elim $ ¬¬p ¬p

  toRelevant = recompute dec

open _⁇ ⦃ ... ⦄ public

¿_¿ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Dec X
¿ _ ¿ = dec

¿_¿ᵇ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Bool
¿ X ¿ᵇ = ⌊ ¿ X ¿ ⌋

_⁇¹ : ∀ {A : Type ℓ} → (P : Pred A ℓ′) → Type (ℓ ⊔ₗ ℓ′)
P ⁇¹ = ∀ {x} → P x ⁇

dec¹ : ∀ {A : Type ℓ} {P : Pred A ℓ′} → ⦃ P ⁇¹ ⦄ → Decidable¹ P
dec¹ _ = dec

¿_¿¹ : ∀ {A : Type ℓ} (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → Decidable¹ P
¿ _ ¿¹ = dec¹

_⁇² : ∀ {A B : Type ℓ} → (P : REL A B ℓ′) → Type (ℓ ⊔ₗ ℓ′)
_~_ ⁇² = ∀ {x y} → (x ~ y) ⁇

dec² : ∀ {A B : Type ℓ} {_~_ : REL A B ℓ′} → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
dec² _ _ = dec

¿_¿² : ∀ {A B : Type ℓ} (_~_ : REL A B ℓ′) → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
¿ _ ¿² = dec²

infix -100 auto∶_
auto∶_ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Type
auto∶_ A = True ¿ A ¿

dec-✓ : ∀ {P : Type ℓ}  ⦃ _ : P ⁇ ⦄ (p : P) → ∃ λ p′ → (¿ P ¿ ≡ yes p′)
dec-✓ {P = P} p = dec-yes ¿ P ¿ p

-- ** instances

private variable A : Type ℓ; B : Type ℓ′
instance
  Dec-⊥ : ⊥ ⁇
  Dec-⊥ .dec = no λ()

  Dec-⊤ : ⊤ ⁇
  Dec-⊤ .dec = yes tt

  Dec-T : T ⁇¹
  Dec-T {false} .dec = no λ ()
  Dec-T {true}  .dec = yes tt

module _ ⦃ _ : A ⁇ ⦄ ⦃ _ : B ⁇ ⦄ where instance
  Dec-→ : (A → B) ⁇
  Dec-→ .dec = dec →-dec dec
    where open import Relation.Nullary

  Dec-× : (A × B) ⁇
  Dec-× .dec = dec ×-dec dec
    where open import Relation.Nullary

  Dec-⊎ : (A ⊎ B) ⁇
  Dec-⊎ .dec = dec ⊎-dec dec
    where open import Relation.Nullary

module _ {P : Pred A ℓ} ⦃ _ : P ⁇¹ ⦄ where instance
  Dec-Any : L.Any.Any P ⁇¹
  Dec-Any .dec = L.Any.any? dec¹ _

  Dec-All : L.All.All P ⁇¹
  Dec-All .dec = L.All.all? dec¹ _

  Dec-MAny : M.Any.Any P ⁇¹
  Dec-MAny .dec = M.Any.dec dec¹ _

  Dec-MAll : M.All.All P ⁇¹
  Dec-MAll .dec = M.All.dec dec¹ _

instance
  open import Data.Nat using (_≤_; _≤?_)
  Dec-≤ : _≤_ ⁇²
  Dec-≤ .dec = _ ≤? _


infix 4 _⊆ˢ′_
record _⊆ˢ′_ {A : Type ℓ}(xs ys : List A) : Type ℓ where
  constructor mk⊆
  field unmk⊆ : xs ⊆ˢ ys
open _⊆ˢ′_ public


open import Prelude.DecEq
module _ ⦃ _ : DecEq A ⦄ where instance
  DecEq⇒Dec : _≡_ {A = A} ⁇²
  DecEq⇒Dec .dec = _ ≟ _

  DecEq⇒Dec-Unique : Unique {A = A} ⁇¹
  DecEq⇒Dec-Unique .dec = L.AP.allPairs? dec² _

  DecEq⇒Dec-⊆ˢ : _⊆ˢ_ {A = A} ⁇²
  DecEq⇒Dec-⊆ˢ {x = []}     {y = ys} .dec = yes λ ()
  DecEq⇒Dec-⊆ˢ {x = x ∷ xs} {y = ys} .dec = case x ∈? ys of λ where
    (no  x∉ys) → no λ xs⊆ys → x∉ys (xs⊆ys (here refl))
    (yes x∈ys) → case ¿ xs ⊆ˢ ys ¿ of λ where
      (no  xs⊈ys) → no λ xs⊆ys → xs⊈ys (λ {x} z → xs⊆ys (there z))
      (yes xs⊆ys) → yes λ{ (here refl) → x∈ys
                         ; (there x∈)  → xs⊆ys x∈ }

  Dec-⊆′ : _⊆ˢ′_ {A = A} ⁇²
  Dec-⊆′ {x = xs}{ys} .dec
    with ¿ xs ⊆ˢ ys ¿
  ... | yes p = yes $ mk⊆ p
  ... | no ¬p = no  $ ⊥-elim ∘ ¬p ∘ unmk⊆
