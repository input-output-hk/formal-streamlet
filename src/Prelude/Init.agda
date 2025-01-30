{-# OPTIONS --safe #-}
module Prelude.Init where

open import Agda.Primitive public
  using ()
  renaming (Set to Type; Setω to Typeω)
open import Level public
  using (Level; 0ℓ; Setω)
  renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
1ℓ = lsuc 0ℓ; 2ℓ = lsuc 1ℓ; 3ℓ = lsuc 2ℓ; 4ℓ = lsuc 3ℓ
variable ℓ ℓ′ ℓ″ ℓ‴ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

open import Function public
  using (_∋_; _∘_; _∘′_; _∘₂_; _$_; _$′_; flip; it; id; _on_; const; case_of_)
open import Function.Definitions public
  using (Injective)
open import Function.Bundles public
  using (Inverse)

open import Data.Empty public
  using (⊥; ⊥-elim)
open import Data.Unit public
  using (⊤; tt)
open import Data.Bool public
  using (Bool; true; false; T; not; _∧_; _∨_; if_then_else_)
open import Data.Product public
  using ( _×_; _,_; _,′_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax; -,_
        ; map₁; map₂; map₂′; curry; uncurry )
open import Data.Sum public
  using (_⊎_; inj₁; inj₂)
module Bin where
  open import Data.Nat.Binary public
  open import Data.Nat.Binary.Properties public
open Bin public
  using () renaming (ℕᵇ to Bitstring)

module Ch where
  open import Data.Char public
  open import Data.Char.Properties public
open Ch public
  using (Char)
module Str where
  open import Data.String public
  open import Data.String.Properties public
open Str public
  using (String)

module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public
  open import Data.Nat.DivMod public
  open import Data.Nat.Induction public
open Nat public
  using ( ℕ; zero; suc; _+_; _∸_; _*_; _/_
        ; _≤_; _<_; _≥_; _>_; _≤ᵇ_; _<ᵇ_
        ; _≰_; _≮_; _≱_; _≯_
        )

module Prod where
  open import Data.Product public
  open import Data.Product.Properties public
module Sum where
  open import Data.Sum public
  open import Data.Sum.Properties public

module Fi where
  open import Data.Fin public
  open import Data.Fin.Properties public
open Fi public
  using (Fin; fromℕ<)
  renaming (zero to fzero; suc to fsuc)

module Fl where
  open import Data.Float public
  open import Data.Float.Properties public
open Fl public
  using (Float)

module Int where
  open import Data.Integer public
  open import Data.Integer.Properties public
open Int public
  using (ℤ)

module M where
  open import Data.Maybe public
  open import Data.Maybe.Properties public
  module Any where
    open import Data.Maybe.Relation.Unary.Any public
  module All where
    open import Data.Maybe.Relation.Unary.All public
    open import Data.Maybe.Relation.Unary.All.Properties public
open import Data.Maybe public
  using ( Maybe; just; nothing; maybe; fromMaybe; is-just; is-nothing
        ; decToMaybe; boolToMaybe )
  renaming (map to mapMaybe)
open M.Any public
  using (just)
open M.All public
  using (just; nothing)

module V where
  open import Data.Vec public
  open import Data.Vec.Properties public
  module All where
    open import Data.Vec.Relation.Unary.All public
    open import Data.Vec.Relation.Unary.All.Properties public
  module Any where
    open import Data.Vec.Relation.Unary.Any public
    open import Data.Vec.Relation.Unary.Any.Properties public
open V public
  using (Vec; []; _∷_)

module L where
  open import Data.List public
  open import Data.List.Properties public
  module All where
    open import Data.List.Relation.Unary.All public
    open import Data.List.Relation.Unary.All.Properties public
  module Any where
    open import Data.List.Relation.Unary.Any public
    open import Data.List.Relation.Unary.Any.Properties public
  module Mem where
    open import Data.List.Membership.Propositional public
    open import Data.List.Membership.Propositional.Properties public
  module First where
    open import Data.List.Relation.Unary.First public
    open import Data.List.Relation.Unary.First.Properties public
  module NE where
    open import Data.List.NonEmpty public
    open import Data.List.NonEmpty.Properties public
  module AP where
    open import Data.List.Relation.Unary.AllPairs public
    open import Data.List.Relation.Unary.AllPairs.Properties public
  module Unique where
    open import Data.List.Relation.Unary.Unique.Propositional public
    open import Data.List.Relation.Unary.Unique.Propositional.Properties public
  module SubL where
    open import Data.List.Relation.Binary.Sublist.Propositional public
    open import Data.List.Relation.Binary.Sublist.Propositional.Properties public
  module SubS where
    open import Data.List.Relation.Binary.Subset.Propositional public
    open import Data.List.Relation.Binary.Subset.Propositional.Properties public
  module Pre where
    open import Data.List.Relation.Binary.Prefix.Heterogeneous public
    open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties public
    open import Data.List.Relation.Binary.Prefix.Homogeneous.Properties public
  module Suf where
    open import Data.List.Relation.Binary.Suffix.Heterogeneous public
    open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties public
    open import Data.List.Relation.Binary.Suffix.Homogeneous.Properties public
  module PW where
    open import Data.List.Relation.Binary.Pointwise public
    open import Data.List.Relation.Binary.Pointwise.Properties public
  module Ex where
    open import Data.List.Extrema.Nat public
  module Eff where
    open import Data.List.Effectful public
open L public
  using (List; []; _∷_; _++_; map; filter; length; sum; and; or; _[_]∷=_)
open L.NE public
  using (List⁺; _∷_; _∷⁺_)
open L.All public
  using ([]; _∷_)
open L.Any public
  using (here; there; _─_)
open L.First public
  using (First; _∷_)
open L.Mem public
  using (_∈_; _∉_)
open L.AP public
  using (AllPairs; []; _∷_)
open L.Unique public
  using (Unique)
open L.SubL public
  using (_⊆_; []; _∷ʳ_; _∷_)
open L.SubS public
  using ()
  renaming (_⊆_ to _⊆ˢ_)
open L.Pre public
  using (Prefix; []; _∷_)
open L.Suf public
  using (Suffix; here; there)
open L.PW public
  using (Pointwise; []; _∷_)

open import Relation.Nullary public
  using (¬_; ¬?; Dec; yes; no; Irrelevant; recompute)
open import Relation.Nullary.Decidable public
  using ( ⌊_⌋; True; False; toWitness; toWitnessFalse; fromWitness
        ; dec-yes; dec-no; dec-true; dec-false; dec-yes-irr; _×-dec_ )
  renaming (map′ to mapDec)
open import Relation.Unary public
  using (Pred; _≐_; ∁)
  renaming ( Decidable to Decidable¹; Irrelevant to Irrelevant¹
           ; _⊆_ to _⊆¹_; _∩_ to _∩¹_ )
open import Relation.Binary public
  using (Rel; REL; DecidableEquality; Transitive)
  renaming (Decidable to Decidable²; Irrelevant to Irrelevant²)
module Eq where
  open import Relation.Binary.PropositionalEquality public
open Eq public
  using (_≡_; _≢_; refl; _≗_; trans; cong; cong₂; subst; sym; module ≡-Reasoning)

module _ {a b} {A : Type a} {B : Type b} where
  Injective≡ : (A → B) → Set _
  Injective≡ f = Injective {A = A} {B = B} _≡_ _≡_ f

open import Algebra.Core public
  using (Op₁; Op₂)

module Eff where
  open import Effect.Monad public

-- ** extras

-- uniquely exists
∃! : {A : Type ℓ} → Pred A ℓ′ → Type _
∃! = P.∃! _≡_
  where import Data.Product as P

-- refinement types (i.e. product with erased second component)
record ∃· {A : Type ℓ} (P : Pred A ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  constructor _,·_
  field
    fst  : A
    .snd : P fst
open ∃· public

-- iff
_↔_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ₗ ℓ′)
A ↔ B = (A → B) × (B → A)

-- singleton types
data Is {A : Type ℓ} : A → Type ℓ where
  ⟫_ : (x : A) → Is x
infix -100 ⟫_

-- get the type of a given term
typeOf : ∀ {A : Type ℓ} → (a : A) → Type ℓ
typeOf {A = A} _ = A

-- sums
private variable A B : Type ℓ

noInj₁ : ¬ A → A ⊎ B → B
noInj₁ ¬a = λ where
  (inj₁ a) → ⊥-elim $ ¬a a
  (inj₂ b) → b

noInj₂ : ¬ B → A ⊎ B → A
noInj₂ ¬b = λ where
  (inj₁ a) → a
  (inj₂ b) → ⊥-elim $ ¬b b

-- maybes
MAll⇒Any : ∀ {P : A → Type} (mx : Maybe A)
  → M.Is-just mx
  → M.All.All P mx
  → M.Any.Any P mx
MAll⇒Any (just x) (just tt) (just px) = just px

MAll-× : ∀ {P Q : A → Type} (mx : Maybe A)
  → M.All.All P mx
  → M.All.All Q mx
  → M.All.All (P ∩¹ Q) mx
MAll-× .nothing  nothing  nothing = nothing
MAll-× .(just _) (just p) (just q) = just (p , q)
