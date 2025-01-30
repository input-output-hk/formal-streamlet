{-# OPTIONS --safe #-}
module Prelude.Membership where

open import Prelude.Init

record Has∈ (F : Type → Type) (A B : Type) : Type₁ where
    field _∙∈_ : A → F B → Type
    infix 100 _∙∈_
open Has∈ ⦃...⦄ public

instance
  Has∈-List : ∀ {A} → Has∈ List A A
  Has∈-List ._∙∈_ = _∈_

  Has∈-List⁺ : ∀ {A} → Has∈ List⁺ A A
  Has∈-List⁺ ._∙∈_ x xs = x ∈ L.NE.toList xs
