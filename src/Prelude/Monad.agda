{-# OPTIONS --safe #-}
module Prelude.Monad where

open import Prelude.Init

private variable x y : Type

record Monad (M : Type → Type ℓ′) : Set (1ℓ ⊔ₗ ℓ′) where
  field
    _>>=_ : M x -> (x -> M y) -> M y
    return : x -> M x

  _>>_ : M x -> M y -> M y
  m >> m' = m >>= λ _ -> m'

  when : Bool -> M ⊤ -> M ⊤
  when cond act =
      if cond
      then act >> return _
      else return _

open Monad ⦃...⦄ public

instance
  Monad-List : Monad List
  Monad-List = record {Eff.RawMonad L.Eff.monad}
