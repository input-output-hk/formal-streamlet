{-# OPTIONS --safe #-}
module Prelude where

-- gather common definition from https://github.com/agda/agda-stdlib
open import Prelude.Init public

-- ported from https://github.com/omelkonian/agda-stdlib-classes
open import Prelude.DecEq public
open import Prelude.Decidable public
open import Prelude.Monoid public
open import Prelude.Monad public

-- ported from https://github.com/omelkonian/formal-prelude
open import Prelude.LiteralSequences public
open import Prelude.InferenceRules public
open import Prelude.Allable public
open import Prelude.Anyable public
open import Prelude.Irrelevance public
open import Prelude.Default public
open import Prelude.FromNat public
open import Prelude.Initial public
open import Prelude.Closures
open import Prelude.Lists public
open import Prelude.Bitmasks public

-- ported from https://github.com/IntersectMBO/formal-ledger-specifications
open import Prelude.STS public

-- ported from https://stackoverflow.com/a/58709254
open import Prelude.AssocList public

-- extra stuff (import manually)
open import Prelude.PFin
open import Prelude.PVec
