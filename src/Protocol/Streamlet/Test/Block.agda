module Protocol.Streamlet.Test.Block where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core

B B′ : Block
B  = ⟨ genesisChain ♯ , 42 , [] ⟩
B′ = ⟨ (Chain ∋ []) ♯ , 21 + 21 , [] ⟩

test : Bool
test = B == B′
{-# COMPILE AGDA2LAMBOX test #-}

_ : test ≡ true
_ = refl
