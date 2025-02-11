module Protocol.Streamlet.Test.LocalState2 where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core

B : Block
B = ⟨ genesisChain ♯ , 42 , [] ⟩

testF testT : Bool
testF = ¿ NotarizedBlock [ Vote (signBlock 𝕃 B) ] B ¿ᵇ
testT = ¿ NotarizedBlock [ Vote (signBlock 𝕃 B) ⨾ Vote (signBlock 𝔸 B) ] B ¿ᵇ

test : Bool
test = (testF == false) ∧ (testT == true)
{-# COMPILE AGDA2LAMBOX test #-}

_ : test ≡ true
_ = refl
