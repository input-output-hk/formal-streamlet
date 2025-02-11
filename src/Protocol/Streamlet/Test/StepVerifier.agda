module Protocol.Streamlet.Test.StepVerifier where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core
open import Protocol.Streamlet.StepVerifier ⋯
open import Protocol.Streamlet.Test.ExampleTrace

test : Bool
test = canVote 𝔹 genesisChain [] (b₁ .parentHash) $
  record
    { e-now         = 1
    ; history       = [ p₁ ]
    ; networkBuffer = []
    ; stateMap      = [ ⦅ Voted , [ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [ p₁ ] , [] ⦆
                      ]}
{-# COMPILE AGDA2LAMBOX test #-}

_ : test ≡ true
_ = refl
