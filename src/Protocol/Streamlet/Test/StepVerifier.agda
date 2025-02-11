module Protocol.Streamlet.Test.StepVerifier where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core
open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Decidability ⋯
open import Protocol.Streamlet.StepVerifier ⋯

b₁ : Block
b₁ = ⟨ genesisChain ♯ , 1 , [] ⟩

p₁ : Message
p₁ = Propose (signBlock 𝕃 b₁)

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
