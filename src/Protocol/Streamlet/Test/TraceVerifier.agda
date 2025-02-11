module Protocol.Streamlet.Test.TraceVerifier where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core
open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Decidability ⋯
open import Protocol.Streamlet.TraceVerifier ⋯

b₁ : Block
b₁ = ⟨ genesisChain ♯ , 1 , [] ⟩

p₁ : Message
p₁ = Propose (signBlock 𝕃 b₁)

trace : Actions
trace =
  [ Vote 𝔹 genesisChain []
  ⨾ Deliver 0 {-[ 𝔹 ∣ p₁ ⟩-}
  ⨾ Drop 0 {-[ 𝔸 ∣ p₁ ⟩-}
  ⨾ Propose 𝕃 genesisChain []
  ]

test : Bool
test = ¿ ValidTrace trace ¿ᵇ
{-# COMPILE AGDA2LAMBOX test #-}

_ : test ≡ true
_ = refl
