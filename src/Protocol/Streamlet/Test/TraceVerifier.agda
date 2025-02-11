module Protocol.Streamlet.Test.TraceVerifier where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core
open import Protocol.Streamlet.TraceVerifier ⋯
open import Protocol.Streamlet.Test.ExampleTrace

trace : Actions
trace = L.reverse $
  [ Propose 𝕃 genesisChain []
  ⨾ Deliver 1 -- [ 𝔹 ∣ p₁ ⟩
  ⨾ Vote 𝔹 genesisChain []
  ⨾ AdvanceEpoch
  ⨾ Propose 𝕃 genesisChain []
  ⨾ Deliver 3 -- [ 𝔸 ∣ p₂ ⟩
  ⨾ Vote 𝔸 genesisChain []
  ⨾ AdvanceEpoch
  ⨾ Deliver 1 -- [ 𝕃 ∣ v₁ ⟩
  ⨾ RegisterVote 𝕃 0 -- v₁
  ⨾ Propose 𝕃 [ b₁ ] []
  ⨾ Deliver 6 -- [ 𝔹 ∣ p₃ ⟩
  ] ++
  [ Vote 𝔹 [ b₁ ] []
  ⨾ AdvanceEpoch
  ⨾ AdvanceEpoch
  ⨾ Deliver 3 -- [ 𝕃 ∣ v₂ ⟩
  ⨾ RegisterVote 𝕃 0 -- v₂
  ⨾ Propose 𝕃 [ b₂ ] []
  ⨾ Deliver 7 -- [ 𝔸 ∣ p₅ ⟩
  ⨾ Vote 𝔸 [ b₂ ] []
  ⨾ AdvanceEpoch
  ⨾ Deliver 5 -- [ 𝕃 ∣ v₃ ⟩
  ⨾ Deliver 7 -- [ 𝕃 ∣ v₅ ⟩
  ] ++
  [ RegisterVote 𝕃 0 -- v₃
  ⨾ RegisterVote 𝕃 0 -- v₅
  ⨾ Propose 𝕃 [ b₅ ⨾ b₂ ] []
  ⨾ Deliver 8 -- [ 𝔸 ∣ p₆ ⟩
  ⨾ Vote 𝔸 [ b₅ ⨾ b₂ ] []
  ⨾ AdvanceEpoch
  ⨾ Deliver 9 -- [ 𝕃 ∣ v₆ ⟩
  ⨾ RegisterVote 𝕃 0 -- v₆
  ⨾ Propose 𝕃 [ b₆ ⨾ b₅ ⨾ b₂ ] []
  ⨾ Deliver 10 -- [ 𝔸 ∣ p₇ ⟩
  ⨾ Vote 𝔸 [ b₆ ⨾ b₅ ⨾ b₂ ] []
  ⨾ FinalizeBlock 𝔸 [ b₆ ⨾ b₅ ⨾ b₂ ] b₇
  ]

test : Bool
test = ¿ ValidTrace trace ¿ᵇ
-- {-# COMPILE AGDA2LAMBOX test #-}

_ : test ≡ true
_ = refl
