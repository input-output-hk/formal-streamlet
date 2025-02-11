module Protocol.Streamlet.Test.LocalState where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core
open import Protocol.Streamlet.Block ⋯
open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.Chain ⋯
open import Protocol.Streamlet.Local.State ⋯

instance
  NotarizedBlock-dec : NotarizedBlock ⁇²
  NotarizedBlock-dec {ms}{b} .dec with dec
  ... | yes p = yes (record { enoughVotes = p  })
  ... | no ¬p = no λ nb → ¬p (nb .enoughVotes)

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
