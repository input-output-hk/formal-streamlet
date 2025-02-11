module Protocol.Streamlet.Test.Chain where

open import Prelude
open import Hash

open import Protocol.Streamlet.Test.Core
  hiding (Dec-connects)

instance
  Dec-connects : _-connects-to-_ ⁇²
  Dec-connects .dec with dec | dec
  ... | yes p | yes q = yes (connects∶ p q)
  ... | no ¬p | _     = no λ where (connects∶ p _) → ¬p p
  ... | _     | no ¬q = no λ where (connects∶ _ q) → ¬q q

CH : Chain
CH = [ ⟨ genesisChain ♯ , 41 , [] ⟩ ]

testF = ¿ ⟨ CH ♯ , 40 , [] ⟩ -connects-to- CH ¿ᵇ
testT = ¿ ⟨ CH ♯ , 42 , [] ⟩ -connects-to- CH ¿ᵇ

test : Bool
test = (testF == false) ∧ (testT == true)
{-# COMPILE AGDA2LAMBOX test #-}

_ : test ≡ true
_ = refl
