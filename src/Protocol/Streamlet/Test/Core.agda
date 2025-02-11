module Protocol.Streamlet.Test.Core where

open import Prelude
open import Hash
open import DummyHashing
open import Protocol.Streamlet.Assumptions

pattern 𝕃 = fzero
pattern 𝔸 = fsuc fzero
pattern 𝔹 = fsuc (fsuc fzero)

⋯ : Assumptions
⋯ = record {go; honest-majority = auto; Honest-irr = λ _ _ → refl} where module go where

  hashes = DummyHashing
  open HashAssumptions hashes

  signatures = DummySigning (λ _ _ _ → true)
  open SignatureAssumptions signatures

  nodes       = 3
  nodes⁺      = Nat.s≤s Nat.z≤n
  epochLeader = const 𝕃
  Honest      = const ⊤
  Dec-Honest  = ⁇ dec

  Transaction = ⊤
  DecEq-Tx    = DecEq    Transaction ∋ it
  Hashable-Tx = Hashable Transaction ∋ it

  keys : Fin nodes → KeyPair
  keys = λ where
    𝕃 → mk-keyPair (fromℕ 0) (fromℕ 0)
    𝔸 → mk-keyPair (fromℕ 1) (fromℕ 1)
    𝔹 → mk-keyPair (fromℕ 2) (fromℕ 2)

open Assumptions ⋯ public
