module Protocol.Streamlet.Test where

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

open Assumptions ⋯

open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Decidability ⋯

{-
       (b₂)     (b₅)     (b₆)       (b₇)
    ↙ epoch2 ← epoch5 ← epoch6 ⦊ ← epoch7 ✓
⦉ ⊥
    ↖
      epoch1 ← epoch3 ← epoch? ×
       (b₁)     (b₃)
-}
b₁ b₂ b₃ b₅ b₆ b₇ : Block
b₁ = ⟨ genesisChain     ♯ , 1 , [] ⟩
b₂ = ⟨ genesisChain     ♯ , 2 , [] ⟩
b₃ = ⟨ [ b₁ ]           ♯ , 3 , [] ⟩
b₅ = ⟨ [ b₂ ]           ♯ , 5 , [] ⟩
b₆ = ⟨ [ b₅ ⨾ b₂ ]      ♯ , 6 , [] ⟩
b₇ = ⟨ [ b₆ ⨾ b₅ ⨾ b₂ ] ♯ , 7 , [] ⟩

_ = (b₁ ♯) ≡ 1
  ∋ refl
_ = (b₂ ♯) ≡ 2
  ∋ refl
_ = (b₃ ♯) ≡ 4
  ∋ refl
_ = (b₅ ♯) ≡ 7
  ∋ refl
_ = (b₆ ♯) ≡ 15
  ∋ refl
_ = (b₇ ♯) ≡ 31
  ∋ refl

{-
---------------- *start*
Propose 𝕃 b₁
ReceiveMessage 𝔹
Vote 𝔹 b₁
---------------- *b₁ has been notarized*
Propose 𝕃 b₂
ReceiveMessage 𝔸
Vote 𝔸 b₂
---------------- *b₂ has been notarized*
Propose 𝕃 b₃
ReceiveMessage 𝔹
Vote 𝔹 b₃
---------------- *b₃ has been notarized*
Propose 𝕃 b₅
ReceiveMessage 𝔸
Vote 𝔸 b₅
---------------- *b₅ has been notarized*
Propose 𝕃 b₆
ReceiveMessage 𝔸
Vote 𝔸 b₆
---------------- *b₆ has been notarized*
Propose 𝕃 b₇
ReceiveMessage 𝔸
Vote 𝔸 b₇
---------------- *all blocks have been notarized*
---------------- *[ ⊥ ← b₂ ← b₅ ← b₆ ] is finalized*
---------------- *prove consistency: ∄ b at the same height as b₆. notarized(b⨾⋯)*
-}
p₁ v₁ p₂ v₂ p₃ v₃ p₅ v₅ p₆ v₆ p₇ v₇ : Message
p₁ = Propose (signBlock 𝕃 b₁)
v₁ = Vote    (signBlock 𝔹 b₁)
p₂ = Propose (signBlock 𝕃 b₂)
v₂ = Vote    (signBlock 𝔸 b₂)
p₃ = Propose (signBlock 𝕃 b₃)
v₃ = Vote    (signBlock 𝔹 b₃)
p₅ = Propose (signBlock 𝕃 b₅)
v₅ = Vote    (signBlock 𝔸 b₅)
p₆ = Propose (signBlock 𝕃 b₆)
v₆ = Vote    (signBlock 𝔸 b₆)
p₇ = Propose (signBlock 𝕃 b₇)
v₇ = Vote    (signBlock 𝔸 b₇)
-- * validity
_ = ValidChain [ b₇ ⨾ b₆ ⨾ b₅ ⨾ b₂ ]
  ∋ auto
_ = ValidChain [ b₃ ⨾ b₁ ]
  ∋ auto
_ = ¬ ValidChain [ b₂ ⨾ b₁ ]
  ∋ auto
-- * notarization
_ = NotarizedChain [ v₁ ⨾ p₁ ]
                   [ b₁ ]
  ∋ auto
_ = NotarizedChain [ p₂ ⨾ v₁ ⨾ p₁ ]
                   [ b₁ ]
  ∋ auto
_ = NotarizedChain [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
                   [ b₂ ]
  ∋ auto
_ = NotarizedChain [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
                   [ b₃ ⨾ b₁ ]
  ∋ auto
_ = ¬ NotarizedChain [ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
                     [ b₅ ⨾ b₂ ]
  ∋ auto
_ = NotarizedChain [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
                   [ b₅ ⨾ b₂ ]
  ∋ auto
_ = NotarizedChain [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
                   [ b₆ ⨾ b₅ ⨾ b₂ ]
  ∋ auto
_ = NotarizedChain [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
                   [ b₇ ⨾ b₆ ⨾ b₅ ⨾ b₂ ]
  ∋ auto
-- * finalization
_ = FinalizedChain [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
                   [ b₆ ⨾ b₅ ⨾ b₂ ] b₇
  ∋ auto

-- -- * constructor sugar
-- ms∶_ : Bitmask ms → LocalState ms
-- ms∶ bs = record def
--   { received = bs }
-- ms∶_ch∶_ : Bitmask ms → Chain → LocalState ms
-- ms∶ bs ch∶ ch = record
--   { received = bs
--   ; final    = ch }

-- * example trace
-- open import Prelude.Closures _—→_
_ =
  begin
    record
    { e-now         = 1
    ; history       = []
    ; networkBuffer = []
    ; stateMap      = initStateMap
    }
  —→⟨ Propose? _ genesisChain [] ⟩
    record
    { e-now         = 1
    ; history       = [ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₁ ⟩ ⨾ [ 𝔹 ∣ p₁ ⟩ ]
    ; stateMap      = [  {- 𝕃 -} ⦅ Voted , [ p₁ ] , [] , [] ⦆
                      ⨾  {- 𝔸 -} def
                      ⨾  {- 𝔹 -} def
                      ]}
  —→⟨ Drop? [ 𝔸 ∣ p₁ ⟩ ⟩
    record
    { e-now         = 1
    ; history       = [ p₁ ]
    ; networkBuffer = [ 𝔹 ∣ p₁ ⟩ ∷ []
    ; stateMap      = [ ⦅ Voted , [ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ def
                      ]}
  —→⟨ Deliver? [ 𝔹 ∣ p₁ ⟩ ⟩
    record
    { e-now         = 1
    ; history       = [ p₁ ]
    ; networkBuffer = []
    ; stateMap      = [ ⦅ Voted , [ p₁ ] , [] , [] ⦆
                      ⨾  ⦅ Ready , [] , [] , [] ⦆
                      ⨾  ⦅ Ready , [] , [ p₁ ] , [] ⦆
                      ]}
  —→⟨ Vote? 𝔹 genesisChain [] ⟩
    record
    { e-now         = 1
    ; history       = [ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ v₁ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Drop? [ 𝔸 ∣ v₁ ⟩ ⟩
    record
    { e-now         = 1
    ; history       = [ v₁ ⨾ p₁ ]
    ; networkBuffer = [  [ 𝕃 ∣ v₁ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ AdvanceEpoch ⟩
    record
    { e-now         = 2
    ; history       = [ v₁ ⨾ p₁ ]
    ; networkBuffer = [  [ 𝕃 ∣ v₁ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Propose? 𝕃 genesisChain [] ⟩
    record
    { e-now         = 2
    ; history       = [ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ p₂ ⟩ ⨾ [ 𝔹 ∣ p₂ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Drop? [ 𝔹 ∣ p₂ ⟩ ⟩
    record
    { e-now         = 2
    ; history       = [ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝔸 ∣ p₂ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Deliver? [ 𝔸 ∣ p₂ ⟩ ⟩
    record
    { e-now         = 2
    ; history       = [ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [  [ 𝕃 ∣ v₁ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ]  , [] , [] ⦆
                      ⨾ ⦅ Ready , [] , [ p₂ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Vote? 𝔸 genesisChain [] ⟩
    record
    { e-now         = 2
    ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ v₂ ⟩  ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆ ]}
  —→⟨ Drop? [ 𝔹 ∣ v₂ ⟩ ⟩
    record
    { e-now         = 2
    ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [  [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆ ]}
  —→⟨  AdvanceEpoch ⟩
    record
    { e-now         = 3
    ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₁ ⟩ ⨾ [ 𝕃 ∣ v₂ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Deliver? [ 𝕃 ∣ v₁ ⟩ ⟩
   record
   { e-now         = 3
   ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
   ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ]
   ; stateMap      = [ ⦅ Ready , [ p₂ ⨾ p₁ ] , [ v₁ ] , [] ⦆
                     ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                     ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                     ]}
  —→⟨ Register? 𝕃 v₁ ⟩
   record
   { e-now         = 3
   ; history       = [ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
   ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ]
   ; stateMap      = [ ⦅ Ready , [ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                     ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                     ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                     ]}
  —→⟨ Propose? 𝕃 [ b₁ ] [] ⟩
    record
    { e-now         = 3
    ; history       = [ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔸 ∣ p₃ ⟩ ⨾ [ 𝔹 ∣ p₃ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Drop? [ 𝔸 ∣ p₃ ⟩ ⟩
    record
    { e-now         = 3
    ; history       = [ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝔹 ∣ p₃ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Deliver? [ 𝔹 ∣ p₃ ⟩ ⟩
    record
    { e-now         = 3
    ; history       = [ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₁ ⨾ p₁ ] , [ p₃ ] , [] ⦆
                      ]}
  —→⟨ Vote? 𝔹 [ b₁ ] [] ⟩
    record
    { e-now         = 3
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Drop? [ 𝔸 ∣ v₃ ⟩ ⟩
    record
    { e-now         = 3
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ AdvanceEpoch ⟩
    record
    { e-now         = 4
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ AdvanceEpoch ⟩
    record
    { e-now         = 5
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₂ ⟩ ⨾ [ 𝕃 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Deliver? [ 𝕃 ∣ v₂ ⟩ ⟩
    record
    { e-now         = 5
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₂ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Register? 𝕃 v₂ ⟩
    record
    { e-now         = 5
    ; history       = [ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Propose? 𝕃 [ b₂ ] [] ⟩
    record
    { e-now         = 5
    ; history       = [ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔸 ∣ p₅ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Deliver? [ 𝔸 ∣ p₅ ⟩ ⟩
    record
    { e-now         = 5
    ; history       = [ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₂ ⨾ p₂ ] , [ p₅ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Vote? 𝔸 [ b₂ ] [] ⟩
    record
    { e-now         = 5
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝕃 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Voted , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Voted , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ AdvanceEpoch ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝔹 ∣ p₅ ⟩ ⨾ [ 𝕃 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Drop? [ 𝔹 ∣ p₅ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝕃 ∣ v₅ ⟩ ⨾ [ 𝔹 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Drop? [ 𝔹 ∣ v₅ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₃ ⟩ ⨾ [ 𝕃 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Deliver? [ 𝕃 ∣ v₃ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝕃 ∣ v₅ ⟩ ]
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₃ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Deliver? [ 𝕃 ∣ v₅ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = []
    ; stateMap      = [ ⦅ Ready , [ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₃ ⨾ v₅ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Register? 𝕃 v₃ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = []
    ; stateMap      = [ ⦅ Ready , [ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₅ ] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Register? 𝕃 v₅ ⟩
    record
    { e-now         = 6
    ; history       = [ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = []
    ; stateMap      = [ ⦅ Ready , [ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
                      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
                      ]}
  —→⟨ Propose? 𝕃 [ b₅ ⨾ b₂ ] [] ⟩
    record
    { e-now         = 6
    ; history       = [ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔸 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ p₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Deliver? [ 𝔸 ∣ p₆ ⟩ ⟩
    record
    { e-now         = 6
    ; history       = [ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔹 ∣ p₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [ p₆ ] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Vote? 𝔸 [ b₅ ⨾ b₂ ] [] ⟩
    record
    { e-now         = 6
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝕃 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Voted , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ AdvanceEpoch ⟩
    record
    { e-now         = 7
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝕃 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Ready , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Deliver? [ 𝕃 ∣ v₆ ⟩ ⟩
    record
    { e-now         = 7
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Ready , [ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [ v₆ ] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Register? 𝕃 v₆ ⟩
    record
    { e-now         = 7
    ; history       = [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ]
    ; stateMap      =
      [ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Propose? 𝕃 [ b₆ ⨾ b₅ ⨾ b₂ ] [] ⟩
    record
    { e-now         = 7
    ; history       = [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ⨾ [ 𝔸 ∣ p₇ ⟩ ⨾ [ 𝔹 ∣ p₇ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Deliver? [ 𝔸 ∣ p₇ ⟩ ⟩
    record
    { e-now         = 7
    ; history       = [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer = [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ p₇ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [ p₇ ] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Vote? 𝔸 [ b₆ ⨾ b₅ ⨾ b₂ ] [] ⟩
    record
    { e-now         = 7
    ; history       = [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer =
      [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ p₇ ⟩ ⨾ [ 𝕃 ∣ v₇ ⟩ ⨾ [ 𝔹 ∣ v₇ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Voted , [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  —→⟨ Finalize? 𝔸 [ b₆ ⨾ b₅ ⨾ b₂ ] b₇ ⟩
    record
    { e-now         = 7
    ; history       = [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₃ ⨾ p₃ ⨾ v₂ ⨾ p₂ ⨾ v₁ ⨾ p₁ ]
    ; networkBuffer =
      [ [ 𝔹 ∣ p₆ ⟩ ⨾ [ 𝔹 ∣ v₆ ⟩ ⨾ [ 𝔹 ∣ p₇ ⟩ ⨾ [ 𝕃 ∣ v₇ ⟩ ⨾ [ 𝔹 ∣ v₇ ⟩ ]
    ; stateMap      =
      [ ⦅ Voted , [ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ v₃ ⨾ p₅ ⨾ v₂ ⨾ p₃ ⨾ v₁ ⨾ p₂ ⨾ p₁ ] , [] , [] ⦆
      ⨾ ⦅ Voted , [ v₇ ⨾ p₇ ⨾ v₆ ⨾ p₆ ⨾ v₅ ⨾ p₅ ⨾ v₂ ⨾ p₂ ] , [] , [ b₆ ⨾ b₅ ⨾ b₂ ] ⦆
      ⨾ ⦅ Ready , [ v₃ ⨾ p₃ ⨾ v₁ ⨾ p₁ ] , [] , [] ⦆
      ]}
  ∎
