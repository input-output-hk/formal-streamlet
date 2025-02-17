
# Streamlet Protocol Description

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Global.Step (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯
open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.Chain ⋯
open import Protocol.Streamlet.Local.State ⋯
open import Protocol.Streamlet.Local.Step ⋯
open import Protocol.Streamlet.Global.State ⋯
```
-->

## Sending messages

```agda
updateLocal : ∀ p ⦃ _ : Honest p ⦄ → LocalState → Op₁ GlobalState
updateLocal p ls s = record s
  { stateMap = s .stateMap [ p ,· it ]≔ ls }

module _
  (s : GlobalState) {env : Envelope}
  (let [ p ∣ m ⟩ = env)
  (env∈ : env ∈ s .networkBuffer) (let envⁱ = L.Any.index env∈) where

  deliverMsg dropMsg : GlobalState
  deliverMsg = record s
    { stateMap      = s .stateMap [ p ]%= receiveMessage m
    ; networkBuffer = L.removeAt (s .networkBuffer) envⁱ
    }
  dropMsg = record s
    { networkBuffer = L.removeAt (s .networkBuffer) envⁱ }

broadcast : Pid → Maybe Message → Op₁ GlobalState
broadcast _   nothing  s = s
broadcast pid (just m) s = record s
  { networkBuffer = s .networkBuffer ++ msgs
  ; history       = m ∷ s .history
  }
  where msgs = L.map [_∣ m ⟩ (filter (pid ≢?_) allPids)

advanceEpoch : Op₁ GlobalState
advanceEpoch s = record s
  { e-now    = suc (s .e-now)
  ; stateMap = V.map epochChange (s .stateMap)
  }
```

## The (global) step relation

```agda
data _—→_ (s : GlobalState) : GlobalState → Type where

   -- An *honest* node performs a local step.
  LocalStep : ⦃ _ : Honest p ⦄ →
    (p ▷ s .e-now ⊢ s ＠ p —[ mm ]→ ls′)
    ─────────────────────────────────────────
    s —→ broadcast p mm (updateLocal p ls′ s)

  -- A *dishonest* node can:
  --   - Replay a message sent previously by an honest participant.
  --   - Broadcast any message signed by a dishonest participant.
  --   - Update their local database arbitrarily.
  DishonestLocalStep :
    ∙ Dishonest p
    ∙ (Honest (m ∙pid) → m ∈ s .history)
      ───────────────────────────────────────────────
      s —→ broadcast p (just m) s

  -- * Deliver a message in the network.
  -- Since we may deliver any message on the network, this models
  -- non-determinism in the order that messages may arrive.
  Deliver :
    (env∈ : env ∈ s .networkBuffer) →
    ─────────────────────────────────
    s —→ deliverMsg s env∈

  -- * Advancing to the next epoch.
  AdvanceEpoch :
    ───────────────────
    s —→ advanceEpoch s

  -- * A message is lost in the network.
  Drop :
    (env∈ : env ∈ s .networkBuffer) →
    ─────────────────────────────────
    s —→ dropMsg s env∈
```
*Note* : We have system epoch but not local epochs.
 In a synchronous network (like the one assumed in Streamlet) only the system epoch is needed.
 If we were to assume a partially-synchronous network then we need the epoch in each local state.

<!--
```agda
broadcast[_↝_∣_⟩ : ∀ p ⦃ _ : Honest p ⦄ → LocalState → Maybe Message → Op₁ GlobalState
broadcast[ p ↝ ls′ ∣ mm ⟩ = broadcast p mm ∘ updateLocal p ls′

module ∣ProposeBlock∣ p ⦃ _ : Honest p ⦄ s ch txs where
  E   = s .e-now
  L   = E .epochLeader
  B   = let H = _♯ ⦃ Hashable-List ⦃ Hashable-Block ⦄ ⦄ ch
        in ⟨ H , E , txs ⟩
  SB  = signBlock p B
  M   = Propose SB
  ≪db = (s ＠ p) .db
module ∣VoteBlock∣ p ⦃ _ : Honest p ⦄ s (ch : Chain) txs where
  E   = s .e-now
  L   = E .epochLeader
  B   = ⟨ ch ♯ , E , txs ⟩
  SB  = signBlock p B
  SBᵖ = signBlock L B
  M   = Vote    SB
  Mᵖ  = Propose SBᵖ
  ≪db = (s ＠ p) .db
module ∣RegisterVote∣ p  ⦃ _ : Honest p ⦄ s (sb : SignedBlock) where
  E   = s .e-now
  B   = sb .block
  Eᴮ  = sb .block .epoch
  Pᴮ  = sb .node
  ≪db = (s ＠ p) .db

module ∣Base∣ p ⦃ _ : Honest p ⦄ where
  lookup✓ = pLookup-replicate p initLocalState

module ∣AdvanceEpoch∣ p ⦃ _ : Honest p ⦄ s where
  lookup✓ = pLookup-map p epochChange (s .stateMap)

module ∣Deliver∣
  p ⦃ _ : Honest p ⦄ s {env : Envelope} (let [ p′ ∣ m ⟩ = env)
  (env∈ : env ∈ s .networkBuffer) (let s′ = deliverMsg s env∈)
  where

  module _ ⦃ _ : Honest p′ ⦄ where
    lookup✓ = pLookup∘updateAt p′ {receiveMessage m} (s .stateMap)
    lookup✖ = λ (p≢ : p ≢ p′) →
      pLookup∘updateAt′ p p′ {receiveMessage m} (p≢ ∘ ↑-injective) (s .stateMap)

  db≡ : (s′ ＠ p) .db ≡ (s ＠ p) .db
  db≡
    with honest? p′
  ... | no _
    = refl
  ... | yes hp′
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ ⦃ hp′ ⦄ p≢ = refl
  ... | yes refl
    rewrite lookup✓ ⦃ it ⦄
    = refl

  ＠ph≡ : (s′ ＠ p) .phase ≡ (s ＠ p) .phase
  ＠ph≡
    with honest? p′
  ... | no _ = refl
  ... | yes hp′
    with p ≟ p′
  ... | no p≢ rewrite lookup✖ ⦃ hp′ ⦄ p≢ = refl
  ... | yes refl rewrite lookup✓ ⦃ it ⦄ = refl

module ∣LocalStep∣ p ⦃ hp : Honest p ⦄ p′ ⦃ hp′ : Honest p′ ⦄ s mm ls′
  (let s′ = broadcast[ p′ ↝ ls′ ∣ mm ⟩ s)
  where
  pi pi′ : HonestPid
  pi  = p  ,· it
  pi′ = p′ ,· it

  lookup✓ = V.lookup∘updateAt (↑ pi′) {const ls′} (s .stateMap)
  lookup✖ = λ (p≢ : p ≢ p′) →
    V.lookup∘updateAt′ (↑ pi) (↑ pi′) {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)

  lookup✓′ : s′ ＠ p′ ≡ ls′
  lookup✓′ with ⟫ mm
  ... | ⟫ just _  = lookup✓
  ... | ⟫ nothing = lookup✓

  lookup✖′ : p ≢ p′ → s′ ＠ p ≡ s ＠ p
  lookup✖′ p≢ with ⟫ mm
  ... | ⟫ just _  = lookup✖ p≢
  ... | ⟫ nothing = lookup✖ p≢

module ∣DishonestLocalStep∣
  p ⦃ hp : Honest p ⦄ p′ (¬hp′ : Dishonest p′) s m
  (let s′ = broadcast p′ (just m) s)
  where

  p≢ : p ≢ p′
  p≢ refl = ⊥-elim $ ¬hp′ hp

  db≡ : (s ＠ p) .db ≡ (s′ ＠ p) .db
  db≡ = refl
```
-->
