
# Global state of the entire system.

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Global.State (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.State ⋯
open import Protocol.Streamlet.Local.Chain ⋯
```
-->

The global state consists of a local state for each *honest* node.
```agda
StateMap : Type
StateMap = HonestVec LocalState
```

Other than that, it records the current epoch, in-flight messages, and
the whole history of previous messages.
```agda
record GlobalState : Type where
  constructor mkGlobalState
  field
    e-now         : Epoch          -- The current epoch.
    stateMap      : StateMap       -- A map assigning each PID its local state.
    networkBuffer : List Envelope  -- Messages in transit on the network.
    history       : List Message   -- All messages seen so far.
```
<!--
```agda
open GlobalState public
variable s s′ s″ : GlobalState
```
-->

The initial global state starts at epoch 1 with no messages and initial local states.
```agda
initStateMap : StateMap
initStateMap = V.replicate _ initLocalState

initGlobalState : GlobalState
initGlobalState = mkGlobalState 1 initStateMap [] []
```
<!--
```agda
instance
  Def-StateMap     = Default _ ∋ λ where .def → initStateMap
  Def-GlobalState  = Default _ ∋ λ where .def → initGlobalState
  Init-GlobalState = HasInitial _ ∋ λ where .Initial → _≡ initGlobalState
```
-->

```agda
_＠_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → LocalState
s ＠ p = pLookup (s .stateMap) (p ,· it)
```
