

## Traces

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Global.Traces (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯
open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.Chain ⋯
open import Protocol.Streamlet.Local.State ⋯
open import Protocol.Streamlet.Local.Step ⋯
open import Protocol.Streamlet.Global.State ⋯
open import Protocol.Streamlet.Global.Step ⋯
```
-->



We consider **traces** of the (global) step relation,
defined as its *reflexive-transitive closure*, and use these to prove invariants
as state predicates:

```agda
open import Prelude.Closures _—→_ public
  using ( begin_; _∎
        ; _↞—_; _⟨_⟩←—_; _⟨_∣_⟩←—_
        ; _—↠_; _—→⟨_⟩_
        ; Reachable; Invariant; StepPreserved; Step⇒Invariant
        ; Trace; TraceProperty; TraceInvariant
        )

StateProperty = GlobalState → Type
```

Now, we can consider a specific local step occurring within a sequence of global transitions:

```agda
record Step : Type where
  constructor _⊢_
  field
    stepArgs : _ × _ × _ × _ × _
    step : let p , e , ls , mm , ls' = stepArgs in
           p ▷ e ⊢ ls —[ mm ]→ ls'

LocalStepProperty = Step → Type

allLocalSteps : (s′ ↞— s) → List Step
allLocalSteps = λ where
  (_ ∎) → []
  (_ ⟨ LocalStep st ⟩←— tr) → (_ ⊢ st) ∷ allLocalSteps tr
  (_ ⟨ _ ⟩←— tr) → allLocalSteps tr

_∋⋯_ : Trace → LocalStepProperty → Type
(_ , _ , _ , tr) ∋⋯ P = Any P (allLocalSteps tr)
```
