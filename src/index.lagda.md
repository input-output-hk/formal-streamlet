# Index
```agda
-- {-# OPTIONS --safe #-}

-- ** prerequisites
open import Prelude
open import Hash

-- ** the Streamlet protocol
open import Protocol.Streamlet

-- ** decision procedures
open import Protocol.Streamlet.Decidability

-- ** mechanized proof of consistency
open import Protocol.Streamlet.Properties

-- ** example trace
open import DummyHashing {- unsafe -}
open import Protocol.Streamlet.Test.Core
open import Protocol.Streamlet.Test.ExampleTrace

-- ** trace verifier
open import Protocol.Streamlet.TraceVerifier
open import Protocol.Streamlet.Test.TraceVerifier

-- ** variants on trace verification
open import Protocol.Streamlet.TraceVerifier.Intrinsic
open import Protocol.Streamlet.TraceVerifier.Reverse

-- ** other tests
open import Protocol.Streamlet.Test.Block
open import Protocol.Streamlet.Test.Chain
open import Protocol.Streamlet.Test.LocalState
open import Protocol.Streamlet.Test.LocalState2
open import Protocol.Streamlet.StepVerifier
open import Protocol.Streamlet.Test.StepVerifier
```
