# STREAMLET: Textbook Streamlined Blockchains

```agda
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet (⋯ : Assumptions) where

open import Protocol.Streamlet.Base public
open import Protocol.Streamlet.Assumptions public

open import Protocol.Streamlet.Block ⋯ public
open import Protocol.Streamlet.Message ⋯ public
open import Protocol.Streamlet.Local.Chain ⋯ public
open import Protocol.Streamlet.Local.State ⋯ public
open import Protocol.Streamlet.Local.Step ⋯ public
open import Protocol.Streamlet.Global.State ⋯ public
open import Protocol.Streamlet.Global.Step ⋯ public
open import Protocol.Streamlet.Global.Traces ⋯ public
```
