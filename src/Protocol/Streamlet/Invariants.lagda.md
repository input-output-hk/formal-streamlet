# Proven properties of state invariants
<!--
```agda
{-# OPTIONS --safe #-}
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Invariants (⋯ : _) where
```
-->

```agda
open import Protocol.Streamlet.Invariants.History ⋯ public
open import Protocol.Streamlet.Invariants.Votes ⋯ public
open import Protocol.Streamlet.Invariants.Uniqueness ⋯ public
open import Protocol.Streamlet.Invariants.Unforgeability ⋯ public
open import Protocol.Streamlet.Invariants.VotedOnlyOnce ⋯ public
open import Protocol.Streamlet.Invariants.TraceInvariants ⋯ public
open import Protocol.Streamlet.Invariants.IncreasingEpochs ⋯ public
```
