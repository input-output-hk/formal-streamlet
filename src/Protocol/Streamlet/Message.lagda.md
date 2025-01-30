## Messages

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Message (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯
```
-->
```agda
data Message : Type where
  Propose Vote : SignedBlock → Message
```
<!--
```agda
variable
  m m′ : Message
  ms ms′ : List Message
  mm : Maybe Message

instance
  DecEq-Message : DecEq Message
  DecEq-Message ._≟_ (Propose sb) (Propose sb′)
    with sb ≟ sb′
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl = yes refl
  DecEq-Message ._≟_ (Vote sb) (Vote sb′)
    with sb ≟ sb′
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl = yes refl
  DecEq-Message ._≟_ (Propose _) (Vote _) = no λ ()
  DecEq-Message ._≟_ (Vote _) (Propose _) = no λ ()
```
-->

```agda
record Envelope : Type where
   constructor [_∣_⟩
   field recipient : Pid
         content   : Message
```
<!--
```agda
open Envelope public
variable env env′ : Envelope; envs envs′ : List Envelope

record HasMessage (A : Type) : Type where
  field _∙message : A → Message
  infix 100 _∙message
open HasMessage ⦃...⦄ public

instance
  HasSB-Msg = HasSignedBlock Message ∋ λ where ._∙signedBlock → λ where
    (Propose b) → b
    (Vote    b) → b

  HasBlock-Msg = HasBlock Message ∋ λ where ._∙block → _∙block ∘ _∙signedBlock
  HasPid-Msg   = HasPid   Message ∋ λ where ._∙pid   → _∙pid   ∘ _∙signedBlock
  HasEpoch-Msg = HasEpoch Message ∋ λ where ._∙epoch → _∙epoch ∘ _∙block

  HasMsg-Env   = HasMessage Envelope ∋ λ where ._∙message → content
  HasBlock-Env = HasBlock   Envelope ∋ λ where ._∙block   → _∙block ∘ _∙message
  HasPid-Env   = HasPid     Envelope ∋ λ where ._∙pid     → recipient
```
-->
