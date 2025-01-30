<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Block (⋯ : _) (open Assumptions ⋯) where
```
-->

## Blocks

```agda
record Block : Type where
  constructor ⟨_,_,_⟩
  field parentHash : Hash
        epoch      : Epoch
        payload    : List Transaction
```
<!--
```agda
open Block public
variable b b′ b″ : Block

instance
  Hashable-Block : Hashable Block
  Hashable-Block ._♯ ⟨ h , e , txs ⟩ = (h , e , txs) ♯
  Hashable-Block .♯-inj eq♯ =
    let
      h≡ , et≡ = Prod.,-injective (♯-inj eq♯)
      e≡ , t≡  = Prod.,-injective et≡
    in
       subst (λ ◆ → _ ≡ ⟨ ◆ , _ , _ ⟩) h≡
     $ cong₂ (λ ◆ ◇ → ⟨ _ , ◆ , ◇ ⟩) e≡ t≡

  DecEq-Block : DecEq Block
  DecEq-Block ._≟_ ⟨ h , e , txs ⟩ ⟨ h′ , e′ , txs′ ⟩
    with h ≟ h′
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl
    with e ≟ e′
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl
    with txs ≟ txs′
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl = yes refl
```
-->

## Signed Blocks

These blocks are the ones that are transmitted in messages.

```agda
record SignedBlock : Type where
  constructor _signed-by_
  field block     : Block
        node      : Pid

  --We assume the signature is correct.
  --Otherwise we have to add a property that signatures are valid
  -- or at least that they are determined by the block and pid,
  -- in order to be able to say that it is enough to compare node and block.
  signature : Signature
  signature = sign (node ∙sk) block

signBlock : Pid → Block → SignedBlock
signBlock pid b = b signed-by pid
```
<!--
```agda
open SignedBlock public
variable sb sb′ : SignedBlock

instance
  DecEq-SignedBlock : DecEq SignedBlock
  DecEq-SignedBlock ._≟_ (b signed-by p) (b′ signed-by p′)
    with b ≟ b′ | p ≟ p′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl

record HasBlock (A : Type) : Type where
  field _∙block : A → Block
  infix 100 _∙block
open HasBlock ⦃...⦄ public

record HasEpoch (A : Type) : Type where
  field _∙epoch : A → Epoch
  infix 100 _∙epoch
open HasEpoch ⦃...⦄ public

record HasPid (A : Type) : Type where
  field _∙pid : A → Pid
  infix 100 _∙pid
open HasPid ⦃...⦄ public

record HasSignedBlock (A : Type) : Type where
  field _∙signedBlock : A → SignedBlock
  infix 100 _∙signedBlock
open HasSignedBlock ⦃...⦄ public

instance
  HasEpoch-B  = HasEpoch Block ∋ λ where ._∙epoch → epoch

  HasBlock-SB = HasBlock SignedBlock ∋ λ where ._∙block → block
  HasEpoch-SB = HasEpoch SignedBlock ∋ λ where ._∙epoch → epoch ∘ block
  HasPid-SB   = HasPid   SignedBlock ∋ λ where ._∙pid   → node
```
-->
