<!--
```agda
{-# OPTIONS --safe #-}
module Hash where

open import Prelude

private variable A B : Type
```
-->

# Hashes

Hashes are represented as bitstrings:
```agda
Hash : Type
Hash = Bitstring
```
<!--
```agda
variable H H′ : Hash
```
-->

Hashable types are collected under a appropriate typeclass:
```agda
record Hashable (A : Type) : Type where
  field
    _♯    : A → Hash
    ♯-inj : Injective≡ _♯

  infix 100 _♯
```
<!--
```agda
Hashable¹ : ∀ {A} → (A → Type) → Type
Hashable¹ P = ∀ {x} → Hashable (P x)
```
-->

We assume an abstract type of *nonces* and
hashing functions for primitive types and type formers:
```agda
record HashAssumptions : Type₁ where
  field
    Nonce : Type
    instance
      -- type formers
      Hashable-×     : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A × B)
      Hashable-⊎     : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A ⊎ B)
      Hashable-List  : ⦃ Hashable A ⦄ → Hashable (List A)
      Hashable-Maybe : ⦃ Hashable A ⦄ → Hashable (Maybe A)

      -- base types
      Hashable-⊤         : Hashable ⊤
      Hashable-String    : Hashable String
      Hashable-Bitstring : Hashable Bitstring
      Hashable-Nonce     : Hashable Nonce
      Hashable-ℕ         : Hashable ℕ
      Hashable-Int       : Hashable ℤ
      Hashable-Float     : Hashable Float
      Hashable-Fin       : ∀{n} → Hashable (Fin n)
```
<!--
```agda
open Hashable ⦃...⦄ public
```
-->

# Signatures

Let's start with various aliases for bitstrings and key pairs:
```agda
Key Signature PublicKey PrivateKey : Type
Key        = Bitstring
Signature  = Bitstring
PublicKey  = Key
PrivateKey = Key

record KeyPair : Type where
  constructor mk-keyPair
  field publicKey  : PublicKey
        privateKey : PrivateKey
open KeyPair public
```

We then assume that there is a way to sign (hashable) values,
as well as the existence of a suitable signature verification algorithm (e.g. SHA256).
```agda
record SignatureAssumptions : Type₁ where
  field
    verify-signature : PublicKey → Signature → Hash → Bool
    sign : ⦃ Hashable A ⦄ → Key → A → Signature
```
