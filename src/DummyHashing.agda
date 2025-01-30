{-# OPTIONS --allow-incomplete-matches #-}
module DummyHashing where

open import Prelude
open import Hash

private variable A B : Type

DummyHashing : HashAssumptions
DummyHashing = record {go} where module go where
  Nonce = ⊤

  instance
    Hashable-× : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A × B)
    Hashable-× ._♯ (a , b) = a ♯ Bin.+ b ♯

    Hashable-⊎ : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A ⊎ B)
    Hashable-⊎ ._♯ = λ where
      (inj₁ a) → Bin.zero Bin.+ a ♯
      (inj₂ b) → Bin.suc Bin.zero Bin.+ b ♯

    Hashable-List : ⦃ Hashable A ⦄ → Hashable (List A)
    Hashable-List ._♯ = λ where
      [] → ε
      (x ∷ xs) → x ♯ Bin.+ xs ♯

    Hashable-Maybe : ⦃ Hashable A ⦄ → Hashable (Maybe A)
    Hashable-Maybe ._♯ = λ where
      nothing  → ε
      (just x) → x ♯

    Hashable-Bitstring = Hashable Bitstring ∋ λ where ._♯ → id

    Hashable-⊤         = Hashable ⊤     ∋ λ where ._♯ → const ε
    Hashable-ℕ         = Hashable ℕ     ∋ λ where ._♯ → fromℕ′
    Hashable-Int       = Hashable ℤ       ∋ λ where ._♯ → _♯ ∘ Int.∣_∣
    Hashable-Float     = Hashable Float ∋ λ where ._♯ → _♯ ∘ uncurry _,_ ∘ Fl.toRatio

    Hashable-Char   = Hashable Char   ∋ λ where ._♯ → _♯ ∘ Ch.toℕ
    Hashable-String = Hashable String ∋ λ where ._♯ → _♯ ∘ Str.toList

    Hashable-Fin = (∀{n} → Hashable (Fin  n)) ∋ λ where ._♯ → _♯ ∘ Fi.toℕ

  Hashable-Nonce = Hashable-⊤

DummySigning : (PublicKey → Signature → Hash → Bool) → SignatureAssumptions
DummySigning versig = record {go} where module go where
  open HashAssumptions DummyHashing

  verify-signature = versig

  sign : ∀ {A} → ⦃ Hashable A ⦄ → Key → A → Signature
  sign = λ k a → (k , a) ♯
