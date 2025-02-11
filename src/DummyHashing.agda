module DummyHashing where

open import Prelude
open import Hash

private variable A B : Type

postulate @0 TODO : ∀ {A : Type} → A

DummyHashing : HashAssumptions
DummyHashing = record {go} where module go where instance
  Hashable-× : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A × B)
  Hashable-× ._♯ (a , b) = a ♯ Bin.+ b ♯
  Hashable-× .♯-inj _ = TODO

  Hashable-⊎ : ⦃ Hashable A ⦄ → ⦃ Hashable B ⦄ → Hashable (A ⊎ B)
  Hashable-⊎ ._♯ = λ where
    (inj₁ a) → Bin.zero Bin.+ a ♯
    (inj₂ b) → Bin.suc Bin.zero Bin.+ b ♯
  Hashable-⊎ .♯-inj _ = TODO

  Hashable-List : ⦃ Hashable A ⦄ → Hashable (List A)
  -- Hashable-List ._♯ = λ where
  --   [] → ε
  --   (x ∷ xs) → x ♯ Bin.+ xs ♯
  Hashable-List ._♯ [] = ε
  Hashable-List ._♯ (x ∷ xs) = x ♯ Bin.+ xs ♯
  Hashable-List .♯-inj _ = TODO

  Hashable-Maybe : ⦃ Hashable A ⦄ → Hashable (Maybe A)
  Hashable-Maybe ._♯ = λ where
    nothing  → ε
    (just x) → x ♯
  Hashable-Maybe .♯-inj _ = TODO

  Hashable-Bitstring = Hashable Bitstring ∋ λ where ._♯ → id; .♯-inj _ → TODO

  Hashable-⊤         = Hashable ⊤     ∋ λ where ._♯ → const ε; .♯-inj _ → TODO
  Hashable-ℕ         = Hashable ℕ     ∋ λ where ._♯ → fromℕ′; .♯-inj _ → TODO
  Hashable-Int       = Hashable ℤ       ∋ λ where ._♯ → _♯ ∘ Int.∣_∣; .♯-inj _ → TODO

  Hashable-Fin = (∀{n} → Hashable (Fin  n)) ∋ λ where ._♯ → _♯ ∘ Fi.toℕ; .♯-inj _ → TODO

DummySigning : (PublicKey → Signature → Hash → Bool) → SignatureAssumptions
DummySigning versig = record {go} where module go where
  open HashAssumptions DummyHashing

  verify-signature = versig

  sign : ∀ {A} → ⦃ Hashable A ⦄ → Key → A → Signature
  sign = λ k a → (k , a) ♯
