## Assumptions of the Streamlet protocol

<!--
```agda
{-# OPTIONS --safe #-}
module Protocol.Streamlet.Assumptions where

open import Prelude
open import Hash

open import Protocol.Streamlet.Base
```
-->

```agda
record Assumptions : Type₁ where

  -- * cryptographic assumptions

  field hashes : _
  open HashAssumptions hashes public

  field signatures : _
  open SignatureAssumptions signatures public

  -- * participants

  field nodes : ℕ -- Fixed number of participants.
  field nodes⁺ : nodes > 0

  Pid : Type
  Pid = Fin nodes -- Each participant is assigned an identifier `Pid`.

  allPids : List Pid
  allPids = L.allFin nodes

  -- * random leader selection

  field epochLeader : Epoch → Pid

  -- * honest majority

  IsMajorityRatio  : ℕ → Type
  IsMajorityRatio n = 3 * n ≥ 2 * nodes

  IsMajorityRatio⁺ : ℕ → Type
  IsMajorityRatio⁺ n = 3 * n > 2 * nodes

  IsMajority  : ∀ {A : Type} → List A → Type
  IsMajority  = IsMajorityRatio  ∘ length

  IsMajority⁺ : ∀ {A : Type} → List A → Type
  IsMajority⁺ = IsMajorityRatio⁺ ∘ length

  field Honest : Pid → Type
        instance Dec-Honest : Honest ⁇¹
        -- Honest-irr : Irrelevant¹ Honest

  Dishonest = ¬_ ∘ Honest

  honest? : Decidable¹ Honest
  honest? = dec¹ ⦃ Dec-Honest ⦄

  field honest-majority : IsMajority⁺ (filter honest? allPids)

  -- * transactions

  field
    Transaction : Type -- Abstract type of transactions.
    instance
      DecEq-Tx    : DecEq    Transaction
      Hashable-Tx : Hashable Transaction

  -- * public-key infrastructure

  field keys : Pid → KeyPair

  _∙pk _∙sk : Pid → PublicKey
  p ∙pk = p .keys .publicKey
  p ∙sk = p .keys .privateKey

  -- * extra lemmas

  majority⁺ : ¬ IsMajorityRatio 0
  majority⁺ m0 with nodes | nodes⁺
  ... | Nat.zero | ()

  majority-≤ : ∀ {n m} →
    ∙ n ≤ m
    ∙ IsMajorityRatio n
      ─────────────────
      IsMajorityRatio m
  majority-≤ {n}{m} n≤m maj =
    begin 2 * nodes ≤⟨ maj ⟩
          3 * n     ≤⟨ *-mono-≤ {3} ≤-refl n≤m ⟩
          3 * m     ∎ where open Nat; open ≤-Reasoning

  majority-∷ : ∀ {n} → IsMajorityRatio n → IsMajorityRatio (suc n)
  majority-∷ = majority-≤ (Nat.n≤1+n _)

  majority-⊆ : ∀ {A : Type} {vs vs′ : List A} →
    ∙ vs ⊆ vs′
    ∙ IsMajority vs
      ──────────────
      IsMajority vs′
  majority-⊆ = majority-≤ ∘ L.SubL.length-mono-≤

  honestFromMajority : ∀ {pids} →
    ∙ Unique pids
    ∙ 3 * length pids ≥ nodes
      ───────────────────────
      Any Honest pids
  honestFromMajority {xs} uxs xs≥n/3 = QED
    where
    hs = filter honest? allPids

    uhs : Unique hs
    uhs = filter⁺ honest? (allFin⁺ nodes)
      where open L.Unique

    xs∩ = xs ∩ hs

    open Nat; open ≤-Reasoning

    len+ : length xs + length hs > nodes
    len+ = *-cancelˡ-< 3 _ _ $
      begin-strict
        3 * nodes
      ≡⟨⟩
        nodes + 2 * nodes
      <⟨ +-monoʳ-< nodes honest-majority ⟩
        nodes + 3 * length hs
      ≤⟨ +-monoˡ-≤ _ xs≥n/3  ⟩
        3 * length xs + 3 * length hs
      ≡˘⟨ *-distribˡ-+ 3 (length xs) _ ⟩
        3 * (length xs + length hs)
      ∎

    len∩ : length xs∩ > 0
    len∩ =
      begin-strict
        0
      ≡˘⟨ n∸n≡0 nodes ⟩
        nodes ∸ nodes
      <⟨ ∸-monoˡ-< len+ ≤-refl ⟩
        (length xs + length hs) ∸ nodes
      ≤⟨ length-∩ uxs uhs ⟩
        length xs∩
      ∎

    QED : Any Honest xs
    QED =
      let
        x , x∈ = nonEmpty∈ len∩
        x∈xs , x∈hs = ∈-∩⁻ x xs hs x∈
        _ , hx = L.Mem.∈-filter⁻ honest? {xs = allPids} x∈hs
      in
        L.Any.map (λ where refl → hx) x∈xs

  open import Prelude.PVec Honest ⦃ Dec-Honest ⦄ public
    renaming (PVec to HonestVec; pFins to honestPids; PIndex to HonestPid)
```
