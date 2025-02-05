
# Chains

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Local.Chain (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯

-- exporting here because cannot declare in `Assumptions` record
-- * ERROR: Cannot use generalized variable from let-opened module: ⋯
variable
  p p′ : Pid
  txs txs′ : List Transaction
```
-->

A chain is simply a sequence of blocks.

```agda
Chain = List Block
```
<!--
```agda
variable ch ch′ : Chain
```
-->


The genesis block is just the start of any chain, so it's simpler to consider
any empty chain to consist of just the genesis block.

```agda
genesisChain = Chain ∋ []

instance HasEpoch-Chain = HasEpoch Chain ∋ λ where ._∙epoch → λ where
  []      → 0
  (b ∷ _) → b .epoch
```

Not all chains are valid though:
each subsequent block must reference the latest block *by hash*
and cannot decrease the epoch number.

```agda
record _-connects-to-_ (b : Block) (ch : Chain) : Type where
  constructor connects∶
  field hashesMatch   : b .parentHash ≡ ch ♯
        epochAdvances : b .epoch > ch ∙epoch

data ValidChain : Chain → Type where
  [] :
      ───────────────────────
      ValidChain genesisChain

  _∷_⊣_ :
    ∀ b →
    ∙ ValidChain ch
    ∙ b -connects-to- ch
      ────────────────────
      ValidChain (b ∷ ch)
```
<!--
```agda
open _-connects-to-_ public

variable vch vch′ : ValidChain ch

uncons-vc : ValidChain (b ∷ ch) → ValidChain ch
uncons-vc (_ ∷ p ⊣ _) = p

module @0 _ where
  connects-to≡ :
    ∙ b -connects-to- ch
    ∙ b -connects-to- ch′
      ─────────────────────
      ch ≡ ch′
  connects-to≡ {ch = ch} {ch′ = ch′} b↝ b↝′ = ♯-inj ch♯≡
    where
    ch♯≡ : ch ♯ ≡ ch′ ♯
    ch♯≡ = trans (sym $ b↝ .hashesMatch) (b↝′ .hashesMatch)

  b≡→ch≡ :
    ∙ ValidChain (b  ∷ ch)
    ∙ ValidChain (b′ ∷ ch′)
    ∙ b ≡ b′
      ─────────────────────
      ch ≡ ch′
  b≡→ch≡ (_ ∷ _ ⊣ b↝) (_ ∷ _ ⊣ b↝′) refl = connects-to≡ b↝ b↝′

  ch≢→b≢ :
    ∙ ValidChain (b  ∷ ch)
    ∙ ValidChain (b′ ∷ ch′)
    ∙ ch ≢ ch′
      ─────────────────────
      b ≢ b′
  ch≢→b≢ vch vch′ = _∘ b≡→ch≡ vch vch′

  ∣ch∣≢→b≢ :
    ∙ ValidChain (b  ∷ ch)
    ∙ ValidChain (b′ ∷ ch′)
    ∙ length ch ≢ length ch′
      ─────────────────────
      b ≢ b′
  ∣ch∣≢→b≢ vch vch′ len≢ = ch≢→b≢ vch vch′ λ where refl → len≢ refl

  -- chainLen≤epoch :
  --   ValidChain ch
  --   ─────────────────────
  --   ch ∙epoch ≥ length ch

  advancingEpochs :
    ValidChain ch
    ───────────────────────────────────
    All (λ b → b .epoch ≤ ch ∙epoch) ch
  advancingEpochs [] = []
  advancingEpochs {ch = b ∷ ch} (.b ∷ vch ⊣ b↝) =
    Nat.≤-refl ∷ L.All.map (λ {b′} → QED {b′}) (advancingEpochs vch)
    where
    QED : ∀ {b′} → b′ .epoch ≤ ch ∙epoch → b′ .epoch ≤ b .epoch
    QED b≤ = Nat.≤-trans b≤ (Nat.<⇒≤ $ b↝ .epochAdvances)

  connects-to-epoch< :
    ∙ ValidChain ch
    ∙ b ∈ ch
    ∙ b′ -connects-to- ch
      ─────────────────────
      b .epoch < b′ .epoch
  connects-to-epoch< vch b∈ b↝ =
    Nat.≤-<-trans (L.All.lookup (advancingEpochs vch) b∈) (b↝ .epochAdvances)

  connects-to∉ :
    ∙ ValidChain ch
    ∙ b -connects-to- ch
      ──────────────────
      b ∉ ch
  connects-to∉ {ch = b′ ∷ ch}{b} vch b↝ b∈ = Nat.<⇒≱ e> e≤
    where
    e> : b .epoch > b′ .epoch
    e> = b↝ .epochAdvances

    e≤ : b .epoch ≤ b′ .epoch
    e≤ = L.All.lookup (advancingEpochs vch) b∈

  connect-to∈ :
    ∙ ValidChain ch
    ∙ ValidChain ch′
    ∙ b ∈ ch
    ∙ b -connects-to- ch′
      ──────────────────────
      length ch′ ≤ length ch
  connect-to∈ (_ ∷ _ ⊣ b↝′) _ (here refl) b↝
    rewrite connects-to≡ b↝ b↝′ = Nat.n≤1+n _
  connect-to∈ (_ ∷ vch ⊣ _) vch′ (there b∈) b↝
    = Nat.m≤n⇒m≤1+n $ connect-to∈ vch vch′ b∈ b↝
```
-->
