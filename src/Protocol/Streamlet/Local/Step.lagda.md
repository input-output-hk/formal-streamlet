
# Transitions between local states of a single node.

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Base
open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Local.Step (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet.Block ⋯
open import Protocol.Streamlet.Message ⋯
open import Protocol.Streamlet.Local.Chain ⋯
open import Protocol.Streamlet.Local.State ⋯
```
-->

## Some auxililary functions
```agda
proposeBlock : LocalState → Message → LocalState
proposeBlock ls m = record ls
  { phase = Voted
  ; db    = m ∷ ls .db
  }

voteBlock : (ls : LocalState) → AnyFirst (m ≡_) (ls .inbox) → Message → LocalState
voteBlock {m} ls m∈ vote = record ls
  { db    = vote ∷ m ∷ ls .db
  ; phase = Voted
  ; inbox = (ls .inbox) L.Any.─ (AnyFirst⇒Any m∈)
  }

registerVote : (ls : LocalState) → m ∈ ls .inbox → LocalState
registerVote {m} ls m∈ = record ls
  { db    = m ∷ ls .db
  ; inbox = (ls .inbox) L.Any.─ m∈
  }

finalize : Chain → Op₁ LocalState
finalize ch ls = record ls
  { final = ch}
```

## The local step relation

Given a local state a step may produce a message.
(The local step relation could be made deterministic, by stating
that a node should propose or vote before it starts to process votes.)

```agda
data _▷_⊢_—[_]→_
  (p : Pid) (e : Epoch) (ls : LocalState) : Maybe Message → LocalState → Type where

  -- Leader proposes a new block.
  ProposeBlock :
    let
      L = epochLeader e
      h = ch ♯
      b = ⟨ h , e , txs ⟩
      m = Propose $ signBlock p b
    in
    ∙ ls .phase ≡ Ready
    ∙ p ≡ L
    ∙ ch longest-notarized-chain-∈ ls .db
    ∙ ValidChain (b ∷ ch)
      ─────────────────────────────────────────
      p ▷ e ⊢ ls —[ just m ]→ proposeBlock ls m

  -- Upon getting the first valid proposal a node votes for it.
  VoteBlock :
    let
      L  = epochLeader e
      b  = ⟨ H , e , txs ⟩
      sᴾ = signBlock L b
      mᵖ = Propose sᴾ
      m  = Vote    $ signBlock p b
    in
    ∀ (m∈ : AnyFirst (mᵖ ≡_) (ls .inbox)) →
    ∙ sᴾ ∉ map _∙signedBlock (ls .db) -- an alternative is to change voteBlock, accept the proposal but erase the existing vote.
    ∙ ls .phase ≡ Ready
    ∙ p ≢ L
    ∙ ch longest-notarized-chain-∈ ls .db
    ∙ ValidChain (b ∷ ch)
      ─────────────────────────────────────────
      p ▷ e ⊢ ls —[ just m ]→ voteBlock ls m∈ m

  -- NB: could a node get a proposal for a future epoch?

  -- Whenever other nodes vote, register their vote.
  RegisterVote : let m = Vote sb in
    -- TODO: discard dishonest votes
    ∀ (m∈ : m ∈ ls .inbox) →
    ∙ sb ∉ map _∙signedBlock (ls .db)
           -- don't count a vote twice
           -- even if one is Propose sb and the other is Vote sb
      ───────────────────────────────────────────
      p ▷ e ⊢ ls —[ nothing ]→ registerVote ls m∈

  -- Node finalizes a block (in their view).
  FinalizeBlock : ∀ ch b →
    ∙ ValidChain (b ∷ ch)
    ∙ FinalizedChain (ls .db) ch b
      ───────────────────────────────────────
      p ▷ e ⊢ ls —[ nothing ]→ finalize ch ls
```

When the epoch advances, reset all phases to `Ready`:
```agda
epochChange : Op₁ LocalState
epochChange ls = record ls
  { phase = Ready }
```

A node can also receive messages at their inbox:
```agda
receiveMessage : Message → Op₁ LocalState
receiveMessage m ls = record ls
  { inbox = ls .inbox L.∷ʳ m }
```

## Traces

We consider **traces** of the (local) step relation,
defined as its *reflexive-transitive closure*:

```agda
private module ∣LOCAL∣ (p : Pid) where

  StateProperty = LocalState → Type

  _—→_ : Rel LocalState _
  ls —→ ls′ = ∃ λ e → ∃ λ mm → p ▷ e ⊢ ls —[ mm ]→ ls′

  open import Prelude.Closures _—→_ public

  -- step incorporating global changes as well (currently unused)
  data _—→⁺_ : Rel LocalState 0ℓ where
    LocalStep      : ls —→ ls′ → ls —→⁺ ls′
    EpochChange    : ls —→⁺ epochChange ls
    ReceiveMessage : ls —→⁺ receiveMessage m ls

open ∣LOCAL∣ public using () renaming
  ( _—→_ to _▷_—→_; _—↠_ to _▷_—↠_; _—→⁺_ to _▷_—→⁺_
  ; Reachable to LocalReachable; Invariant to LocalInvariant
  ; StateProperty to LocalStateProperty
  )
```
