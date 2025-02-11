{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.StepVerifier (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
open import Protocol.Streamlet.Decidability ⋯


-- * verifying that a certain step is possible

module _
  (p : Pid)
  (ch : Chain) (txs : List Transaction) (H : Hash)
  (s : GlobalState)
  where
  canVote? : Maybe $ ∃ λ s′ → s —→ s′
  canVote?
    with honest? p
  ... | no ¬hp
    = nothing
  ... | yes hp
    with dec | dec | dec | dec | dec | dec
  ... | no ¬p | _ | _ | _ | _ | _
    = nothing
  ... | _ | no ¬p | _ | _ | _ | _
    = nothing
  ... | _ | _ | no ¬p | _ | _ | _
    = nothing
  ... | _ | _ | _ | no ¬p | _ | _
    = nothing
  ... | _ | _ | _ | _ | no ¬p | _
    = nothing
  ... | _ | _ | _ | _ | _ | no ¬p
    = nothing
  ... | yes _p | yes q | yes w | yes x | yes y | yes z
    = just (-, Vote? p ⦃ hp ⦄ ch txs {_p}{q}{w}{x}{y}{z})

  canVote : Bool
  canVote = case canVote? of λ where
    nothing  → false
    (just _) → true
