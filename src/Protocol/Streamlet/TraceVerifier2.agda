{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.TraceVerifier2 (⋯ : _) (open Assumptions ⋯) where

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
    = just (-, Vote? p ⦃ hp ⦄ {H = H} ch txs {_p}{q}{w}{x}{y}{z})

  canVote : Bool
  canVote = case canVote? of λ where
    nothing  → false
    (just _) → true

-- * verifying a whole trace

data Action : Type where
  Vote    : Pid → Chain → List Transaction → Hash → Action
  -- Propose : Pid → Chain → List Transaction → Action

Actions = List Action

private variable
  α α′ : Action
  αs αs′ : Actions

data ValidAction : Action → GlobalState → Type where
  Vote : ⦃ _ : Honest p ⦄ →
    let
      ls = (s ＠ p)
      e  = s .e-now

      L  = epochLeader e
      b  = ⟨ H , e , txs ⟩
      sᴾ = signBlock L b
      mᵖ = Propose sᴾ
    in
    ∀ (m∈ : AnyFirst (mᵖ ≡_) (ls .inbox)) →
    .(sᴾ ∉ map _∙signedBlock (ls .db)) →
    .(ls .phase ≡ Ready) →
    .(p ≢ L) →
    .(ch longest-notarized-chain-∈ ls .db) →
    .(ValidChain (b ∷ ch)) →
      ValidAction (Vote p ch txs H) s

⟦_⟧ : ValidAction α s → GlobalState
⟦_⟧ {α}{s} = λ where
  (Vote {p = p} {H = H} {txs = txs} m∈ m∉ ph≡ p≡ ch∈ vch) →
    let
      ls = s ＠ p
      e  = s .e-now

      b  = ⟨ H , e , txs ⟩
      m  = Vote $ signBlock p b
    in
      broadcast p (just m) $ updateLocal p (voteBlock ls m∈ m) s

instance
  Dec-ValidAction : ValidAction ⁇²
  Dec-ValidAction {α}{s} .dec
    with α
  ... | Vote p ch txs H
    with honest? p
  ... | no ¬hp
    = no λ where (Vote ⦃ hp ⦄ _ _ _ _ _ _) → ¬hp hp
  ... | yes hp
    -- with dec | dec | dec | dec | dec | dec
    with (let
            ls = (s ＠ p) ⦃ hp ⦄
            e = s .e-now
            L = epochLeader e
            b = ⟨ H , e , txs ⟩
            sᴾ = signBlock L b
            mᵖ = Propose sᴾ
          in
         ¿ (AnyFirst (mᵖ ≡_) (ls .inbox)) ¿)
       | (let
            ls = (s ＠ p) ⦃ hp ⦄
            e = s .e-now
            L = epochLeader e
            b = ⟨ H , e , txs ⟩
            sᴾ = signBlock L b
            mᵖ = Propose sᴾ
          in ¿ sᴾ ∉ map _∙signedBlock (ls .db) ¿)
       | (let
            ls = (s ＠ p) ⦃ hp ⦄
            e = s .e-now
            L = epochLeader e
            b = ⟨ H , e , txs ⟩
            sᴾ = signBlock L b
            mᵖ = Propose sᴾ
          in ¿ ls .phase ≡ Ready ¿)
       | (let
            ls = (s ＠ p) ⦃ hp ⦄
            e = s .e-now
            L = epochLeader e
            b = ⟨ H , e , txs ⟩
            sᴾ = signBlock L b
            mᵖ = Propose sᴾ
          in ¿ p ≢ L ¿)
       | (let
            ls = (s ＠ p) ⦃ hp ⦄
            e = s .e-now
            L = epochLeader e
            b = ⟨ H , e , txs ⟩
            sᴾ = signBlock L b
            mᵖ = Propose sᴾ
          in ¿ ch longest-notarized-chain-∈ ls .db ¿)
       | (let
            ls = (s ＠ p) ⦃ hp ⦄
            e = s .e-now
            L = epochLeader e
            b = ⟨ H , e , txs ⟩
            sᴾ = signBlock L b
            mᵖ = Propose sᴾ
          in ¿ ValidChain (b ∷ ch) ¿)
  ... | no ¬p | _ | _ | _ | _ | _
    = no λ where (Vote p _ _ _ _ _) → ¬p p
  ... | _ | no ¬p | _ | _ | _ | _
    = no λ where (Vote _ p _ _ _ _) → ¬p (toRelevant p)
  ... | _ | _ | no ¬p | _ | _ | _
    = no λ where (Vote _ _ p _ _ _) → ¬p (toRelevant p)
  ... | _ | _ | _ | no ¬p | _ | _
    = no λ where (Vote _ _ _ p _ _) → ¬p (toRelevant p)
  ... | _ | _ | _ | _ | no ¬p | _
    = no λ where (Vote _ _ _ _ p _) → ¬p (toRelevant p)
  ... | _ | _ | _ | _ | _ | no ¬p
    = no λ where (Vote _ _ _ _ _ p) → ¬p (toRelevant p)
  ... | yes _p | yes q | yes w | yes x | yes y | yes z
    = yes $ Vote ⦃ hp ⦄ _p q w x y z

mutual
  data ValidTrace : Actions → GlobalState → Type where
    [] :
      ───────────────
      ValidTrace [] s

    _∷_⊣_ : ∀ α →
      ∀ (tr : ValidTrace αs s) →
      ∙ ValidAction α s′ →
      ∀ ⦃ eq : s′ ≡ ⟦ tr ⟧∗ ⦄ →
        ──────────────────────
        ValidTrace (α ∷ αs) s′

  ⟦_⟧∗ : ValidTrace αs s → GlobalState
  ⟦_⟧∗ {s = s} = λ where
    [] → s
    (_ ∷ _ ⊣ vα) → ⟦ vα ⟧

  -- ValidTrace-s≡ : ValidTrace αs s  → s ≡ ⟦

Irr-ValidAction : Irrelevant (ValidAction α s)
Irr-ValidAction (Vote ⦃ hp ⦄ m∈ m∉ ph≡ p≢ ch∈ vch) (Vote ⦃ hp′ ⦄ m∈′ m∉′ ph≡′ p≢′ ch∈′ vch′)
  rewrite AnyFirst-irrelevant ≡-irrelevant m∈ m∈′
        | Honest-irr hp hp′
  = refl

Irr-ValidTrace : Irrelevant (ValidTrace αs s)
Irr-ValidTrace [] [] = refl
Irr-ValidTrace ((_ ∷ vαs ⊣ vα) ⦃ eq ⦄) ((_ ∷ vαs′ ⊣ vα′) ⦃ eq′ ⦄)
  = {!!}
  -- rewrite Irr-ValidTrace vαs (subst (ValidTrace _) ? vαs′) | Irr-ValidAction vα vα′
  -- = refl

instance
  Dec-ValidTrace : ValidTrace ⁇²
  Dec-ValidTrace {tr}{s} .dec with tr
  ... | []     = yes []
  ... | α ∷ αs
    with ¿ ValidTrace αs s ¿
  ... | no ¬vαs = no λ where ((_ ∷ vαs ⊣ _) ⦃ eq ⦄) → ¬vαs {!subst (ValidTrace _) (sym eq) vαs!} -- vαs
  ... | yes vαs
    with s′ ← ⟦ vαs ⟧∗
    with ¿ ValidAction α s′ ¿
  ... | no ¬vα = no λ
    where ((_ ∷ tr ⊣ vα) ⦃ eq ⦄) → ¬vα {!!} -- (subst (ValidAction α) (cong ⟦_⟧∗ $ Irr-ValidTrace tr vαs) vα)
  ... | yes vα = yes $ (_ ∷ {!vαs!} ⊣ {!vα!}) -- _ ∷ vαs ⊣ vα
