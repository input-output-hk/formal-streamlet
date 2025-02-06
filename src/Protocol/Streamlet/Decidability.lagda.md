# Decidable propositions appearing in the Streamlet protocol
<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Protocol.Streamlet.Assumptions

module Protocol.Streamlet.Decidability (⋯ : _) (open Assumptions ⋯) where

open import Protocol.Streamlet ⋯
```
-->

All the logical propositional appearing in the formulation
of the Streamlet protocol (c.f. `Protocol.Streamlet`) are in fact **decidable**,
meaning that we can utilize *proof-by-computation* to automatically discharge
proofs on closed terms. (c.f. `Protocol.Streamlet.Test`).

Many of these are **already** decidable, by virtue of the decidability of their
building blocks, such as the case of notarization where it is derived from all the following:

1. Decidability of the basic operations of equality (`≡`) and inequality (`≥`).

2. Decidability of the basic type formers of `⊎` and `All`.


The rest of this file provides manual proofs that this is indeed the case
for all other propositions where this is not automatically derived.

```agda
instance
  Dec-connects : _-connects-to-_ ⁇²
  Dec-connects .dec with dec | dec
  ... | yes p | yes q = yes (connects∶ p q)
  ... | no ¬p | _     = no λ where (connects∶ p _) → ¬p p
  ... | _     | no ¬q = no λ where (connects∶ _ q) → ¬q q


  Dec-ValidChain : ValidChain ⁇¹
  Dec-ValidChain {ch} .dec with ch in ch≡
  ... | [] = yes []
  ... | b ∷ ch
    with dec | dec
  ... | yes p | yes q = yes (b ∷ p ⊣ q)
  ... | no ¬p | _     = no λ where (_ ∷ p ⊣ _) → ¬p p
  ... | _     | no ¬q = no λ where (_ ∷ _ ⊣ q) → ¬q q

  Dec-chain-∈ : _chain-∈_ ⁇²
  Dec-chain-∈ {[]} {ms} .dec = yes []
  Dec-chain-∈ {b ∷ ch} {ms} .dec
              with ¿ Any ((b ≡_) ∘ _∙block) ms ¿
  ... | no ¬p = no λ where (p ∷ _ ⊣ _) → ¬p p
  ... | yes p with ¿ ch chain-∈ ms ¿
  ... | no ¬q = no (λ where (_ ∷ q ⊣ _) → ¬q q)
  ... | yes q with ¿ b -connects-to- ch ¿
  ... | no ¬w = no (λ where (_ ∷ _ ⊣ w) → ¬w w)
  ... | yes w = yes (p ∷ q ⊣ w)
```

```agda
instance
  NotarizedBlock-dec : NotarizedBlock ⁇²
  NotarizedBlock-dec {ms}{b} .dec with dec
  ... | yes p = yes (record { enoughVotes = p  })
  ... | no ¬p = no λ nb → ¬p (nb .enoughVotes)

_ = Decidable² NotarizedBlock
  ∋ dec²

_ = Decidable² NotarizedChain
  ∋ dec²
```


```agda
_ = Decidable² _notarized-chain-∈_
  ∋ dec²

-- For any block b add it the result with its corresponding chain when the
-- index corresponds b .epoch.
-- We could also generate proof of the validity of the chain.
allValidChainsUpToLength : ℕ → List Message → List Chain
allValidChainsUpToLength zero ms = [ [] ]
allValidChainsUpToLength (suc n) ms =
  let
    vs = allValidChainsUpToLength n ms
    -- bs is the list of blocks for the current length
    bs = filter (λ b → ¿ b .epoch ≡ suc n ¿) (L.map _∙block ms)

    f : Chain → List Chain
    f ch = bs >>= (λ b → if ⌊ ¿ b -connects-to- ch ¿ ⌋ then [ b ∷ ch ] else [])
  in
    vs ++ (vs >>= f)

maxEpoch : List Message → Epoch
maxEpoch ms = L.Ex.max 0 (L.map (epoch ∘ _∙block) ms)

allValidChains : List Message → List Chain
allValidChains ms = allValidChainsUpToLength (maxEpoch ms) ms

chain-∈⇒allValidChainsUpToLength : ∀ (n : ℕ) →
  ∙ ch ∙epoch ≤ n
  ∙ ch chain-∈ ms
    ──────────────────────────────────
    ch ∈ allValidChainsUpToLength n ms
chain-∈⇒allValidChainsUpToLength zero e≤n []
  = here refl
chain-∈⇒allValidChainsUpToLength zero Nat.z≤n (m∈ ∷ ch∈ ⊣ connects∶ _ ea)
  = ⊥-elim (Nat.n≮0 ea)
chain-∈⇒allValidChainsUpToLength (suc n) e≤n []
  = L.Mem.∈-++⁺ˡ (chain-∈⇒allValidChainsUpToLength n Nat.z≤n [])
chain-∈⇒allValidChainsUpToLength {b ∷ ch} {ms} (suc n) e≤n (m∈ ∷ ch∈ ⊣ x)
  with b .epoch Nat.≤? n
... | yes be≤n
  = L.Mem.∈-++⁺ˡ (chain-∈⇒allValidChainsUpToLength {b ∷ ch} n be≤n (m∈ ∷ ch∈ ⊣ x))
... | no ¬be≤n
  with eq ← b. epoch ≡ suc n ∋ Nat.≤∧≮⇒≡ e≤n (¬be≤n ∘ Nat.s≤s⁻¹) =
  let
    open Nat
    connects∶ _ ie  = x
    che≤n : (ch ∙epoch) ≤ n
    che≤n = s≤s⁻¹ (≤-trans ie e≤n)

    ch∈all : ch ∈ allValidChainsUpToLength n ms
    ch∈all = chain-∈⇒allValidChainsUpToLength n che≤n ch∈

    vs = allValidChainsUpToLength n ms

    b∈ : b ∈ L.map _∙block ms
    b∈ = L.Any.map⁺ m∈

    bs = filter (λ b → ¿ b .epoch ≡ suc n ¿) (L.map _∙block ms)

    b∈bs : b ∈ bs
    b∈bs = L.Mem.∈-filter⁺ _ b∈ eq
  in
    L.Mem.∈-++⁺ʳ vs
  $ L.Mem.>>=-∈↔ .Inverse.to
      ( ch
      , ch∈all
      , L.Mem.>>=-∈↔ .Inverse.to (b , (b∈bs , subst (λ c → _ ∈ (if ⌊ c ⌋ then _ else _))
                                                    (sym (proj₂ (dec-✓ x))) (here refl))))

maxEpoch-correct : ch chain-∈ ms → ch ∙epoch ≤ maxEpoch ms
maxEpoch-correct [] = Nat.z≤n
maxEpoch-correct {b ∷ ch}{ms} (m∈ ∷ ch∈ ⊣ _) =
  let
    b∈ : b ∈ map _∙block ms
    b∈ = L.Any.map⁺ {P = b ≡_} m∈

    es = map (epoch ∘ _∙block) ms

    be∈ : b .epoch ∈ es
    be∈ = subst (_ ∈_) (sym (L.map-∘ ms)) (L.Mem.∈-map⁺ epoch b∈)
  in
    L.All.lookup {P = _≤ maxEpoch ms} (L.Ex.xs≤max 0 es) be∈

chain-∈⇒allValidChains : ch chain-∈ ms → ch ∈ allValidChains ms
chain-∈⇒allValidChains {ms = ms} ch∈ =
  chain-∈⇒allValidChainsUpToLength (maxEpoch ms) (maxEpoch-correct ch∈) ch∈

{-
open L.Unique using ([]; _∷_; filter⁺; ++⁺; map⁺)

Unique-allChains : Unique $ allChains ms
Unique-allChains {[]} = [] ∷ []
Unique-allChains {m ∷ ms}
  with IH ← Unique-allChains {ms}
  = ++⁺ IH (map⁺ (λ where refl → refl) IH) λ (p , q) →
    let x , x∈ , x≡ = L.Mem.∈-map⁻ (blockMessage m ∷_) q in ?

Unique-allValidChains : Unique $ allValidChains ms
Unique-allValidChains {ms} =
  L.Unique.filter⁺ (λ ch → ¿ ValidChain ch ¿) (Unique-allChains {ms})
-}

instance
  Dec-longest-notarized-chain-∈ : Longest∈ ⁇²
  Dec-longest-notarized-chain-∈ {ch}{ms} .dec
    with ¿ Any _ (allValidChains ms) ¿
  ... | yes ∃ch′ =
    let ch′ , ch′∈ , ch′≰ = L.Any.satisfied ∃ch′
    in no λ where (mkLongest∈ ∄ch′) → ch′≰ $ ∄ch′ {ch′} ch′∈
  ... | no ¬∃ch′ = yes $ mkLongest∈ λ {ch′} (ch′∈ , p) → case ¿ ch′ ≤ᶜʰ ch ¿ of λ where
    (no ch′≰) → ⊥-elim
              $ ¬∃ch′
              $ L.Any.map (λ where refl → (ch′∈ , p) , ch′≰)
              $ chain-∈⇒allValidChains ch′∈
    (yes ch′≤) → ch′≤

  Dec-Finalized : ∀ {ms ch b} → FinalizedChain ms ch b ⁇
  Dec-Finalized {ch = ch} .dec
    with ch
  ... | [] = no λ ()
  ... | _ ∷ [] = no λ ()
  ... | _ ∷ _ ∷ _
    with dec | dec | dec
  ... | yes p | yes q | yes r = yes (Finalize p q r)
  ... | no ¬p | _     | _     = no λ where (Finalize p _ _) → ¬p p
  ... | _     | no ¬q | _     = no λ where (Finalize _ q _) → ¬q q
  ... | _     | _     | no ¬r = no λ where (Finalize _ _ r) → ¬r r
```

We can now provide smart constructors for using proof-by-reflection
without calling `auto`:

<!--
```agda
  DecEq-Envelope : DecEq Envelope
  DecEq-Envelope ._≟_ [ p ∣ m ⟩ [ p′ ∣ m′ ⟩
    with p ≟ p′ | m ≟ m′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
```
-->
```agda
module _ {e : Epoch} (let L = epochLeader e) {ls : LocalState} where
  ProposeBlock? : ∀ ch txs →
    let
      h = ch ♯
      b = ⟨ h , e , txs ⟩
      m = Propose $ signBlock L b
    in
    {_ : auto∶ ls .phase ≡ Ready}
    {_ : auto∶ ch longest-notarized-chain-∈ ls .db}
    {_ : auto∶ ValidChain (b ∷ ch)}
    → L ▷ e ⊢ ls —[ just m ]→ proposeBlock ls m
  ProposeBlock? _ _ {p}{q}{r} =
    ProposeBlock (toWitness p) refl (toWitness q) (toWitness r)

  VoteBlock? : ∀ p ch txs →
    let
      b  = ⟨ ch ♯ , e , txs ⟩
      mᵖ = Propose $ signBlock L b
      m  = Vote    $ signBlock p b
    in
    {m∈ : auto∶ AnyFirst (mᵖ ≡_) (ls .inbox)}
    {_ : auto∶ signBlock L b ∉ map _∙signedBlock (ls .db)}
    {_ : auto∶ ls .phase ≡ Ready}
    {_ : auto∶ p ≢ L}
    {_ : auto∶ ch longest-notarized-chain-∈ ls .db}
    {_ : auto∶ ValidChain (b ∷ ch)}
    → p ▷ e ⊢ ls —[ just m ]→ voteBlock ls (toWitness m∈) m
  VoteBlock? _ _ _ {p}{q}{r}{w}{x}{s} =
    VoteBlock (toWitness p) (toWitness q) (toWitness r) (toWitness w) (toWitness x) (toWitness s)

  RegisterVote? : ∀ p m
    ⦃ _ : m ≡ Vote sb ⦄
    {m∈ : auto∶ m ∈ ls .inbox}
    {_ : auto∶ m ∙signedBlock ∉ map _∙signedBlock (ls .db)}
    → p ▷ e ⊢ ls —[ nothing ]→ registerVote ls (toWitness m∈)
  RegisterVote? _ _ ⦃ refl ⦄ {p}{q} = RegisterVote (toWitness p) (toWitness q)

  FinalizeBlock? : ∀ p ch b →
    {_ : auto∶ ValidChain (b ∷ ch)}
    {_ : auto∶ FinalizedChain (ls .db) ch b}
    → p ▷ e ⊢ ls —[ nothing ]→ finalize ch ls
  FinalizeBlock? _ _ _ {p}{q} = FinalizeBlock _ _ (toWitness p) (toWitness q)

module _ {s : GlobalState} where

  module _ p ⦃ _ : Honest p ⦄ (let ls = s ＠ p; e = s .e-now)
    where
    Propose? : ∀ ch txs → let open ∣ProposeBlock∣ p s ch txs in
        let ls′ = proposeBlock ls M in
        ⦃ _ : p ≡ L ⦄
        {_ : auto∶ ls .phase ≡ Ready }
        {_ : auto∶ ch longest-notarized-chain-∈ ls .db }
        {_ : auto∶ ValidChain (B ∷ ch) }
        → s —→ broadcast L (just M) (updateLocal p ls′ s)
    Propose? _ _ ⦃ refl ⦄ {p}{q}{r} =
      LocalStep $ ProposeBlock? _ _ {p}{q}{r}

    Vote? : ∀ ch txs → let open ∣VoteBlock∣ p s ch txs in
      {m∈ : auto∶ AnyFirst (Mᵖ ≡_) (ls .inbox)}
      {_ : auto∶ signBlock L B ∉ map _∙signedBlock (ls .db)}
      {_ : auto∶ ls .phase ≡ Ready}
      {_ : auto∶ p ≢ L}
      {_ : auto∶ ch longest-notarized-chain-∈ ls .db}
      {_ : auto∶ ValidChain (B ∷ ch)}
      → s —→ broadcast p (just M) _
    Vote? _ _ {p}{q}{w}{x}{y}{z} =
      LocalStep $ VoteBlock? _ _ _ {p}{q}{w}{x}{y}{z}

    Register? : ∀ m →
      ⦃ _ : m ≡ Vote sb ⦄
      {m∈ : auto∶ m ∈ ls .inbox}
      {_ : auto∶ m ∙signedBlock ∉ map _∙signedBlock (ls .db)}
      → s —→ _
    Register? _ ⦃ m≡ ⦄ {p}{q} =
      LocalStep $ RegisterVote? _ _ ⦃ m≡ ⦄ {p}{q}

    Finalize? : ∀ ch b →
      {_ : auto∶ ValidChain (b ∷ ch)}
      {_ : auto∶ FinalizedChain (ls .db) ch b}
      → s —→ _
    Finalize? _ _ {p}{q} =
      LocalStep $ FinalizeBlock? _ _ _ {p}{q}

  module _ env {p : auto∶ env ∈ s .networkBuffer} where
    Deliver? : s —→ _
    Deliver? = Deliver (toWitness p)

    Drop? : s —→ _
    Drop? = Drop (toWitness p)
```
