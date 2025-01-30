{-# OPTIONS --safe #-}
module Prelude.Lists where

open import Prelude.Init hiding (mapMaybe); open L using (mapMaybe)
open import Prelude.FromNat
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Anyable
open import Prelude.Allable
open L.Any using (satisfied)

private variable
  A B : Type
  xs ys : List A
  x x′ y : A
  f : A → B

-- * Nats

open Nat hiding (_≟_)

module _ m {n o} (open ≤-Reasoning) where
  +-∸-assoc≤ : (m + n) ∸ o ≤ m + (n ∸ o)
  +-∸-assoc≤
    with o ≤? n
  ... | yes o≤n = ≤-reflexive $ +-∸-assoc _ o≤n
  ... | no o≰n
    with o>n ← <⇒≤ (≰⇒> o≰n)
    with m≡m+n∸o ← begin-equality
      m           ≡˘⟨ +-identityʳ _ ⟩
      m + 0       ≡˘⟨ cong (m +_) $ m≤n⇒m∸n≡0 o>n ⟩
      m + (n ∸ o) ∎
    with o ≥? m + n
  ... | yes o≥m+n =
    begin
      (m + n) ∸ o
    ≡⟨ m≤n⇒m∸n≡0 o≥m+n ⟩
      0
    ≤⟨ z≤n ⟩
      m
    ≡⟨ m≡m+n∸o ⟩
      m + (n ∸ o)
    ∎
  ... | no o≱m+n =
    let o<m+n = <⇒≤ (≰⇒> o≱m+n) in
    begin
      (m + n) ∸ o
    ≤⟨ +-cancelʳ-≤ o _ m
    $ begin (m + n) ∸ o + o ≡⟨ m∸n+n≡m o<m+n ⟩
            m + n           ≤⟨ +-monoʳ-≤ m o>n ⟩
            m + o           ∎
    ⟩
      m
    ≡⟨ m≡m+n∸o ⟩
      m + (n ∸ o)
    ∎

-- * Empty list

Null : Pred (List A) _
Null = _≡ []

Null-map⁻ : Null (map f xs) → Null xs
Null-map⁻ {xs = []} _ = refl

-- * Any/All

private variable P Q : Pred A ℓ

∈-lookup : ∀ {xs : List A} (i : Any P xs) → L.Any.lookup i ∈ xs
∈-lookup = λ where
  (here px) → here refl
  (there i) → there (∈-lookup i)

anyAll : ∀ {xs : List A} → All Q xs → (i : Any P xs) → Q (L.Any.lookup i)
anyAll q = L.All.lookup q ∘ ∈-lookup

satisfied′ : ∀ {A : Type} {P : A → Type} {xs : List A} →
  Any P xs
  ───────────────────
  ∃[ x ] x ∈ xs × P x
satisfied′ = λ where
  (here px)   → -, here refl , px
  (there pxs) → let x , x∈ , px = satisfied′ pxs
                in  x , there x∈ , px

∃⇔Any : ∀ {xs : List A} →
  (∃ λ x → P x × x ∈ xs)
  ══════════════════════
  Any P xs

module _ {P : A → Type} {xs : List A} where
  ∃⇒Any = ∃⇔Any {P = P}{xs = xs} .proj₁
  Any⇒∃ = ∃⇔Any {P = P}{xs = xs} .proj₂

∃⇔Any = (λ (_ , px , x∈) → L.Any.map (λ where refl → px) x∈)
      , λ where (here px)   → -, px , here refl
                (there pxs) → map₂ (map₂ there) (Any⇒∃ pxs)

-- * indexing

Index : List A → Type
Index = Fin ∘ length

mapWithIndex : ∀ {B : Type} (xs : List A) → (Index xs → B) → List B
mapWithIndex [] _ = []
mapWithIndex (_ ∷ xs) f = f 0 ∷ mapWithIndex xs (f ∘ fsuc)

filterByIndex : (xs : List A) → (Index xs → Bool) → List A
filterByIndex [] _ = []
filterByIndex (x ∷ xs) f =
  let xs′ = filterByIndex xs (f ∘ fsuc) in
  if f 0 then x ∷ xs′ else xs′

∈-filterByIndex⁻ : ∀ (xs : List A) (f : Index xs → Bool) → filterByIndex xs f ⊆ˢ xs
∈-filterByIndex⁻ (x ∷ xs) f x∈
  with f 0
... | false = there $ ∈-filterByIndex⁻ xs (f ∘ fsuc) x∈
... | true
  with x∈
... | here refl = here refl
... | there x∈  = there $ ∈-filterByIndex⁻ xs (f ∘ fsuc) x∈

subsetIndices : xs ⊆ˢ ys → List (Index ys)
subsetIndices {xs = []} {ys} p = []
subsetIndices {xs = x ∷ xs} {ys} p =
  L.Any.index (p $ here refl) ∷ subsetIndices {xs = xs} (p ∘ there)

removeAt∗ : (xs : List A) → List (Index xs) → List A
removeAt∗ xs is = filterByIndex xs (⌊_⌋ ∘ (_∉? is))

∈-removeAt∗⁻ : ∀ {xs : List A} {is : List (Index xs)} → removeAt∗ xs is ⊆ˢ xs
∈-removeAt∗⁻ = ∈-filterByIndex⁻ _ _

remove⊆ˢ : {xs ys : List A} → xs ⊆ˢ ys → List A
remove⊆ˢ {ys = ys} p = removeAt∗ ys $ subsetIndices p

∈-remove⊆ˢ⁻ : ∀ {xs ys : List A} (p : xs ⊆ˢ ys) → remove⊆ˢ p ⊆ˢ ys
∈-remove⊆ˢ⁻ _ = ∈-removeAt∗⁻

lookup≡proj₁∘satisfied : ∀ {xs : List A} (p : Any P xs) →
  L.Any.lookup p ≡ satisfied p .proj₁
lookup≡proj₁∘satisfied (here _)  = refl
lookup≡proj₁∘satisfied (there p) = lookup≡proj₁∘satisfied p

∈-removeAt⁻ : ∀ (n : Index xs) {x} → x ∈ L.removeAt xs n → x ∈ xs
∈-removeAt⁻ {xs = _ ∷ _} fzero p = there p
∈-removeAt⁻ {xs = _ ∷ _} (fsuc n) = λ where
  (here refl) → here refl
  (there p)   → there $′ ∈-removeAt⁻ n p

∈-∷ʳ⁻ : ∀ {x y} → x ∈ xs L.∷ʳ y → (x ∈ xs) ⊎ (x ≡ y)
∈-∷ʳ⁻ {xs = xs}{x}{y} x∈ = case L.Mem.∈-++⁻ xs x∈ of λ where
  (inj₁ x∈)        → inj₁ x∈
  (inj₂ (here x≡)) → inj₂ x≡

-- * constructing indexed functions

∅ : Index {A = A} [] → B
∅ ()

[_∶_⋯_∶_] : (x : A) → B → ∀ xs → (Index xs → B) → (Index (x ∷ xs) → B)
[ _ ∶ b ⋯ _ ∶ f ] = λ where
  fzero    → b
  (fsuc i) → f i

-- * removing suffix

_─⋯_ : (xs : List A) → Index xs → List A
xs ─⋯ i = L.drop (suc $ Fi.toℕ i) xs

private
  open import Prelude.LiteralSequences
  ns = List ℕ ∋ [ 0 ⨾ 1 ⨾ 2 ⨾ 3 ]
  _ = ns ─⋯ 0 ≡ [ 1 ⨾ 2 ⨾ 3 ]
    ∋ refl
  _ = ns ─⋯ 1 ≡ [ 2 ⨾ 3 ]
    ∋ refl
  _ = ns ─⋯ 2 ≡ [ 3 ]
    ∋ refl
  _ = ns ─⋯ 3 ≡ []
    ∋ refl

─⋯-⊆ : (i : Index xs) → (xs ─⋯ i) ⊆ˢ xs
─⋯-⊆ {xs = _ ∷ _} fzero    = there
─⋯-⊆ {xs = _ ∷ _} (fsuc i) = there ∘′ ─⋯-⊆ _

─⋯-∷ : (i : Index xs) → ∃ λ ys → xs ≡ ys ++ L.lookup xs i ∷ (xs ─⋯ i)
─⋯-∷ {xs = _ ∷ _}  fzero    = [] , refl
─⋯-∷ {xs = _ ∷ xs} (fsuc i) = let ys , xs≡ = ─⋯-∷ i in  _ ∷ ys , cong (_ ∷_) xs≡

─⋯-len : (i : Index xs) → length (xs ─⋯ i) < length xs
─⋯-len {xs = _ ∷ _}  fzero    = ≤-refl
─⋯-len {xs = _ ∷ xs} (fsuc i) = s≤s $ <⇒≤ $ ─⋯-len {xs = xs} i

-- * filter

module _ {P : A → Set} (P? : Decidable¹ P) where

  filter-length : length xs ≡ length (filter P? xs) + length (filter (¬? ∘ P?) xs)
  filter-length {[]} = refl
  filter-length {x ∷ xs} with P? x
  ... | no ¬p
   rewrite +-suc (length (filter P? xs)) (length (filter (¬? ∘ P?) xs))
   rewrite filter-length {xs = xs} = refl
  ... | yes p rewrite filter-length {xs = xs} = refl

  module _ {Q : A → Set} (Q? : Decidable¹ Q) (P⇔Q : P ≐ Q) where
    filter≡ : ∀ xs → filter P? xs ≡ filter Q? xs
    filter≡ [] = refl
    filter≡ (x ∷ xs)
      with IH ← filter≡ xs
      with P? x
    ... | yes px rewrite dec-yes (Q? x) (P⇔Q .proj₁ px) .proj₂ = cong (x ∷_) IH
    ... | no ¬px rewrite dec-no  (Q? x) (¬px ∘ P⇔Q .proj₂)     = IH

module _ {P : Pred A ℓ} ⦃ _ : P ⁇¹ ⦄ (f : B → A) where
  filter-map : ∀ xs → filter ¿ P ¿¹ (map f xs) ≡ map f (filter (¿ P ¿¹ ∘ f) xs)
  filter-map [] = refl
  filter-map (x ∷ xs)
    with IH ← filter-map xs
    with ¿ P (f x) ¿
  ... | yes _ = cong (_ ∷_) IH
  ... | no  _ = IH

-- * membership

open L.Mem using (mapWith∈)
open L.All using (lookup; tabulate; ¬Any⇒All¬)
open L.Any using (index; _─_)

∈-─⁻ : (x∈′ : x′ ∈ xs) → x ∈ (xs ─ x∈′) → x ∈ xs
∈-─⁻ = λ where
  (here _)   x∈′         → there x∈′
  (there x∈) (here refl) → here refl
  (there x∈) (there x∈′) → there $ ∈-─⁻ x∈ x∈′

∈-─⁺ : x ≢ y → (x∈ : x ∈ xs) → y ∈ xs → y ∈ (xs ─ x∈)
∈-─⁺ {xs = x ∷ xs} x≢ = λ where
  (here refl) (here refl) → ⊥-elim $ x≢ refl
  (there x∈)  (here refl) → here refl
  (here refl) (there y∈)  → y∈
  (there x∈)  (there y∈)  → there $ ∈-─⁺ x≢ x∈ y∈

All-─⁻ : ∀ {A : Type} {P : A → Type} {x : A} xs →
  ∀ (x∈ : x ∈ xs) →
  ∙ P x
  ∙ All P (xs ─ x∈)
    ─────────────────────
    All P xs
All-─⁻ (_ ∷ _)    (here refl) x∈ xs∈       = x∈ ∷ xs∈
All-─⁻ (_  ∷ xs) (there x∈xs) x∈ (p ∷ xs∈) = p  ∷ All-─⁻ xs x∈xs x∈ xs∈

All∈-dropHead : ∀ {A : Type} {x : A} {xs ys} →
  ∙ x ∉ ys
  ∙ All (_∈ (x ∷ xs)) ys
    ────────────────────
    All (_∈ xs) ys
All∈-dropHead x∉ p = L.All.tabulate λ y∈ →
  case L.All.lookup p y∈ of λ where
    (here refl) → ⊥-elim $ x∉ y∈
    (there p) → p

length-mapWith∈ : (f : ∀ {x} → x ∈ xs → B) →
  length (mapWith∈ xs f) ≡ length xs
length-mapWith∈ {xs = []} _ = refl
length-mapWith∈ {xs = _ ∷ xs} f = cong suc $ length-mapWith∈ {xs = xs} (f ∘ there)

mapWith∈-∀ : ∀ {xs : List A}  {f : ∀ {x : A} → x ∈ xs → B} {P : B → Type}
  → (∀ {x} x∈ → P (f {x} x∈))
  → (∀ {y} → y ∈ mapWith∈ xs f → P y)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (here px)  rewrite px = ∀P (here refl)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (there y∈) = mapWith∈-∀ (∀P ∘ there) y∈

Unique-mapWith∈ : ∀ {A B : Type} {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → (∀ {x x′} {x∈ : x ∈ xs} {x∈′ : x′ ∈ xs}
        → f x∈ ≡ f x∈′
        → index x∈ ≡ index x∈′)
  → Unique (mapWith∈ xs f)
Unique-mapWith∈ {xs = []}     {f = f} f≡ = []
Unique-mapWith∈ {xs = x ∷ xs} {f = f} f≡
  = L.All.tabulate (mapWith∈-∀ {P = f (here refl) ≢_} λ _ eq → case f≡ eq of λ () )
  ∷ Unique-mapWith∈ {xs = xs} (Fi.suc-injective ∘ f≡)

filterWith∈ : (xs : List A) {P : ∀ {x} → x ∈ xs → Set}
              (P? : ∀ {x} (x∈ : x ∈ xs) → Dec (P x∈)) → List A
-- filterWith∈ xs P?
--   = map proj₁
--   $ filter (λ (x , x∈) → P? x∈)
--   $ mapWith∈ xs λ {x} x∈ → x , x∈
filterWith∈ [] P? = []
filterWith∈ (x ∷ xs) P?
  with IH ← filterWith∈ xs (P? ∘ there)
  with P? (here refl)
... | yes px = x ∷ IH
... | no ¬px = IH

filterWith∈≡ :
  (xs : List A)
  {P Q : ∀ {x} → x ∈ xs → Set}
  (P? : ∀ {x} (x∈ : x ∈ xs) → Dec (P x∈))
  (Q? : ∀ {x} (x∈ : x ∈ xs) → Dec (Q x∈))
  (P⇔Q : ∀ {x}{x∈ : x ∈ xs} → P x∈ ↔ Q x∈)
  → filterWith∈ xs P? ≡ filterWith∈ xs Q?
filterWith∈≡ [] P? Q? P⇔Q = refl
filterWith∈≡ (x ∷ xs) P? Q? P⇔Q
  with IH ← filterWith∈≡ xs (P? ∘ there) (Q? ∘ there) P⇔Q
  with P? (here refl)
... | yes px rewrite dec-yes (Q? (here refl)) (P⇔Q .proj₁ px) .proj₂
  = cong (x ∷_) IH
... | no ¬px rewrite dec-no (Q? (here refl)) (¬px ∘ P⇔Q .proj₂)
  = IH

filter∘mapWith∈ :
  ∀ (xs : List A)
  → (f : ∀ {x} → x ∈ xs → B)
  → {P : B → Set}
  → (P? : Decidable¹ P)
  -- → filter P? (mapWith∈ xs f) ≡ map f (filterWith∈ xs (P? ∘ f))
  → length (filter P? (mapWith∈ xs f)) ≡ length (filterWith∈ xs (P? ∘ f))
filter∘mapWith∈ [] f {P} P? = refl
filter∘mapWith∈ (x ∷ xs) f {P} P?
  with IH ← filter∘mapWith∈ xs (f ∘ there) P?
  with P? (f $ here refl)
... | yes px = cong suc IH
... | no ¬px = IH

filterWith∈≗filter : ∀ {P : A → Set} (P? : Decidable¹ P) xs
                   → filterWith∈ xs (λ {x} _ → P? x) ≡ filter P? xs
filterWith∈≗filter P? []       = refl
filterWith∈≗filter P? (x ∷ xs)
  with IH ← filterWith∈≗filter P? xs
  with P? x
... | yes px = cong (x ∷_) IH
... | no ¬px = IH

index∘subst : ∀ {x x′}{xs : List A}{x∈ : x ∈ xs} (eq : x ≡ x′)
  → index (subst (_∈ _) eq x∈) ≡ index x∈
index∘subst refl = refl

module _ (f : A → Maybe B) where
  mapMaybe-++ : ∀ xs ys → mapMaybe f (xs ++ ys) ≡ mapMaybe f xs ++ mapMaybe f ys
  mapMaybe-++ []       ys = refl
  mapMaybe-++ (x ∷ xs) ys with f x
  ... | just _  = cong (_ ∷_) (mapMaybe-++ xs ys)
  ... | nothing = mapMaybe-++ xs ys

  open L.Mem

  ∈-mapMaybe-++⁻ : ∀ xs {ys} {x : B}
    → x ∈ mapMaybe f (xs ++ ys)
    → x ∈ mapMaybe f xs
    ⊎ x ∈ mapMaybe f ys
  ∈-mapMaybe-++⁻ xs {ys} rewrite mapMaybe-++ xs ys = ∈-++⁻ _

  ∈-mapMaybe-++⁺ˡ : ∀ {xs ys} {x : B}
    → x ∈ mapMaybe f xs
    → x ∈ mapMaybe f (xs ++ ys)
  ∈-mapMaybe-++⁺ˡ {xs}{ys} rewrite mapMaybe-++ xs ys = ∈-++⁺ˡ

  ∈-mapMaybe-++⁺ʳ : ∀ xs {ys} {y : B}
    → y ∈ mapMaybe f ys
    → y ∈ mapMaybe f (xs ++ ys)
  ∈-mapMaybe-++⁺ʳ xs {ys} rewrite mapMaybe-++ xs ys = ∈-++⁺ʳ _

  --
  ∈-mapMaybe⁺ : x ∈ xs → f x ≡ just y → y ∈ mapMaybe f xs
  ∈-mapMaybe⁺ {x = x} {xs = xs} {y = y} x∈ eq
    = L.Any.mapMaybe⁺ f xs
    $ L.Any.map (λ where refl → subst (Any _) (sym eq) (just refl))
                (∈-map⁺ f x∈)

  ∈-mapMaybe⁻ : y ∈ mapMaybe f xs
              → ∃ λ x → (x ∈ xs) × (f x ≡ just y)
  ∈-mapMaybe⁻ {y = y} {xs = x ∷ xs} y∈
    with f x in fx≡
  ... | nothing = map₂ (map₁ there) (∈-mapMaybe⁻ y∈)
  ... | just y′
    with y∈
  ... | here refl = x , here refl , fx≡
  ... | there y∈′ = map₂ (map₁ there) (∈-mapMaybe⁻ y∈′)

  mapMaybe-⊆ : xs ⊆ˢ ys → mapMaybe f xs ⊆ˢ mapMaybe f ys
  mapMaybe-⊆ {xs = x ∷ xs} {ys = ys} xs⊆ fx∈ =
    let x , x∈ , fx≡ = ∈-mapMaybe⁻ fx∈
    in  ∈-mapMaybe⁺ (xs⊆ x∈) fx≡

-- * subsets/sublists

⊆⇒⊆ˢ : xs ⊆ ys → xs ⊆ˢ ys
⊆⇒⊆ˢ (_    ∷ʳ p) = there ∘ ⊆⇒⊆ˢ p
⊆⇒⊆ˢ (refl ∷ p)  = λ where
  (here refl) → here refl
  (there x∈)  → there (⊆⇒⊆ˢ p x∈)

⊆ˢ-tail : ∀ {z} → z ∉ xs → z ∷ xs ⊆ˢ z ∷ ys → xs ⊆ˢ ys
⊆ˢ-tail z∉ sub x∈ =
  L.Any.tail (lookup (¬Any⇒All¬ _ z∉) x∈ ∘ sym) (sub $ there x∈)

⊆ˢ-length : Unique xs → xs ⊆ˢ ys → length xs ≤ length ys
⊆ˢ-length {xs = []} {ys} uniq xs⊆ = z≤n
⊆ˢ-length {xs = x ∷ xs} {ys} (x∉xs ∷ uniq) xs⊆ =
  begin-strict length xs  ≤⟨ ⊆ˢ-length uniq xs⊆ys′ ⟩
               length ys′ <⟨ ≤-reflexive $ sym $ L.length-removeAt′ ys _ ⟩
               length ys  ∎
  where
  open Nat.≤-Reasoning

  x∈ys : x ∈ ys
  x∈ys = xs⊆ (here refl)

  ys′ = ys ─ x∈ys

  xs⊆ys′ : xs ⊆ˢ ys′
  xs⊆ys′ y∈ = ∈-─⁺ (L.All.lookup x∉xs y∈) x∈ys (xs⊆ $ there y∈)

-- * Fin lists

Fins = List ∘ Fin

module _ {n : ℕ} {x x′ : Fin (suc n)} (x≢ : x′ ≢ x) where
  ∈-punchOutʳ : ∀ {ys : Fins (suc n)}
    → (x∉ : x′ ∉ ys)
    → x ∈ ys
    → Fi.punchOut {n}{x′}{x} x≢
        ∈ mapWith∈ ys (λ {y} y∈ → Fi.punchOut {n}{x′}{y} λ where refl → x∉ y∈)
  ∈-punchOutʳ x∉ = λ where
    (here refl) → here refl
    (there p)   → there $ ∈-punchOutʳ (x∉ ∘ there) p

  ∈-punchOutˡ : ∀ {ys : Fins (suc n)}
    → (x∉ : x′ ∉ ys)
    → Fi.punchOut {n}{x′}{x} x≢
        ∈ mapWith∈ ys (λ {y} y∈ → Fi.punchOut {n}{x′}{y} λ where refl → x∉ y∈)
    → x ∈ ys
  ∈-punchOutˡ {ys = _ ∷ _} x∉ = λ where
    (here px) → here  $ Fi.punchOut-injective x≢ (λ where refl → x∉ $ here refl) px
    (there p) → there $ ∈-punchOutˡ (x∉ ∘ there) p

  ∈-punchOut : ∀ {ys : Fins (suc n)}
    → (x∉ : x′ ∉ ys)
    → (Fi.punchOut {n}{x′}{x} x≢
        ∈ mapWith∈ ys (λ {y} y∈ → Fi.punchOut {n}{x′}{y} λ where refl → x∉ y∈))
    ↔ (x ∈ ys)
  ∈-punchOut x∉ = ∈-punchOutˡ x∉ , ∈-punchOutʳ x∉

punchOut≡⇒index≡ : ∀ {n}{xs : Fins (suc n)}{x x′ x₀}{x∈ : x ∈ xs}{x∈′ : x′ ∈ xs}
  → Unique xs
  → (x≢ : L.All.All (x₀ ≢_) xs)
  → Fi.punchOut (lookup x≢ x∈) ≡ Fi.punchOut (lookup x≢ x∈′)
  → index x∈ ≡ index x∈′
punchOut≡⇒index≡ {n}{xs}{x}{x′}{x₀}{x∈}{x∈′} uxs x≢ eq = let open ≡-Reasoning in
  begin
    index x∈
  ≡⟨ cong index $ unique⇒irrelevant uxs x∈ _ ⟩
    index (subst (_∈ _) x≡ x∈′)
  ≡⟨ index∘subst x≡ ⟩
    index x∈′
  ∎
  where
  open import Data.List.Membership.Propositional.Properties.WithK
    using (unique⇒irrelevant)

  x≡ : x′ ≡ x
  x≡ = sym $ Fi.punchOut-injective (lookup x≢ x∈) (lookup x≢ x∈′) eq

-- * prefix (up to propositional equality)

Prefix≡ : List A → List A → Type _
Prefix≡ = Prefix _≡_

≡⇒Prefix : xs ≡ ys → Prefix≡ xs ys
≡⇒Prefix {xs = []}    {ys = []}    refl = []
≡⇒Prefix {xs = _ ∷ _} {ys = _ ∷ _} refl = refl ∷ ≡⇒Prefix refl

instance
  Dec-Prefix≡ : ⦃ DecEq A ⦄ → Prefix≡ {A = A} ⁇²
  Dec-Prefix≡ = ⁇ L.Pre.prefix? _≟_ _ _

Prefix⇒⊆ : Prefix≡ xs ys → xs ⊆ˢ ys
Prefix⇒⊆ (refl ∷ pre) = λ where
  (here refl) → here refl
  (there p)   → there (Prefix⇒⊆ pre p)

Prefix⇒All : ∀ {P : Pred A ℓ} → Prefix≡ xs ys → L.All.All P ys → L.All.All P xs
Prefix⇒All = L.SubS.All-resp-⊇ ∘ Prefix⇒⊆

Prefix-take : ∀ {n} → Prefix≡ (L.take n xs) xs
Prefix-take {xs = xs} {n = n} with n
... | zero  = []
... | suc _ with xs
... | []    = []
... | _ ∷ _ = refl ∷ Prefix-take

-- * suffix (up to propositional equality)

Suffix≡ : List A → List A → Type _
Suffix≡ = Suffix _≡_

≡⇒Suffix : xs ≡ ys → Suffix≡ xs ys
≡⇒Suffix = here ∘ L.PW.≡⇒Pointwise-≡

instance
  Dec-Suffix≡ : ⦃ DecEq A ⦄ → Suffix≡ {A = A} ⁇²
  Dec-Suffix≡ = ⁇ L.Suf.suffix? _≟_ _ _

Suffix⇒⊆ : Suffix≡ xs ys → xs ⊆ˢ ys
Suffix⇒⊆ (here eq) rewrite L.PW.Pointwise-≡⇒≡ eq = id
Suffix⇒⊆ (there p) = there ∘ Suffix⇒⊆ p

Suffix⇒All : ∀ {P : Pred A ℓ} → Suffix≡ xs ys → L.All.All P ys → L.All.All P xs
Suffix⇒All = L.SubS.All-resp-⊇ ∘ Suffix⇒⊆

Suffix-drop : ∀ n → Suffix≡ (L.drop n xs) xs
Suffix-drop zero = ≡⇒Suffix refl
Suffix-drop {xs = xs} (suc n) with xs
... | []    = here []
... | _ ∷ _ = there $′ Suffix-drop n

-- ** non-empty lists

nonEmpty∈ : length xs > 0 → ∃ (_∈ xs)
nonEmpty∈ {xs = _ ∷ _} _ = -, here refl

-- * intersection

module _ ⦃ _ : DecEq A ⦄ where
  infixr 7 _∩_
  _∩_ : Op₂ (List A)
  xs ∩ ys = filter (_∈? ys) xs

  ∈-∩⁻ : ∀ x xs ys → x ∈ (xs ∩ ys) → (x ∈ xs) × (x ∈ ys)
  ∈-∩⁻ _ _ _ = L.Mem.∈-filter⁻ (_∈? _)

  Unique-∩ : Unique xs → Unique (xs ∩ ys)
  Unique-∩ = L.Unique.filter⁺ (_∈? _)

  ∩-identityˡ : Null ([] ∩ xs)
  ∩-identityˡ = refl

  ∩-identityʳ : Null (xs ∩ [])
  ∩-identityʳ {xs} = L.filter-none _ {xs} $ L.All.tabulate λ where _ ()

length-∩ˡ : ∀ {n}{xs ys : Fins n}
  → length (xs ∩ ys) ≤ length xs
length-∩ˡ {xs = []} {ys} = z≤n
length-∩ˡ {xs = x ∷ xs} {ys}
  with x ∈? ys
... | no _ = let open ≤-Reasoning in
  begin length (xs ∩ ys) ≤⟨ length-∩ˡ {xs = xs} ⟩
        length xs        ≤⟨ n≤1+n _ ⟩
        1 + length xs    ∎
... | yes _ = let open ≤-Reasoning in
  begin 1 + length (xs ∩ ys) ≤⟨ +-mono-≤ ≤-refl $ length-∩ˡ {xs = xs} ⟩
        1 + length xs        ∎

length-unique-fin : ∀ {n}{xs : Fins n}
  → Unique xs
  → length xs ≤ n
length-unique-fin {xs = []} _ = z≤n
length-unique-fin {suc n} {x ∷ xs} (x≢ ∷ uxs)
  = s≤s $ let open ≤-Reasoning in
  begin
    length xs
  ≡˘⟨ length-mapWith∈ (Fi.punchOut ∘ lookup x≢) ⟩
    length xs′
  ≤⟨ length-unique-fin {xs = xs′} uxs′ ⟩
    n
  ∎
  where
  xs′ : Fins n
  xs′ = mapWith∈ xs (Fi.punchOut ∘ lookup x≢)

  uxs′ : Unique xs′
  uxs′ = Unique-mapWith∈ $ punchOut≡⇒index≡ uxs x≢

length-∩ : ∀ {n}{xs ys : Fins n}
  → Unique xs
  → Unique ys
  → length (xs ∩ ys) ≥ length xs + length ys ∸ n
length-∩ {n} {[]} {ys} _ uys = let open ≤-Reasoning in
  begin
    length ys ∸ n
  ≡⟨ m≤n⇒m∸n≡0 (length-unique-fin uys) ⟩
    0
  ∎
length-∩ {suc n} {x ∷ xs} {ys} (x≢ ∷ uxs) uys
  with IH ← length-∩ {suc n}{xs} uxs uys
  with x ∈? ys
... | yes x∈ = let open ≤-Reasoning in
  begin
    length xs + length ys ∸ n
  ≡⟨⟩
    (1 + (length xs + length ys)) ∸ suc n
  ≤⟨ +-∸-assoc≤ 1 {o = suc n} ⟩
    1 + (length xs + length ys ∸ suc n)
  ≤⟨ +-monoʳ-≤ 1 IH ⟩
    1 + length (xs ∩ ys)
  ∎
... | no x∉ = let open ≤-Reasoning in
  begin
    length xs + length ys ∸ n
  ≡˘⟨ cong (λ ◆ → ◆ + _ ∸ n) len≡-xs ⟩
    length xs′ + length ys ∸ n
  ≡˘⟨ cong (λ ◆ → length xs′ + ◆ ∸ n) len≡-ys ⟩
    length xs′ + length ys′ ∸ n
  ≤⟨ IH′ ⟩
    length (xs′ ∩ ys′)
  ≡⟨ len≡ ⟩
    length (xs ∩ ys)
  ∎
  where
  x↓ : {x : Fin (suc n)} → x ∈ xs → Fin n
  x↓ = Fi.punchOut ∘ lookup x≢

  xs′ : Fins n
  xs′ = mapWith∈ xs x↓

  uxs′ : Unique xs′
  uxs′ = Unique-mapWith∈ $ punchOut≡⇒index≡ uxs x≢

  len-xs′ : length xs′ ≤ n
  len-xs′ = length-unique-fin uxs′

  len≡-xs : length xs′ ≡ length xs
  len≡-xs = length-mapWith∈ x↓

  y↓ : {y : Fin (suc n)} → y ∈ ys → Fin n
  y↓ {y} y∈ = Fi.punchOut {i = x} {j = y} λ where refl → x∉ y∈

  ys′ : Fins n
  ys′ = mapWith∈ ys y↓

  uys′ : Unique ys′
  uys′ = Unique-mapWith∈ $ punchOut≡⇒index≡ uys (¬Any⇒All¬ ys x∉)

  len-ys′ : length ys′ ≤ n
  len-ys′ = length-unique-fin uys′

  len≡-ys : length ys′ ≡ length ys
  len≡-ys = length-mapWith∈ y↓

  IH′ : length (xs′ ∩ ys′) ≥ length xs′ + length ys′ ∸ n
  IH′ = length-∩ {n = n} uxs′ uys′

  len≡ : length (xs′ ∩ ys′) ≡ length (xs ∩ ys)
  len≡ = let open ≡-Reasoning in
    begin
      length (xs′ ∩ ys′)
    ≡⟨⟩
      length (filter (_∈? ys′) xs′)
    ≡⟨⟩
      length (filter (_∈? mapWith∈ ys y↓) $ mapWith∈ xs x↓)
    ≡⟨ filter∘mapWith∈ xs x↓ (_∈? mapWith∈ ys y↓) ⟩
      length (filterWith∈ xs ((_∈? mapWith∈ ys y↓) ∘ x↓))
    ≡⟨⟩
      length (filterWith∈ xs λ {x} x∈ → x↓ x∈ ∈? mapWith∈ ys y↓)
    ≡⟨ cong length
     $ filterWith∈≡
         xs
         (λ {x} x∈ → x↓ x∈ ∈? mapWith∈ ys y↓)
         (λ {x} _ → x ∈? ys)
         (λ {x} {x∈} → ∈-punchOut (lookup x≢ x∈) x∉)
     ⟩
      length (filterWith∈ xs λ {x} _ → x ∈? ys)
    ≡⟨ (cong length $ filterWith∈≗filter (_∈? ys) xs) ⟩
      length (filter (_∈? ys) xs)
    ≡⟨⟩
      length (xs ∩ ys)
    ∎

enumerate∈ : ∀ {A : Type} → (xs : List A) → List $ ∃ (_∈ xs)
enumerate∈ xs = mapWith∈ xs λ {x} x∈ → x , x∈

All-mapWith∈⁺ : ∀ {P : B → Type} {f : ∀ {x : A} → x ∈ xs → B} →
  All (λ (x , x∈) → P (f {x} x∈)) (enumerate∈ xs) →
  All P (mapWith∈ xs f)
All-mapWith∈⁺ {xs = []} [] = []
All-mapWith∈⁺ {xs = _ ∷ xs} {P = P} {f = f} (p ∷ ps)
  = p
  ∷ All-mapWith∈⁺ {xs = xs} (L.All.map⁻ ps′)
  where
  -- ps : All (λ (x , x∈) → P (f {x} x∈)) (mapWith∈ xs λ x → ? , there x)

  ps′ : L.All.All (λ (x , x∈) → P (f {x} x∈))
                  (map (λ (x , x∈) → x , there x∈) $ enumerate∈ xs)
  ps′ = subst
    (λ ◆ → L.All.All (λ (x , x∈) → P (f {x} x∈)) ◆)
    (sym $ L.Mem.map-mapWith∈ xs (λ {x} x∈ → x , x∈) (λ (x , x∈) → x , there x∈))
    ps

∈-mapWith∈⁻ : ∀ {xs : List A} {f : ∀ {x} → x ∈ xs → B} {y : B}
  → y ∈ mapWith∈ xs f
  → ∃ λ x → Σ (x ∈ xs) λ x∈ → y ≡ f {x} x∈
∈-mapWith∈⁻ {xs = x ∷ _}  (here refl) = x , here refl , refl
∈-mapWith∈⁻ {xs = x ∷ xs} (there p)   = let x , x∈ , y≡ = ∈-mapWith∈⁻ p in x , there x∈ , y≡

Unique-mapWith∈⁺ : ∀ {f : ∀ {x : A} → x ∈ xs → B} →
  (∀ {x y} (x∈ : x ∈ xs) (y∈ : y ∈ xs) → f x∈ ≡ f y∈ → x ≡ y) →
  Unique xs →
  Unique (mapWith∈ xs f)
Unique-mapWith∈⁺ {xs = []} f≡ uniq = []
Unique-mapWith∈⁺ {xs = x ∷ xs} {f = f} f≡ (x∉ ∷ uniq)
  = All-mapWith∈⁺ QED
  ∷ Unique-mapWith∈⁺ {xs = xs} (λ x∈ y∈ → f≡ (there x∈) (there y∈)) uniq
  where
  -- x∉ : All (x ≢_) xs

  QED : L.All.All (λ (y , y∈) → f {x} (here refl) ≢ (f {y} $ there y∈)) (enumerate∈ xs)
  QED = tabulate λ x∈ f∘there≡ → let _ , p , eq = ∈-mapWith∈⁻ x∈ in
    L.All.lookup x∉ (subst (λ ◆ → ◆ .proj₁ ∈ xs) (sym eq) p) $
      f≡ (here refl) (there _) f∘there≡

-- ** UniqueBy

UniqueBy : (A → B) → List A → Type
UniqueBy f = Unique ∘ map f

∉-─ : ∀ {A B : Type} {x : A} {xs} (f : A → B) →
  ∀ (x∈ : x ∈ xs)
  → UniqueBy f xs
  → x ∉ xs L.Mem.─ x∈
∉-─ {xs = _ ∷ xs} _ = λ where
  (here refl) (x∉ ∷ _)   x∈          → L.All.lookup x∉ (L.Mem.∈-map⁺ _ x∈) refl
  (there x∈)  (x∉ ∷ _)   (here refl) → L.All.lookup x∉ (L.Mem.∈-map⁺ _ x∈) refl
  (there x∈)  (_ ∷ uniq) (there p)   → ∉-─ {xs = xs} _ x∈ uniq p

-- ** nub (ported from omelkonian/formal-prelude)

module _ ⦃ _ : DecEq A ⦄ where

  nub : List A → List A
  nub [] = []
  nub (x ∷ xs) with x ∈? xs
  ... | yes _ = nub xs
  ... | no  _ = x ∷ nub xs

  nub-⊆⁺ : xs ⊆ˢ nub xs
  nub-⊆⁺ {xs = x ∷ xs} (here refl)
    with x ∈? xs
  ... | yes x∈ = nub-⊆⁺ {xs = xs} x∈
  ... | no  _  = here refl
  nub-⊆⁺ {xs = x ∷ xs} (there y∈)
    with x ∈? xs
  ... | yes _ = nub-⊆⁺ {xs = xs} y∈
  ... | no  _ = there $ nub-⊆⁺ {xs = xs} y∈

  nub-⊆⁻ : nub xs ⊆ˢ xs
  nub-⊆⁻ {xs = x ∷ xs}
    with x ∈? xs
  ... | yes x∈ = there ∘ nub-⊆⁻ {xs = xs}
  ... | no  _  = λ where
    (here refl) → here refl
    (there y∈)  → there $ nub-⊆⁻ {xs = xs} y∈

  All-nub⁺ : All P xs → All P (nub xs)
  All-nub⁺ {xs = []}     []       = []
  All-nub⁺ {xs = x ∷ xs} (p ∷ ps) with x ∈? xs
  ... | yes _ = All-nub⁺ ps
  ... | no  _ = p ∷ All-nub⁺ ps

  Unique-nub : Unique (nub xs)
  Unique-nub {[]} = []
  Unique-nub {x ∷ xs} with x ∈? xs
  ... | yes _ = Unique-nub {xs}
  ... | no x∉ = All-nub⁺ (¬Any⇒All¬ xs x∉) ∷ Unique-nub {xs}

  nub-filter : {P : A → Set} (P? : Decidable¹ P) → nub (filter P? xs) ≡ filter P? (nub xs)
  nub-filter {xs = []} P? = refl
  nub-filter {xs = x ∷ xs} P?
    with P? x | x ∈? xs
  ... | no _  | yes _ = nub-filter {xs = xs} P?
  ... | no ¬p | no _
    rewrite L.filter-reject P? {x}{nub xs} ¬p
    = nub-filter {xs = xs} P?
  ... | yes p | no x∉
    rewrite L.filter-accept P? {x}{nub xs} p
    with x ∈? filter P? xs
  ... | yes x∈ = ⊥-elim (x∉ (proj₁ $ L.Mem.∈-filter⁻ P? x∈ ))
  ... | no _ = cong (x ∷_) $ nub-filter {xs = xs} P?
  nub-filter {xs = x ∷ xs} P? | yes p | yes x∈ with x ∈? filter P? xs
  ... | yes _ = nub-filter {xs = xs} P?
  ... | no x∉ = ⊥-elim $ x∉ (L.Mem.∈-filter⁺ P? x∈ p)

  nub-length : length (nub xs) ≤ length (nub (x ∷ xs))
  nub-length {xs}{x} with x ∈? xs
  ... | yes _ = ≤-refl
  ... | no _ = n≤1+n _

-- ** nubBy

  -- NB: right-biased, e.g. nubBy ∣_∣ [-1,0,1] = [0,1]
  nubBy : (B → A) → List B → List B
  nubBy f [] = []
  nubBy f (x ∷ xs) with f x ∈? map f xs
  ... | yes _ = nubBy f xs
  ... | no  _ = x ∷ nubBy f xs

  module _ (f : B → A) where
    nubBy-⊆⁻ : nubBy f xs ⊆ˢ xs
    nubBy-⊆⁻ {xs = y ∷ xs} x∈ with f y ∈? map f xs
    ... | yes _ = there (nubBy-⊆⁻ {xs = xs} x∈)
    ... | no  _ with x∈
    ... | here refl = here refl
    ... | there x∈′ = there (nubBy-⊆⁻ {xs = xs} x∈′)

    nubBy-⊆⁺ : map f xs ⊆ˢ map f (nubBy f xs)
    nubBy-⊆⁺ {xs = y ∷ xs} (here refl)
      with f y ∈? map f xs
    ... | yes fy∈ = nubBy-⊆⁺ {xs = xs} fy∈
    ... | no  _   = here refl
    nubBy-⊆⁺ {xs = y ∷ xs} (there x∈)
      with f y ∈? map f xs
    ... | yes fy∈ = nubBy-⊆⁺ x∈
    ... | no  _   = there (nubBy-⊆⁺ x∈)

    UniqueBy-nubBy : ∀ xs → UniqueBy f (nubBy f xs)
    UniqueBy-nubBy [] = []
    UniqueBy-nubBy (x ∷ xs) with f x ∈? map f xs
    ... | yes _  = UniqueBy-nubBy xs
    ... | no fx∉ = ¬Any⇒All¬ (map f (nubBy f xs)) (fx∉ ∘ L.SubS.map⁺ _ nubBy-⊆⁻)
                 ∷ UniqueBy-nubBy xs

++-injectiveʳ : ∀ {xs ys zs : List A} →
  xs ++ ys ≡ xs ++ zs
  ────────────────────
  ys ≡ zs
++-injectiveʳ {xs = []}    = id
++-injectiveʳ {xs = _ ∷ _} = ++-injectiveʳ ∘ L.∷-injectiveʳ
