{-# OPTIONS --safe #-}
open import Prelude.Init
open import Prelude.Initial
open import Prelude.InferenceRules

module Prelude.Closures {A : Type ℓ} (_—→_ : Rel A ℓ) where

private variable x y z : A

-- left-biased
infix  3 _∎
infixr 2 _—→⟨_⟩_ _—↠⟨_⟩_
infix  1 begin_; pattern begin_ x = x
infix -1 _—↠_

data _—↠_ : Rel A ℓ where
  _∎ : ∀ x → x —↠ x
  _—→⟨_⟩_ : ∀ x → x —→ y → y —↠ z → x —↠ z

—↠-trans : Transitive _—↠_
—↠-trans (x ∎) xz = xz
—↠-trans (_ —→⟨ r ⟩ xy) yz = _ —→⟨ r ⟩ —↠-trans xy yz

_—↠⟨_⟩_ : ∀ x → x —↠ y → y —↠ z → x —↠ z
_—↠⟨_⟩_ _ = —↠-trans

-- right-biased view
_←—_ = flip _—→_

-- infix  3 _∎
infixr 2 _⟨_⟩←—_
infix -1 _←—_ _↞—_ _⁺↞—_
data _↞—_ : Rel A ℓ where
  _∎ : ∀ x → x ↞— x
  _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ↞— x
data _⁺↞—_ : Rel A ℓ where
  _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ⁺↞— x

pattern _⟨_∣_⟩←—_ z z←y y y↞x = _⟨_⟩←—_ {y = y} z z←y y↞x

↞—-trans : Transitive _↞—_
↞—-trans (x ∎) xz = xz
↞—-trans (_ ⟨ r ⟩←— zy) yx = _ ⟨ r ⟩←— ↞—-trans zy yx

_⟨_⟩↞—_ : ∀ z → z ↞— y → y ↞— x → z ↞— x
_⟨_⟩↞—_ _ = ↞—-trans

-- view correspondence
infixr 2 _`—→⟨_⟩_
_`—→⟨_⟩_ : ∀ x → y ←— x → z ↞— y → z ↞— x
_ `—→⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
_ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

viewLeft : x —↠ y → y ↞— x
viewLeft (_ ∎)          = _ ∎
viewLeft (_ —→⟨ st ⟩ p) = _ `—→⟨ st ⟩ viewLeft p

infixr 2 _`⟨_⟩←—_
_`⟨_⟩←—_ : ∀ z → y —→ z → x —↠ y → x —↠ z
_ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
_ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

viewRight : y ↞— x → x —↠ y
viewRight (_ ∎)          = _ ∎
viewRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— viewRight p

view↔ : (x —↠ y) ↔ (y ↞— x)
view↔ = viewLeft , viewRight

--
⟨∣⟩←-inj : ∀{y′ : A}{z← : z ←— y}{←x : y ↞— x}{z←′ : z ←— y′}{←x′ : y′ ↞— x} →
    _≡_ {A = z ↞— x } (z ⟨ z← ∣ y ⟩←— ←x) (z ⟨ z←′ ∣ y′ ⟩←— ←x′)
  → Σ (y ≡ y′) λ where refl →  z← ≡ z←′ × ←x ≡ ←x′
  -- → (y , z← , ←x) ≡ (y′ , z←′ , ←x′)
⟨∣⟩←-inj refl = refl , refl , refl

factor : ∀{w} →
   (y←x : y ↞— x) →
   (z←y : z ↞— y) →
   (w←x : w ↞— x) →
   (z←w : z ↞— w) →
   ↞—-trans z←y y←x ≡ ↞—-trans z←w w←x →
   (y ↞— w) ⊎ (w ↞— y)
factor y←x (_ ∎) w←x z←w eq = inj₁ z←w
factor y←x z←y w←x (_ ∎) eq = inj₂ z←y
factor y←x (_ ⟨ z←y′ ⟩←— z←y) w←x (_ ⟨ z←w′ ⟩←— z←w) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = factor y←x z←y w←x z←w eq

factor⁺ : ∀ {≪y ≫y ≪w ≫w} →
   (y←x : ≪y ↞— x) →
   (y←y : ≫y ←— ≪y) →
   (z←y : z  ↞— ≫y) →

   (w←x : ≪w ↞— x) →
   (w←w : ≫w ←— ≪w) →
   (z←w : z  ↞— ≫w) →

   ↞—-trans z←y (_ ⟨ y←y ⟩←— y←x) ≡ ↞—-trans z←w (_ ⟨ w←w ⟩←— w←x) →

   ((≪y , ≫y , y←y) ≡ (≪w , ≫w , w←w)) ⊎ (≪y ↞— ≫w) ⊎ (≪w ↞— ≫y)

factor⁺ y←x y←y (_ ∎) w←x w←w (_ ∎) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = inj₁ refl
factor⁺ y←x y←y (_ ∎) w←x w←w (_ ⟨ _ ⟩←— z←w) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = inj₂ (inj₁ z←w)
factor⁺ y←x y←y (_ ⟨ _ ⟩←— z←y) w←x w←w (_ ∎) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = inj₂ (inj₂ z←y)
factor⁺ y←x y←y (_ ⟨ z←y′ ⟩←— z←y) w←x w←w (_ ⟨ z←w′ ⟩←— z←w) eq
  with refl , refl , eq ← ⟨∣⟩←-inj eq
  = factor⁺ y←x y←y z←y w←x w←w z←w eq

-- property preservation
StepPreserved′ : Rel (Pred A ℓ) _
StepPreserved′ P Q = ∀ {s s′} →
  ∙ s —→ s′
  ∙ P s
    ───────
    Q s′

StepPreserved : Pred (Pred A ℓ) _
StepPreserved P = StepPreserved′ P P

StepPreservedSt : Rel (Pred A ℓ) _
StepPreservedSt P Q = StepPreserved′ (P ∩¹ Q) P

-- well-rooted traces
module _ ⦃ _ : HasInitial A ⦄ where
  Reachable : Pred A _
  Reachable s = ∃ λ s₀ → Initial s₀ × (s ↞— s₀)

  Reachable-inj : ∀ {s s₀} {init init′ : Initial s₀}{tr tr′ : s ↞— s₀} →
    ∙ _≡_ {A = Reachable s} (s₀ , init , tr) (s₀ , init′ , tr′)
      ─────────────────────────────────────────────────────────
      tr ≡ tr′
  Reachable-inj refl = refl

  Invariant : Pred (Pred A ℓ) _
  Invariant = Reachable ⊆¹_

  -- invariance through step preservation
  module _ {P} (initP : Initial ⊆¹ P) (stepP : StepPreserved P) where
    Step⇒Invariant : Invariant P
    Step⇒Invariant = λ where
      (_ , init , (_ ∎)) → initP init
      (_ , init , (_ ⟨ step ⟩←— p)) → stepP step $ Step⇒Invariant (_ , init , p)

  -- reachability-indexed properties
  Trace = ∃ Reachable

  TraceProperty  = Trace → Type

  TraceInvariant : Pred (Pred Trace ℓ) _
  TraceInvariant P = ∀ {s} (Rs : Reachable s) → P (-, Rs)
