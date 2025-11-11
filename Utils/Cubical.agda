{-# OPTIONS --cubical #-}

module Utils.Cubical where

open import Level using (Level) renaming (suc to suℓ; zero to 0ℓ)
  public
open import Cubical.Core.Primitives using (Σ; _,_; fst; snd; _[_↦_]; inS; outS)
  public
open import Cubical.Foundations.Function using (_∘_; idfun)
  public
open import Cubical.Foundations.Prelude using 
  ( refl; _≡_; PathP; subst; _∙_; sym; cong; congP; hcomp; hfill
  ; i0; i1; transp; toPathP; fromPathP; ~_; I; transport-filler; funExt
  ; symP; step-≡; _≡⟨_⟩≡⟨_⟩_; _≡⟨⟩_; _∎; isContr; isProp; isSet; inS; fill
  ; _∧_; _∨_; IsOne; Sub; comp; transportRefl; Partial)
  renaming (transport to coe)
  public
open import Cubical.Foundations.HLevels 
  using (hProp; hSet; isSetΣ; isSetΠ; isOfHLevelLift)
  public
open import Cubical.Foundations.Isomorphism using 
  (isIso; isoToEquiv; Iso; isIsoToIsEquiv)
  public
open import Cubical.Foundations.Univalence using (ua; unglue; Glue)
  public
open import Cubical.Foundations.Equiv using (isEquiv)
  public

infix 4 _≡[_]≡_

_≡[_]≡_ : ∀ {a} {A B : Set a} → A → A ≡ B → B → Set a
x ≡[ eq ]≡ y = PathP (λ i → eq i) x y

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- TODO: Find a nicer abstraction here
toi0 : ∀ {A B : Set ℓ} (p : A ≡ B) (i : I) → p i ≡ A
toi0 p i j = p (i ∧ ~ j)

coei0 :  ∀ {A B : Set ℓ} (p : A ≡ B) (i : I) → p i → A
coei0 p i = coe (toi0 p i)

private variable
  A B : Set

-- Cubical primitives with properly documented side conditions (and 
-- computational behaviour on |φ = i1|)

transp' : ∀ (φ : I) {B : Set [ φ ↦ (λ _ → A) ]} 
            (p : (A ≡ outS B) [ φ ↦ (λ where (φ = i1) → refl) ])
        → A → outS B
transp' φ p x = transp (λ i → outS p i) φ x


transp'' : ∀ (φ : I) {B : Set [ φ ↦ (λ _ → A) ]} 
             (p : (A ≡ outS B) [ φ ↦ (λ where (φ = i1) → refl) ])
         → (A → outS B) [ φ ↦ (λ where (φ = i1) x → x) ]
transp'' φ {B = B} p = inS (transp' φ {B = B} p)

hcomp' : ∀ {φ : I} (x : I → Partial φ A) → A [ φ ↦ x i0 ] → A
hcomp' x y = hcomp x (outS y)

hcomp'' : ∀ {φ : I} (x : I → Partial φ A) → A [ φ ↦ x i0 ] → A [ φ ↦ x i1 ]
hcomp'' x y = inS (hcomp' x y)

comp' : ∀ (p : A ≡ B) {φ : I}
          (x : ∀ (i : I) → Partial φ (p i)) 
      → p i0 [ φ ↦ x i0 ] → p i1
comp' p x y = comp (λ i → p i) x (outS y)

comp'' : ∀ (p : A ≡ B) {φ : I}
           (x : ∀ (i : I) → Partial φ (p i)) 
       → p i0 [ φ ↦ x i0 ] → p i1 [ φ ↦ x i1 ]
comp'' p x y = inS (comp' p x y)

