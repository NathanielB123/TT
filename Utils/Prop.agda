{-# OPTIONS --prop --rewriting #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils

module Utils.Prop where

infix 4 _≡ᴾ_

open UtilVars

data _≡ᴾ_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ᴾ x

apᴾ : (f : A → B) → x ≡ᴾ y → f x ≡ᴾ f y
apᴾ f refl = refl

symᴾ : x ≡ᴾ y → y ≡ᴾ x
symᴾ refl = refl

_∙ᴾ_ : x ≡ᴾ y → y ≡ᴾ z → x ≡ᴾ z
refl ∙ᴾ p = p

transpᴾ : (P : A → Prop ℓ) → x₁ ≡ᴾ x₂ → P x₁ → P x₂
transpᴾ P refl d = d

-- Subsingleton elimination for propositional identity (consistent with K)
postulate
  ↑≡ : x ≡ᴾ y → x ≡ y
  ↑≡-refl : ↑≡ (refl {x = x}) ≡ refl
  {-# REWRITE ↑≡-refl #-}

↓≡ : x ≡ y → x ≡ᴾ y
↓≡ refl = refl

coeᴾ : A ≡ᴾ B → A → B
coeᴾ p x = coe (↑≡ p) x

-- Some more Prop utils (unused)
{-
infix 4 _≡[_]≡ᴾ_

private variable 
  P Q : Prop _

record ∃ (A : Set ℓ₁) (P : A → Prop ℓ₂) : Set (ℓ₁ ⊔l ℓ₂) where
  constructor _∃,_
  field
    fst : A
    snd : P fst
open ∃ public

record Σᴾ (P : Prop ℓ₁) (Q : P → Prop ℓ₂) : Prop (ℓ₁ ⊔l ℓ₂) where
  constructor _Σ,_
  field
    fst : P
    snd : Q fst
open Σᴾ public

data ⊥ : Prop where

absurd⊥ : ⊥ → A
absurd⊥ ()

absurdᴾ : ⊥ → P
absurdᴾ ()

∃≡ : {P : A → Prop ℓ} {x y : ∃ A P} → x .fst ≡ y .fst → x ≡ y
∃≡ refl = refl

record ⊤ : Prop where

data Decᴾ (A : Set ℓ) : Set ℓ where
  yes : A       → Decᴾ A
  no  : (A → ⊥) → Decᴾ A

record _≡[_]≡ᴾ_ {A B : Set ℓ} (x : A) (p : A ≡ᴾ B) (y : B) : Prop ℓ where
  constructor coe[]
  field
    []coe : coeᴾ p x ≡ᴾ y
open _≡[_]≡ᴾ_ public
-}