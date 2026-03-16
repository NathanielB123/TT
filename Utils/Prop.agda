{-# OPTIONS --prop --rewriting #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils

module Utils.Prop where

infix 4 _≡ᴾ_

open UtilVars

private variable 
  P Q : Prop _

record ∃ (A : Set ℓ₁) (P : A → Prop ℓ₂) : Set (ℓ₁ ⊔l ℓ₂) where
  constructor _∃,_
  field
    fst : A
    snd : P fst
open ∃

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

data _≡ᴾ_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ᴾ x

symᴾ : x ≡ᴾ y → y ≡ᴾ x
symᴾ refl = refl

transpᴾ : (P : A → Prop ℓ) → x₁ ≡ᴾ x₂ → P x₁ → P x₂
transpᴾ P refl d = d

-- Subsingleton elimination for propositional identity (consistent with K)
postulate
  ↑≡ : x ≡ᴾ y → x ≡ y
  ↑≡-refl : ↑≡ (refl {x = x}) ≡ refl
  {-# REWRITE ↑≡-refl #-}
