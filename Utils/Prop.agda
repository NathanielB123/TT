{-# OPTIONS --prop --rewriting #-}


module Utils.Prop where

import Agda.Builtin.Equality.Rewrite

open import Utils 
  using (ℓ; ℓ₁; ℓ₂; refl; Σ; fst; snd; _,_; 𝟙; ⟨⟩
        ; Bool; tt; ff; 𝟘; _×_; _⊔l_; Dec; yes; no; _＋_; inl; inr) 
  renaming (_≡_ to _≡S_; coe to coeS)
  public

infixr 3 Σ-syntax Σᴾ-syntax
infix 4 _≡_
infix 4 _≡[_]≡_
infixr 2 step-≡-⟩  step-≡-∣
infix 3 _∎
infix 5 ↑≡_
infixr 5 _∙_

infixr 4 _∧,_

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = x ∶ A × B

record Σᴾ (P : Prop ℓ₁) (Q : P → Prop ℓ₂) : Prop (ℓ₁ ⊔l ℓ₂) where
  constructor _∧,_
  field
    fstᴾ : P
    sndᴾ : Q fstᴾ

Σᴾ-syntax = Σᴾ
syntax Σᴾ-syntax P (λ p → Q) = p ∶ P ∧ Q

infix 4 _∧_
_∧_ : Prop ℓ₁ → Prop ℓ₂ → Prop (ℓ₁ ⊔l ℓ₂)
P ∧ Q = p ∶ P ∧ Q

data _≡_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ x

module UtilVars where variable
  A B C D E A₁ A₂ : Set ℓ
  x y z x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ w₁ w₂ : A
  p q r p₁ p₂ q₁ q₂ : x ≡ y
  x₁₂ x₂₃ x₁₃ x₂₁ : x₁ ≡ x₂
  f g h : A → B
open UtilVars

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

ap₂ : (f : A → B → C) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
ap₂ f refl refl = refl

sym : x ≡ y → y ≡ x
sym refl = refl

_∙_ : x ≡ y → y ≡ z → x ≡ z
refl ∙ p = p

step-≡-⟩ : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
step-≡-⟩ x q p = p ∙ q

step-≡-∣ : ∀ x {y : A} → x ≡ y → x ≡ y
step-≡-∣ x p = p

_∎ : ∀ (x : A) → x ≡ x
x ∎ = refl

syntax step-≡-⟩ x q p = x ≡⟨ p ⟩ q
syntax step-≡-∣ x p   = x ≡⟨⟩ p

-- -- Subsingleton elimination for propositional identity (consistent with K)
postulate
  ↑≡_ : x ≡ y → x ≡S y
  ↑≡-refl : ↑≡ refl {x = x} ≡S refl
  {-# REWRITE ↑≡-refl #-}

↓≡_ : x ≡S y → x ≡ y
↓≡ refl = refl

coe : A ≡ B → A → B
coe p x = coeS (↑≡ p) x

tr : (P : A → Set ℓ) → x₁ ≡ x₂ → P x₁ → P x₂
tr P p d = coe (ap P p) d

record _≡[_]≡_ {A B : Set ℓ} (x : A) (p : A ≡ B) (y : B) : Prop ℓ where
  constructor coe[]
  field
    []coe : coe p x ≡ y
open _≡[_]≡_ public

pattern refl[] = coe[] refl

apd : ∀ {B : A → Set ℓ} (f : (x : A) → B x) {x y}
    → (p : x ≡ y) → f x ≡[ ap B p ]≡ f y
apd f refl = refl[]

apd₂ : ∀ {B : A → Set ℓ}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
     → (p : x₁ ≡ x₂) → y₁ ≡[ ap B p ]≡ y₂
     → f x₁ y₁ ≡ f x₂ y₂
apd₂ f refl refl[] = refl

apd₃ : ∀ {B : A → Set ℓ₁} {C : A → Set ℓ₂}
         (f : (x : A) → B x → C x → D) {x₁ x₂ y₁ y₂ z₁ z₂}
     → (p : x₁ ≡ x₂) 
     → y₁ ≡[ ap B p ]≡ y₂
     → z₁ ≡[ ap C p ]≡ z₂
     → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
apd₃ f refl refl[] refl[] = refl

[]sym : ∀ {B : A → Set ℓ} {y₁ y₂}
      → y₁ ≡[ ap B (sym x₂₁) ]≡ y₂
      → y₂ ≡[ ap B x₂₁ ]≡ y₁
[]sym {x₂₁ = refl} y₁₂ .[]coe = sym (y₁₂ .[]coe)

sym[] : ∀ {B : A → Set ℓ} {y₁ y₂}
      → y₁ ≡[ ap B x₁₂ ]≡ y₂
      → y₂ ≡[ ap B (sym x₁₂) ]≡ y₁
sym[] {x₁₂ = refl} y₁₂ .[]coe = sym (y₁₂ .[]coe)

happly : {B : A → Set ℓ} {f g : ∀ x → B x} → f ≡ g → f x ≡ g x
happly refl = refl

happly₂ : ∀ {B : A → Set ℓ₁} {C : ∀ x → B x → Set ℓ₂} {y} 
            {f g : ∀ x → (y : B x) → C x y} 
        → f ≡ g → f x y ≡ g x y
happly₂ p = happly (happly p)

postulate
  funext : {B : A → Set ℓ} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
  
funexti : {B : A → Set ℓ} {f g : {x : A} → B x} → (∀ {x} → f {x} ≡ g {x}) 
        → _≡_ {A = {x : A} → B x} f g
funexti {f = f} {g = g} p = ap (λ f {x} → f x) (funext (λ _ → p))

piext : {B₁ B₂ : A → Set ℓ} → (∀ x → B₁ x ≡ B₂ x) → (∀ x → B₁ x) ≡ (∀ x → B₂ x)
piext p = ap (λ □ → ∀ x → □ x) (funext p)

piexti : {B₁ B₂ : A → Set ℓ} → (∀ {x} → B₁ x ≡ B₂ x) 
       → (∀ {x} → B₁ x) ≡ (∀ {x} → B₂ x)
piexti p = ap (λ □ → ∀ {x} → □ {x}) (funexti p)

piext[] : {B₁ : A₁ → Set ℓ} {B₂ : A₂ → Set ℓ} (A≡ : A₁ ≡ A₂) 
        → (∀ {x₁ x₂} (x≡ : x₁ ≡[ A≡ ]≡ x₂) → B₁ x₁ ≡ B₂ x₂) 
        → (∀ x → B₁ x) ≡ (∀ x → B₂ x)
piext[] refl p = piext λ x → p refl[]

record Lift (P : Prop ℓ) : Set ℓ where
  constructor lift
  field
    lower : P
open Lift public

data Decᴾ (P : Prop ℓ) : Set ℓ where
  yes : P → Decᴾ P
  no  : (P → 𝟘) → Decᴾ P
