{-# OPTIONS --cubical-compatible #-}

module Utils where

open import Level using (Level)

open import Relation.Binary.PropositionalEquality as EQ
  using (_≡_; refl; erefl; sym; subst-application′)
  renaming 
    (trans to infixr 4 _∙_; J to ≡-elim
    ; cong to ap; cong-app to happly; cong₂ to ap₂
    ; sym-cong to sym-ap)
  public
open EQ.≡-Reasoning using (begin_; step-≡-⟩; step-≡-∣; step-≡-⟨; _∎) public
open import Data.Unit using () renaming (⊤ to 𝟙; tt to ⟨⟩) public
open import Data.Bool using (Bool) renaming (true to tt; false to ff) public
open import Data.Empty using () renaming (⊥ to 𝟘; ⊥-elim to absurd) public
open import Data.Product using (Σ; _,_) renaming (proj₁ to fst; proj₂ to snd)
  public

infix 4 _≡[_]≡_

variable
  ℓ ℓ₁ ℓ₂ : Level

module UtilVars where variable
  A B C : Set ℓ
  x y z x₁ x₂ x₃ : A
  p q r : x ≡ y
  x₁₂ x₂₃ x₁₃ : x₁ ≡ x₂
open UtilVars

coe : A ≡ B → A → B
coe refl x = x

-- We ensure |transp| is defeq to |coe ap| to make |_≡[_]≡_| nicer
-- The downside is that we have to redefine all utilities from the stdlib 
-- that refer to |transp|/|subst|
transp : (P : A → Set ℓ) (p : x ≡ y) → P x → P y
transp P p d = coe (ap P p) d

{-# DISPLAY coe (ap P p) = transp P p #-}

_≡[_]≡_ : A → A ≡ B → B → Set _
x ≡[ p ]≡ y = coe p x ≡ y

apd : ∀ {B : A → Set ℓ} (f : (x : A) → B x) {x y}
    → (p : x ≡ y) → f x ≡[ ap B p ]≡ f y
apd f refl = refl

apd₂ : ∀ {B : A → Set ℓ}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
     → (p : x₁ ≡ x₂) → y₁ ≡[ ap B p ]≡ y₂
     → f x₁ y₁ ≡ f x₂ y₂
apd₂ f refl refl = refl

-- I don't think this is actually very useful because we can't do much with 
-- |coe (apd₂ _ _ _)|
-- apd₂′ : ∀ {B : A → Set ℓ₁} {C : ∀ x → B x → Set ℓ₂}
--           (f : ∀ x y → C x y) {y₁ y₂} 
--           (p : x₁ ≡ x₂) (q : y₁ ≡[ ap B p ]≡ y₂)
--        → f x₁ y₁ ≡[ apd₂ C p q ]≡ f x₂ y₂
-- apd₂′ f refl refl = refl

-- |subst-application′| in the stdlib
-- Intuitively, this is just composition of a path with a binary dependent 
-- function
apd₂′ : ∀ (B : A → Set ℓ₁) {C : A → Set ℓ₂} {y : B x₁}
          (f : ∀ x → B x → C x) (eq : x₁ ≡ x₂) 
       → f x₁ y ≡[ ap C eq ]≡ f x₂ (transp B eq y)
apd₂′ B f refl = refl

extTransp : ∀ (x₁₂ : x₁ ≡ x₂) {B : A → Set ℓ} {y₁ y₂}
          → y₁ ≡[ ap B x₁₂ ]≡ y₂
          → y₁ ≡[ ap B (x₁₂ ∙ x₂₃) ]≡ transp B x₂₃ y₂
extTransp {x₂₃ = refl} refl y₁₂ = y₁₂

sym[] : ∀ {B : A → Set ℓ} {y₁ y₂}
      → y₁ ≡[ ap B x₁₂ ]≡ y₂
      → y₂ ≡[ ap B (sym x₁₂) ]≡ y₁
sym[] {x₁₂ = refl} = sym

-- We keep |D| and |f| separate here because |ap-ap| does not compute
-- judgementally
ap[] : ∀ {C : A → Set ℓ₁} (D : B → Set ℓ₂) {y₁ y₂} 
         {f : A → B} (g : ∀ x → C x → D (f x))
     → y₁ ≡[ ap C x₁₂ ]≡ y₂
     → g x₁ y₁ ≡[ ap D (ap f x₁₂) ]≡ g x₂ y₂
ap[] {x₁₂ = refl} D g y₁₂ = ap (g _) y₁₂

