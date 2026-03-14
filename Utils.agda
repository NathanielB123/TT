{-# OPTIONS --cubical-compatible #-}

module Utils where

open import Agda.Primitive renaming (_⊔_ to _⊔l_) public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Unit renaming (⊤ to 𝟙; tt to ⟨⟩) public
open import Agda.Builtin.Bool renaming (true to tt; false to ff) public

infix 4 _≡[_]≡_
infixr 2 step-≡-⟩  step-≡-∣
infix 3 _∎
infixr 5 _∙_

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

module UtilVars where variable
  A B C A₁ A₂ : Set ℓ
  x y z x₁ x₂ x₃ y₁ y₂ y₃ : A
  p q r : x ≡ y
  x₁₂ x₂₃ x₁₃ x₂₁ : x₁ ≡ x₂
open UtilVars

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

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

J : (P : ∀ y → x ≡ y → Set ℓ) (p : x ≡ y) → P x refl → P y p
J P refl d = d

data 𝟘 : Set where

absurd : .𝟘 → A
absurd ()

coe : A ≡ B → A → B
coe refl x = x

-- We ensure |transp| is defeq to |coe ap| to make |_≡[_]≡_| nicer
-- The downside is that we have to redefine all utilities from the stdlib 
-- that refer to |transp|/|subst|
transp : (P : A → Set ℓ) (p : x ≡ y) → P x → P y
transp P p d = coe (ap P p) d

{-# DISPLAY coe (ap P p) = transp P p #-}

happly : {B : A → Set ℓ} {f g : ∀ x → B x} → f ≡ g → f x ≡ g x
happly refl = refl

happly₂ : ∀ {B : A → Set ℓ₁} {C : ∀ x → B x → Set ℓ₂} {y} 
            {f g : ∀ x → (y : B x) → C x y} 
        → f ≡ g → f x y ≡ g x y
happly₂ p = happly (happly p)

record _≡[_]≡_ {A B : Set ℓ} (x : A) (p : A ≡ B) (y : B) : Set ℓ where
  constructor coe[]
  field
    []coe : coe p x ≡ y
open _≡[_]≡_ public

pattern refl[] = coe[] refl

transp-sym : {P : A → Set ℓ} {y : P x₁} (p : x₂ ≡ x₁)
           → transp P p (transp P (sym p) y) ≡ y
transp-sym refl = refl

sym-transp : {P : A → Set ℓ} {y : P x₁} (p : x₁ ≡ x₂)
           → transp P (sym p) (transp P p y) ≡ y
sym-transp refl = refl

transp-sym[] : {P : A → Set ℓ} {y : P x}
             → transp P (sym p) y ≡[ ap P p ]≡ y
transp-sym[] {p = p} = coe[] (transp-sym p)

sym-transp[] : {P : A → Set ℓ} {y : P x}
             → transp P p y ≡[ ap P (sym p) ]≡ y
sym-transp[] {p = p} = coe[] (sym-transp p)

coe-coe : coe p (coe q x) ≡ coe (q ∙ p) x
coe-coe {q = refl} = refl

ap₂ : (f : A → B → C) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
ap₂ f refl refl = refl

apd : ∀ {B : A → Set ℓ} (f : (x : A) → B x) {x y}
    → (p : x ≡ y) → f x ≡[ ap B p ]≡ f y
apd f refl = refl[]

apd₂ : ∀ {B : A → Set ℓ}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
     → (p : x₁ ≡ x₂) → y₁ ≡[ ap B p ]≡ y₂
     → f x₁ y₁ ≡ f x₂ y₂
apd₂ f refl refl[] = refl

-- |subst-application′| in the stdlib
-- Intuitively, this is just composition of a path with a binary dependent 
-- function
apdd₂ : ∀ (B : A → Set ℓ₁) {C : A → Set ℓ₂} {y : B x₁}
          (f : ∀ x → B x → C x) (eq : x₁ ≡ x₂) 
       → f x₁ y ≡[ ap C eq ]≡ f x₂ (transp B eq y)
apdd₂ B f refl = refl[]

extTransp : ∀ (x₁₂ : x₁ ≡ x₂) {B : A → Set ℓ} {y₁ y₂}
          → y₁ ≡[ ap B x₁₂ ]≡ y₂
          → y₁ ≡[ ap B (x₁₂ ∙ x₂₃) ]≡ transp B x₂₃ y₂
extTransp {x₂₃ = refl} refl y₁₂ = y₁₂

sym[] : ∀ {B : A → Set ℓ} {y₁ y₂}
      → y₁ ≡[ ap B x₁₂ ]≡ y₂
      → y₂ ≡[ ap B (sym x₁₂) ]≡ y₁
sym[] {x₁₂ = refl} y₁₂ .[]coe = sym (y₁₂ .[]coe)

[]sym : ∀ {B : A → Set ℓ} {y₁ y₂}
      → y₁ ≡[ ap B (sym x₂₁) ]≡ y₂
      → y₂ ≡[ ap B x₂₁ ]≡ y₁
[]sym {x₂₁ = refl} y₁₂ .[]coe = sym (y₁₂ .[]coe)

-- We keep |D| and |f| separate here because |ap-ap| does not reduce
ap[] : ∀ {C : A → Set ℓ₁} (D : B → Set ℓ₂) {y₁ y₂} 
         {f : A → B} (g : ∀ x → C x → D (f x))
     → y₁ ≡[ ap C x₁₂ ]≡ y₂
     → g x₁ y₁ ≡[ ap D (ap f x₁₂) ]≡ g x₂ y₂
ap[] {x₁₂ = refl} D g y₁₂ .[]coe = ap (g _) (y₁₂ .[]coe)

postulate
  funext : {B : A → Set ℓ} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
  funext-refl : {B : A → Set ℓ} {f : (x : A) → B x} 
              → funext {f = f} (λ _ → refl) ≡ refl
  
  happly-funext : {B : A → Set ℓ} {f g : (x : A) → B x}
                  (p : ∀ x → f x ≡ g x) → happly (funext p) ≡ p x
  funext-happly : {B : A → Set ℓ} {f g : (x : A) → B x}
                → (p : f ≡ g) → (funext λ x → (happly {x = x} p)) ≡ p

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

data _＋_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔l ℓ₂) where
  inl : A → A ＋ B
  inr : B → A ＋ B

_×_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔l ℓ₂)
A × B = Σ A λ _ → B

data Dec (A : Set ℓ) : Set ℓ where
  yes : A       → Dec A
  no  : (A → 𝟘) → Dec A
