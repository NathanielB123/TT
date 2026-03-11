open import Utils

module Utils.WithK where

open UtilVars

uip : p ≡ q
uip {p = refl} {q = refl} = refl

apdd₂-K : ∀ (B : A → Set ℓ₁) {C : A → Set ℓ₂} {y : B x₁}
            (f : ∀ x → B x → C x) (eq₁ : x₁ ≡ x₂) 
            {eq₂ : C x₁ ≡ C x₂} {eq₃ : B x₁ ≡ B x₂} 
      → f x₁ y ≡[ eq₂ ]≡ f x₂ (coe eq₃ y)
apdd₂-K B f refl {refl} {refl} = refl[] 

apdd₂-K' : ∀ (B : A → Set ℓ) {y : B x₁}
             (f : ∀ x → B x → C) (eq₁ : x₁ ≡ x₂)
         → f x₁ y ≡ f x₂ (transp B eq₁ y)
apdd₂-K' B f p = apd₂ f p refl[]
-- refl {refl} = refl 

refl[]-K : _≡[_]≡_ {A = A} x p x
refl[]-K {p = refl} = refl[]

reix[] : y₁ ≡[ p ]≡ y₂ → y₁ ≡[ q ]≡ y₂
reix[] {p = refl} {q = refl} r = r

coe-K : coe p x ≡ x
coe-K {p = refl} = refl

-- postulate
--   funext : {B : A → Set ℓ} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
--   funext-refl : {B : A → Set ℓ} {f : (x : A) → B x} 
--               → funext {f = f} (λ _ → refl) ≡ refl

-- funexti : {B : A → Set ℓ} {f g : {x : A} → B x} → (∀ {x} → f {x} ≡ g {x}) 
--         → _≡_ {A = {x : A} → B x} f g
-- funexti {f = f} {g = g} p = ap (λ f {x} → f x) (funext (λ _ → p))

-- piext : {B₁ B₂ : A → Set ℓ} → (∀ x → B₁ x ≡ B₂ x) → (∀ x → B₁ x) ≡ (∀ x → B₂ x)
-- piext p = ap (λ □ → ∀ x → □ x) (funext p)

-- piexti : {B₁ B₂ : A → Set ℓ} → (∀ {x} → B₁ x ≡ B₂ x) 
--        → (∀ {x} → B₁ x) ≡ (∀ {x} → B₂ x)
-- piexti p = ap (λ □ → ∀ {x} → □ {x}) (funexti p)

-- piext[] : {B₁ : A₁ → Set ℓ} {B₂ : A₂ → Set ℓ} (A≡ : A₁ ≡ A₂) 
--         → (∀ {x₁ x₂} (x≡ : x₁ ≡[ A≡ ]≡ x₂) → B₁ x₁ ≡ B₂ x₂) 
--         → (∀ x → B₁ x) ≡ (∀ x → B₂ x)
-- piext[] refl p = piext λ x → p refl[]

-- funext[] : {B₁ B₂ : A → Set ℓ} {f : (x : A) → B₁ x} {g : (x : A) → B₂ x} 
--          → (∀ x → f x ≡[ {!!} ]≡ g x) → f ≡[ {!!} ]≡ g
