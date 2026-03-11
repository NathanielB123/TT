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
