{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils
open import Utils.WithK

-- Propositional truncations
module Utils.Trunc where

open UtilVars

postulate
  ∥_∥      : (A : Set ℓ) → Set ℓ
  inc      : A → ∥ A ∥
  squash   : {x y : ∥ A ∥} → x ≡ y
  ∥-∥-elim : (P : ∥ A ∥ → Set ℓ) → (∀ {x} {y₁ y₂ : P x} → y₁ ≡ y₂) 
           → (∀ x → P (inc x)) → (x : ∥ A ∥) → P x
  elim-inc : {P : ∥ A ∥ → Set ℓ} {p : ∀ {x} {y₁ y₂ : P x} → y₁ ≡ y₂}
             {f : ∀ x → P (inc x)}
           → ∥-∥-elim P p f (inc x) ≡ f x
  {-# REWRITE elim-inc #-}

∥-∥-rec : (∀ {y₁ y₂ : B} → y₁ ≡ y₂)
        → (A → B)
        → ∥ A ∥ → B
∥-∥-rec p f x = ∥-∥-elim _ p f x

-- These do not unfold nicely, so we make them opaque and compute with rewrite
-- rules
opaque
  ∥-∥-rec₂ : (∀ {z₁ z₂ : C} → z₁ ≡ z₂)
           → (A → B → C)
           → ∥ A ∥ → ∥ B ∥ → C
  ∥-∥-rec₂ p f x y = ∥-∥-rec (funext λ _ → p) (λ x' y → ∥-∥-rec p (f x') y) x y

  ∥-∥-map : (A → B) → ∥ A ∥ → ∥ B ∥
  ∥-∥-map f = ∥-∥-rec squash λ x → inc (f x)

  ∥-∥-map₂ : (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
  ∥-∥-map₂ f = ∥-∥-rec₂ squash λ x y → inc (f x y)

  ∥-∥-rec₂-inc : {C≡ : (∀ {z₁ z₂ : C} → z₁ ≡ z₂)}
                 {f : A → B → C}
                 {x : A} {y : B}
               → ∥-∥-rec₂ C≡ f (inc x) (inc y) ≡ f x y
  ∥-∥-rec₂-inc = refl

  ∥-∥-map-inc : {f : A → B} {x : A}
              → ∥-∥-map f (inc x) ≡ inc (f x)
  ∥-∥-map-inc = refl

  ∥-∥-map₂-inc : {f : A → B → C} {x : A} {y : B}
               → ∥-∥-map₂ f (inc x) (inc y) ≡ inc (f x y)
  ∥-∥-map₂-inc = refl
{-# REWRITE ∥-∥-rec₂-inc ∥-∥-map-inc ∥-∥-map₂-inc #-}

-- I don't love using '∃' notation for something that contains actual data (the 
-- first component) but I don't know what else to call this...
∃ : (A : Set ℓ₁) → (A → Set ℓ₂) → Set (ℓ₁ ⊔l ℓ₂)
∃ A P = Σ A λ x → ∥ P x ∥

opaque
  ∃squash : {P : A → Set ℓ} {x y : ∃ A P} → x .fst ≡ y .fst → x ≡ y
  ∃squash refl = ap (_ ,_) squash

_∃,_ : {P : A → Set ℓ} (x : A) → P x → ∃ A P
x ∃, p = x , inc p

∃-rec : {P : A → Set ℓ} (f : (x : A) → P x → B) 
      → (∀ {x} {p₁ p₂ : P x} → f x p₁ ≡ f x p₂)
      → ∃ A P → B
∃-rec f q (x , p) 
  = ∥-∥-elim (λ p' → ∃ _ λ y → Σ _ (λ p' → (y ≡ f x p'))) 
    (λ {_} {(y₁ , p₁)} {(y₂ , p₂)} 
     → apd₂ _,_ (∥-∥-rec₂ uip (λ where (_ , refl) (_ , refl) → q) p₁ p₂) 
                (coe[] squash)) 
    (λ p' → f x p' ∃, (p' , refl) ) p .fst

∃-map : {P : A → Set ℓ₁} {Q : B → Set ℓ₂} (f : A → B) 
      → (∀ {x} → P x → Q (f x))
      → ∃ A P → ∃ B Q
∃-map f g (x , p) .fst = f x
∃-map f g (x , p) .snd = ∥-∥-map g p

∃-map₂ : {P : A → Set ℓ₁} {Q : B → Set ℓ₂} {R : C → Set ℓ₃}
          (f : A → B → C) → (∀ {x y} → P x → Q y → R (f x y))
      → ∃ A P → ∃ B Q → ∃ C R
∃-map₂ f g (x , p) (y , q) .fst = f x y
∃-map₂ f g (x , p) (y , q) .snd = ∥-∥-map₂ g p q
