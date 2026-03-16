{-# OPTIONS --prop --rewriting #-}

open import Utils
open import Utils.Prop

-- Strict propositional truncations
module Utils.STrunc where

open UtilVars

data ∥_∥ᴾ (A : Set ℓ) : Prop ℓ where
  incᴾ : A → ∥ A ∥ᴾ

record ∥_∥ (A : Set ℓ) : Set ℓ where
  constructor inc'
  field
    proj : ∥ A ∥ᴾ
open ∥_∥ public

private variable
  P : Prop _

pattern inc x = inc' (incᴾ x)

∥-∥-rec : (A → P) → ∥ A ∥ → P
∥-∥-rec f (inc x) = f x

∥-∥-map : (A → B) → ∥ A ∥ → ∥ B ∥
∥-∥-map f (inc x) .proj = incᴾ (f x)

∃ : (A : Set ℓ₁) → (A → Set ℓ₂) → Set (ℓ₁ ⊔l ℓ₂)
∃ A P = Σ A λ x → ∥ P x ∥

pattern _∃,_ x p = x , inc p

∃-map : {P : A → Set ℓ₁} {Q : B → Set ℓ₂} (f : A → B) 
      → (∀ {x} → P x → Q (f x))
      → ∃ A P → ∃ B Q
∃-map f g (x  , y) .fst = f x
∃-map f g (x ∃, y) .snd .proj = incᴾ (g y)

∃≡ : {B : A → Set ℓ} {x y : ∃ A B} → x .fst ≡ y .fst → x ≡ y
∃≡ refl = refl

-- Subsingleton elimination for propositionally truncated identity
-- (consistent with K)
↑∥≡∥ : ∥ x ≡ y ∥ → x ≡ y
↑∥≡∥ p = ↑≡ (∥-∥-rec ↓≡ p)
