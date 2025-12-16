{-# OPTIONS --cubical-compatible #-}

module Utils where

open import Level using (Level)

open import Relation.Binary.PropositionalEquality as EQ
  using ( _≡_; refl; erefl; cong; subst; sym; subst-subst-sym
        ; subst-sym-subst; sym-cong; cong-app)
  renaming (trans to infixr 4 _∙_; J to ≡-elim)
  public
open EQ.≡-Reasoning using (begin_; step-≡-⟩; step-≡-∣; step-≡-⟨; _∎) public

variable
  ℓ : Level

private variable
  A B C : Set ℓ
  x y z : A
  p q r : x ≡ y

coe : A ≡ B → A → B
coe = subst λ □ → □

_≡[_]≡_ : A → A ≡ B → B → Set _
x ≡[ p ]≡ y = coe p x ≡ y

infix 4 _≡[_]≡_
