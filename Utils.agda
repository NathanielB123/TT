{-# OPTIONS --cubical-compatible #-}

module Utils where

open import Level using (Level)

open import Relation.Binary.PropositionalEquality as EQ
  using ( _≡_; refl; erefl; sym)
  renaming 
    (trans to infixr 4 _∙_; J to ≡-elim; subst to transp
    ; subst-subst-sym to transp-transp-sym
    ; subst-sym-subst to transp-sym-subst
    ; cong to ap; cong-app to happly; cong₂ to ap₂; dcong to apd
    ; sym-cong to sym-ap)
  public
open EQ.≡-Reasoning using (begin_; step-≡-⟩; step-≡-∣; step-≡-⟨; _∎) public
open import Data.Unit using () renaming (⊤ to 𝟙; tt to ⟨⟩) public
open import Data.Bool using (Bool) renaming (true to tt; false to ff) public
open import Data.Empty using () renaming (⊥ to 𝟘; ⊥-elim to absurd) public
open import Data.Product using (Σ; _,_) renaming (proj₁ to fst; proj₂ to snd)
  public

variable
  ℓ : Level

private variable
  A B C : Set ℓ
  x y z : A
  p q r : x ≡ y

coe : A ≡ B → A → B
coe = transp λ □ → □

_≡[_]≡_ : A → A ≡ B → B → Set _
x ≡[ p ]≡ y = coe p x ≡ y

infix 4 _≡[_]≡_
