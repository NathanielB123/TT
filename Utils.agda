{-# OPTIONS --without-K #-}

module Utils where

open import Relation.Binary.PropositionalEquality as EQ
  using ( _≡_; refl; erefl; cong; cong₂; subst; sym; subst-subst-sym
        ; subst-sym-subst; sym-cong; cong-app)
  renaming (trans to infixr 4 _∙_; J to ≡-elim)
  public
