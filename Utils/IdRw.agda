{-# OPTIONS --without-K --rewriting #-}

open import Agda.Builtin.Equality.Rewrite
open import Utils

-- Make some equations about identity types strict
module Utils.IdRw where

open UtilVars

ap-ap : ∀ {f : A → B} {g : B → C}
      → ap g (ap f x₁₂) ≡ ap (λ □ → g (f □)) x₁₂
ap-ap {x₁₂ = refl} = refl

{-# REWRITE ap-ap #-}
