open import Data.Nat using (ℕ) renaming (suc to su; zero to ze)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

module Utils.List where

variable 
  n : ℕ
  A : Set

iter-×ᴺᴱ : ℕ → Set → Set
iter-×ᴺᴱ ze     A = A
iter-×ᴺᴱ (su n) A = A × iter-×ᴺᴱ n A

iter-× : ℕ → Set → Set
iter-× ze     A = ⊤
iter-× (su n) A = iter-×ᴺᴱ n A

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

π₁× : iter-×ᴺᴱ n A → A
π₁× {n = ze}   x        = x
π₁× {n = su n} (x , xs) = x

π₂× : iter-×ᴺᴱ n A → iter-× n A
π₂× {n = ze}   x        = tt
π₂× {n = su n} (x , xs) = xs

[_] : iter-× n A → List A
[_] {n = ze}   tt = [] 
[_] {n = su n} xs = π₁× xs ∷ [_] {n = n} (π₂× {n = n} xs)

len : List A → ℕ
len []       = ze
len (x ∷ xs) = su (len xs)

unpackᴺᴱ : A → (xs : List A) → iter-×ᴺᴱ (len xs) A
unpackᴺᴱ x []       = x
unpackᴺᴱ x (y ∷ ys) = x , unpackᴺᴱ y ys

unpack : (xs : List A) → iter-× (len xs) A
unpack []       = tt
unpack (x ∷ xs) = unpackᴺᴱ x xs

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

stab : ∀ (xs : List A) → [_] {n = len xs} (unpack xs) ≡ xs
stab []       = refl
stab (x ∷ xs) = {!   !}

test-1 : List ℕ
test-1 = [ 1 , 2 , 3 ]

test-2 : List ℕ
test-2 = [ 1 ]

test-3 : List ℕ
test-3 = [ 1 , 2 , 3 , unpack test-1 ] 
