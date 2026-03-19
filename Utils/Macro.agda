open import Utils hiding (Dec; yes; no)

open import Agda.Primitive
open import Reflection as TC hiding (_>>=_)
open import Data.Maybe as M using (Maybe; just; nothing; map)
open import Function using (_∘_; case_of_)
open import Relation.Nullary.Decidable using (yes; no)
open import Data.Nat using (ℕ; _<?_) renaming (zero to ze; suc to su)
open import Data.List using (List; []) renaming (_∷_ to _,-_)

-- Ported from the 1Lab
-- https://1lab.dev/1Lab.Reflection.Marker.html
module Utils.Macro where

open Sort
open Blocker
_<$>_ = map

infixr 5 _ⱽ,-_
infix 6 _<$>_

all-metas-in : Term → List Blocker
all-metas-in tm = go tm [] where
  go  : Term → List Blocker → List Blocker
  go* : List (Arg Term) → List Blocker → List Blocker

  go (var _ args)             acc = go* args acc
  go (con _ args)             acc = go* args acc
  go (def _ args)             acc = go* args acc
  go (lam _ (abs _ t))        acc = go t acc
  go (pat-lam cs args)        acc = acc
  go (pi (arg _ a) (abs _ b)) acc = go a (go b acc)
  go (agda-sort s)            acc = acc
  go (lit l)                  acc = acc
  go (meta x args)            acc = go* args (blockerMeta x ,- acc)
  go unknown                  acc = acc

  go* []             acc = acc
  go* (arg _ x ,- xs) acc = go x (go* xs acc)

wait-for-type : Term → TC Term
wait-for-type tm with all-metas-in tm
... | [] = pure tm
... | it = blockTC (blockerAll it)

-- The marker. The marker is literally just the identity function, but
-- written surrounding rather than prefix. Unlike literally the identity
-- function, however, the marker is marked NOINLINE, so it will not
-- disappear without reduction.
⌜_⌝ : {A : Set ℓ} → A → A
⌜ x ⌝ = x
{-# NOINLINE ⌜_⌝ #-}

-- Abstract over the marked term(s). All marked terms refer to the same
-- variable, so e.g.
--
--  abstract-marker (quoteTerm (f ⌜ x ⌝ (λ _ → ⌜ x ⌝)))
--
-- is (λ e → f e (λ _ → e)). The resulting term is open in precisely one
-- variable: that variable is what substitutes the marked terms.
abstract-marker : Term → Maybe Term
abstract-marker = go 0 where
  go  : ℕ → Term → Maybe Term
  go* : ℕ → List (Arg Term) → Maybe (List (Arg Term))

  go k (var j args) = var j' <$> go* k args
    where
      j' : ℕ
      j' with j <? k
      ... | no  _ = su j
      ... | yes _ = j
  go k (con c args) = con c <$> go* k args
  go k (def f args) with f
  ... | quote ⌜_⌝ = just (var k [])
  -- ^ This is the one interesting case. Any application of the marker
  -- gets replaced with the 'k'th variable. Initially k = 0, so this is
  -- the variable bound by the lambda. But as we encounter further
  -- binders, we must increment this, since the marked term gets farther
  -- and farther away in the context.
  ... | x = def f <$> go* k args
  go k (lam v (abs x t)) = (lam v ∘ abs x) <$> go (su k) t
  go k (pat-lam cs args) = nothing
  go k (pi (arg i a) (abs x t)) = M.do
    t ← go (su k) t
    a ← go k a
    just (pi (arg i a) (abs x t))
  go k (agda-sort s) with s
  ... | set t = (agda-sort ∘ set) <$> go k t
  ... | lit n = just (agda-sort (lit n))
  ... | prop t = (agda-sort ∘ prop) <$> go k t
  ... | propLit n = just (agda-sort (propLit n))
  ... | inf n = just (agda-sort (inf n))
  ... | unknown = just (agda-sort unknown)
  go k (lit l) = just (lit l)
  go k (meta m args) = meta m <$> go* k args
  go k unknown = just unknown

  go* k [] = just []
  go* k (arg i x ,- xs) = M.do
    x ← go k x
    xs ← go* k xs
    just (arg i x ,- xs)

pattern _ⱽ,-_ t xs 
  = arg (arg-info visible (modality relevant quantity-ω)) t ,- xs


private
  -- We need this weird record (instead of a Σ-type) for two reasons.
  -- One is universe levels. The second is that, if we're elaborating a
  -- pre-existing
  --
  --   ap! p
  --
  -- (and supposing ap! had type {it : Σ Type _} → it .fst → x ≡ y), we
  -- will elaborate p against it .fst *before* running the ap-worker
  -- tactic, which very helpfully solves it := ? , [type of p] and
  -- prevents the tactic from firing. So we also need it to be
  -- no-eta-equality.
  record ap-data {ℓ} {A : Set ℓ} (x y : A) : Setω where
    no-eta-equality ; pattern ; constructor mkapdata
    field
      ℓ-mark : Level
      mark   : Set ℓ-mark
      from   : mark → x ≡ y

  ap-worker : ∀ {ℓ} {A : Set ℓ} (x : A) → Term → TC 𝟙
  ap-worker x goal = withNormalisation ff TC.do
    `x ← quoteTC x TC.>>= wait-for-type
    case abstract-marker `x of λ where
      (just l) → do
        unify goal (con (quote mkapdata) 
                   (unknown ⱽ,- unknown ⱽ,- 
                   def (quote ap) (lam visible (abs "□" l) ⱽ,- []) ⱽ,- []))
      nothing → typeError (
        strErr "Failed to abstract over marker in term" ,- termErr `x ,- [])

  open ap-data

  ap!-wrapper : ∀ {ℓ} {A : Set ℓ} {x y : A} 
                  {@(tactic ap-worker x) it : ap-data x y} 
              → it .mark → x ≡ y
  ap!-wrapper {it = mkapdata _ _ f} = f

  ap¡-wrapper : ∀ {ℓ} {A : Set ℓ} {x y : A} 
                  {@(tactic ap-worker y) it : ap-data x y} 
              → it .mark → x ≡ y
  ap¡-wrapper {it = mkapdata _ _ f} = f

macro
  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the LEFT ENDPOINT of the path. Use
  -- with _≡⟨_⟩_.
  ap! : Term → TC 𝟙
  ap! g = unify g (def (quote ap!-wrapper) [])

  -- Generalised ap. Automatically generates the function to apply to by
  -- abstracting over any markers in the RIGHT ENDPOINT of the path. Use
  -- with _≡˘⟨_⟩_.
  ap¡ : Term → TC 𝟙
  ap¡ g = unify g (def (quote ap¡-wrapper) [])

module _ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y} {f : A → (A → A) → A} where
  private
    q : f x (λ y → x) ≡ f y (λ z → y)
    q =
      f ⌜ x ⌝ (λ _ → ⌜ x ⌝) ≡⟨ ap! p ⟩
      f y (λ _ → y)         ∎
