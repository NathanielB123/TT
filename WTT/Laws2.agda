{-# OPTIONS --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

open import WTT.Syntax
open import WTT.SubUniq
open import WTT.Laws1
open import WTT.Laws2<>

-- The actual proofs for the commuting laws can be found in |Laws2Wk| and
-- |Laws2<>|.
module WTT.Laws2 where

wk^T   : ∀ {δ : Sub[ r ] Δ Γ} {B𝒢}
       → A [ wk ]T≔ A[]₁ → A [ δ ]T≔ A[]₂
       → A[]₁ [ δ ^ B𝒢 ]T≔ A[][]
       → A[]₂ [ wk ]T≔ A[][]

^<>T   : ∀ {δ : Sub[ r ] Δ Γ} {B𝒢}
       → A [ < u > ]T≔ A[]₁
       → A [ δ ^ B𝒢 ]T≔ A[]₂
       → A[]₁ [ δ ]T≔ A[][]
       → u [ δ ] B𝒢 ≔ u[]
       → A[]₂ [ < u[] > ]T≔ A[][]

wk^T {r = V} A𝒢₁ A𝒢₂ A𝒢₃ 
  using A𝒢s ← wk^T^^ⱽ _ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} A𝒢₁ A𝒢₃
  with refl ← []T-uniq (A𝒢s .πA𝒢₁) A𝒢₂
  with refl ← u[]Tp (A𝒢s .πA𝒢₁) A𝒢₂
  = πA𝒢₂ A𝒢s
wk^T {r = T} A𝒢₁ A𝒢₂ A𝒢₃
  using A𝒢s ← wk^T^^ _ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} A𝒢₁ A𝒢₃
  with refl ← []T-uniq (A𝒢s .πA𝒢₁) A𝒢₂
  with refl ← u[]Tp (A𝒢s .πA𝒢₁) A𝒢₂
  = πA𝒢₂ A𝒢s

^<>T {r = V} A𝒢₁ A𝒢₂ A𝒢₃ u𝒢 
  = ^<>T^^ⱽ _ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} A𝒢₁ A𝒢₂ A𝒢₃ u𝒢
^<>T {r = T} A𝒢₁ A𝒢₂ A𝒢₃ u𝒢 
  = ^<>T^^ _ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} A𝒢₁ A𝒢₂ A𝒢₃ u𝒢
