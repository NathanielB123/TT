{-# OPTIONS --smart-with --prop --rewriting #-}

open import Utils.Prop
open import Utils.MacroProp

open import Models.GrpdProp.Grpd
open import Models.GrpdProp.Motives
open import Models.GrpdProp.Subst

-- Substitution calculus
module Models.GrpdProp.SubstLaws where

⟦[id]T⟧ : ⟦[]T⟧ ⟦A⟧ ⟦id⟧ ≡ ⟦A⟧
⟦[id]T⟧ = refl

⟦[][]T⟧ : ⟦[]T⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧) ⟦σ⟧ ≡ ⟦[]T⟧ ⟦A⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧) 
⟦[][]T⟧ = apd₂ _,_ refl (coe[] {!!})

⟦wk,⟧ : {⟦t⟧ : ⟦Tm⟧ ⟦Δ⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧)}
      → ⟦⨾⟧ (⟦wk⟧ ⟦A⟧) (⟦,⟧ ⟦A⟧ ⟦δ⟧ ⟦t⟧) ≡ ⟦δ⟧
⟦wk,⟧ = refl

⟦[id]⟧ : {⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧} → ⟦[]⟧ ⟦t⟧ ⟦id⟧ ≡ ⟦t⟧
⟦[id]⟧ = refl

⟦[][]⟧ : {⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧} {⟦δ⟧ : ⟦Sub⟧ ⟦Δ⟧ ⟦Γ⟧} {⟦σ⟧ : ⟦Sub⟧ ⟦Θ⟧ ⟦Δ⟧} 
       → ⟦[]⟧ (⟦[]⟧ ⟦t⟧ ⟦δ⟧) ⟦σ⟧ 
       ≡[ ap (⟦Tm⟧ ⟦Θ⟧) (⟦[][]T⟧ {⟦A⟧ = ⟦A⟧} {⟦δ⟧ = ⟦δ⟧} {⟦σ⟧ = ⟦σ⟧})
       ]≡ ⟦[]⟧ ⟦t⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧) 
⟦[][]⟧ = coe[] {!!}

⟦vz,⟧  : ⟦[]⟧ (⟦vz⟧ ⟦A⟧) (⟦,⟧ ⟦A⟧ ⟦δ⟧ ⟦u⟧) ≡ ⟦u⟧
⟦vz,⟧ = refl


-- postulate
    

-- postulate
--   ⟦[id]⟧ : ⟦[]⟧ ⟦t⟧ ⟦id⟧ ≡[ ap (⟦Tm⟧ ⟦Γ⟧) ⟦[id]T⟧ ]≡ ⟦t⟧
--   ⟦[][]⟧ : ⟦[]⟧ (⟦[]⟧ ⟦t⟧ ⟦δ⟧) ⟦σ⟧ 
--          ≡[ ap (⟦Tm⟧ ⟦Γ⟧) ⟦[][]T⟧ 
--          ]≡ ⟦[]⟧ ⟦t⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧) 
--   ⟦vz,⟧  : {⟦u⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧)} 
--          → ⟦[]⟧ (⟦vz⟧ {⟦A⟧ = ⟦A⟧}) (⟦,⟧ {⟦A⟧ = ⟦A⟧} ⟦δ⟧ ⟦u⟧) 
--          ≡[ ap (⟦Tm⟧ _) (⟦[][]T⟧ ∙ ap (⟦[]T⟧ ⟦A⟧) ⟦wk,⟧)
--          ]≡ ⟦u⟧