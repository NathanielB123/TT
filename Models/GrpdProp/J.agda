{-# OPTIONS --rewriting --prop --smart-with --show-irrelevant #-}

open import Utils.Prop
open import Utils.MacroProp

open import Models.GrpdProp.Grpd
open import Models.GrpdProp.Motives
open import Models.GrpdProp.Subst
open import Models.GrpdProp.Id

module Models.GrpdProp.J where

-- The J rule
module _
        (let Id-t-vz = ⟦Id⟧ (⟦[]T⟧ ⟦A⟧ (⟦wk⟧ ⟦A⟧)) (⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧)) 
                                                   (⟦vz⟧ ⟦A⟧))
        (let id,t = ⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦t⟧)
        (let id,u = ⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦u⟧)
        (⟦P⟧ : ⟦Ty⟧ (⟦▷⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) Id-t-vz)) 
        (⟦d⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ 
                        (⟦,⟧ Id-t-vz id,t
                           (tr (⟦Tm⟧ ⟦Γ⟧) (sym (⟦Id[]T⟧ 
                            {⟦t⟧ = (⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧))}
                            {⟦u⟧ =  (⟦vz⟧ ⟦A⟧)}
                            {⟦δ⟧ = id,t})) 
                            ⟦refl⟧))))
         (⟦p⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Id⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧))
         where
        
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦P⟧ = Grpdᴰ.Data (⟦P⟧ .snd)
    module ⟦t⟧ = _⇒ᴰ_ ⟦t⟧
    module ⟦u⟧ = _⇒ᴰ_ ⟦u⟧
    module ⟦d⟧ = _⇒ᴰ_ ⟦d⟧
    module ⟦p⟧ = _⇒ᴰ_ ⟦p⟧
    module ⟦Γ▷A⟧ = Grpd.Data (⟦▷⟧ ⟦Γ⟧ ⟦A⟧ .snd)

  ⟦J⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ 
                 (⟦,⟧ Id-t-vz (⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦u⟧) 
                      (tr (⟦Tm⟧ ⟦Γ⟧) 
                      (sym  (⟦Id[]T⟧ {⟦t⟧ = ⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧)} 
                                     {⟦u⟧ =  (⟦vz⟧ ⟦A⟧)} 
                                     {⟦δ⟧ = id,u}))
                      ⟦p⟧)))
  ⟦J⟧ .act  ρ 
    = ⟦P⟧.coeG ((⟦Γ⟧.id ρ , ⟦p⟧.act ρ) , lift (coe[] 
      (⌜ ⟦A⟧.idᴰ (⟦t⟧.act ρ) ⌝ ⟦A⟧.∘ᴰ ⟦p⟧.act ρ
      ≡⟨ ap! (sym (⟦t⟧.id ρ)) ⟩
      (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.∘ᴰ ⟦p⟧.act ρ) ∎)))
      (⟦d⟧.act ρ)
  ⟦J⟧ .pres {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ 
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₁
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₂
    rewrite ↑≡ ⟦Γ⟧.∘id ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦A⟧.⁻¹∘∘ᴰ (⟦p⟧.act ρ₁) (⟦u⟧.pres ρ₁₂) .[]coe
    rewrite ↑≡ ⟦t⟧.id ρ₁
    rewrite ↑≡ ⟦t⟧.id ρ₂
    rewrite ↑≡ sym (⟦p⟧.pres ρ₁₂ .lower .[]coe)
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₁) 
                            (⟦u⟧.pres ρ₁₂) .[]coe) = 
    (cohG₁ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ (⟦d⟧.pres ρ₁₂ ⟦P⟧.∘ᴰ cohG₂)
    where
      cohG₁ = ⟦P⟧.cohG ((⟦Γ⟧.id ρ₁ , ⟦p⟧.act ρ₁) , lift refl[]) (⟦d⟧.act ρ₁)
      cohG₂ = ⟦P⟧.cohG ((⟦Γ⟧.id ρ₂ , ⟦p⟧.act ρ₂) , lift refl[]) (⟦d⟧.act ρ₂)

  -- For unclear reasons, 'ap!' behaves weirdly (including possibly looping?!)
  -- in the below code, so we give up on equational reasoning syntax and just
  -- complete the proofs with 'rewrite'
  ⟦J⟧ .id   ρ 
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦A⟧.idᴰ (⟦u⟧.act ρ)) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.∘idᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦u⟧.id ρ
    rewrite ↑≡ ⟦t⟧.id ρ
    -- Actual proof
    using PcohG ← ⟦P⟧.cohG {x₂ = (ρ , ⟦u⟧.act ρ) , ⟦p⟧.act ρ}
                           ((⟦Γ⟧.id ρ , ⟦p⟧.act ρ) , lift refl[]) 
                           (⟦d⟧.act ρ)
    rewrite ↑≡ ⟦d⟧.id ρ
    rewrite ↑≡ ⟦P⟧.id∘ᴰ PcohG .[]coe
    rewrite ↑≡ (⟦P⟧.⁻¹∘ᴰ PcohG .[]coe)
    = refl
  ⟦J⟧ ._⁻¹ {x₁ = ρ₁} {x₂ = ρ₂}  ρ₁₂ = {!!}    
  ⟦J⟧ ._∘_  = {!   !}
