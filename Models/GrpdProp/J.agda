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
        (let ⟦Id-t-vz⟧ = ⟦Id⟧ (⟦[]T⟧ ⟦A⟧ (⟦wk⟧ ⟦A⟧)) (⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧)) 
                                                     (⟦vz⟧ ⟦A⟧))
        (let ⟦<t>⟧ = ⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦t⟧)
        (let ⟦<u>⟧ = ⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦u⟧)
        (⟦P⟧ : ⟦Ty⟧ (⟦▷⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) ⟦Id-t-vz⟧)) 
        (⟦d⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ 
                        (⟦,⟧ ⟦Id-t-vz⟧ ⟦<t>⟧
                           (tr (⟦Tm⟧ ⟦Γ⟧) (sym (⟦Id[]T⟧ 
                            {⟦t⟧ = (⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧))}
                            {⟦u⟧ =  (⟦vz⟧ ⟦A⟧)}
                            {⟦δ⟧ = ⟦<t>⟧})) 
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
                 (⟦,⟧ ⟦Id-t-vz⟧ (⟦,⟧ ⟦A⟧ ⟦id⟧ ⟦u⟧) 
                      (tr (⟦Tm⟧ ⟦Γ⟧) 
                      (sym  (⟦Id[]T⟧ {⟦t⟧ = ⟦[]⟧ ⟦t⟧ (⟦wk⟧ ⟦A⟧)} 
                                     {⟦u⟧ =  (⟦vz⟧ ⟦A⟧)} 
                                     {⟦δ⟧ = ⟦<u>⟧}))
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

  -- For unclear reasons (probably something to do with 'Prop'?), metas are 
  -- being solved non-uniquely in the below code, so we write the proofs in a 
  -- golfed style

  ⟦J⟧ .id   ρ 
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦A⟧.idᴰ (⟦u⟧.act ρ)) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.∘idᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ↑≡ ⟦u⟧.id ρ
    rewrite ↑≡ ⟦t⟧.id ρ
    = ₁ ∙ ₂ ∙ ₃
    where 
      PcohG = ⟦P⟧.cohG {x₂ = (ρ , ⟦u⟧.act ρ) , ⟦p⟧.act ρ}
                       ((⟦Γ⟧.id ρ , ⟦p⟧.act ρ) , lift refl[]) 
                       (⟦d⟧.act ρ)
      ₁ = ap (λ □ → (PcohG ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ (□ ⟦P⟧.∘ᴰ PcohG)) 
             (⟦d⟧.id ρ)
      ₂ = ap ((PcohG ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ_) (⟦P⟧.id∘ᴰ PcohG .[]coe)
      ₃ = ⟦P⟧.⁻¹∘ᴰ PcohG .[]coe

  ⟦J⟧ ._⁻¹ {x₁ = ρ₁} {x₂ = ρ₂}  ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.∘id ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁)
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₂)
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ↑≡ ⟦Γ⟧.∘id (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₁
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₂
    rewrite ↑≡ ⟦Γ⟧.⁻¹∘ ρ₁₂
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₁) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₂) .[]coe
    rewrite ↑≡ ρ₁₂ ⟦t⟧.⁻¹
    rewrite ↑≡ ρ₁₂ ⟦u⟧.⁻¹
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦u⟧.pres ρ₁₂) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) .[]coe
    rewrite ↑≡ ⟦A⟧.∘idᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹⁻¹ᴰ (⟦p⟧.act ρ₁) .[]coe
    rewrite ↑≡ ⟦A⟧.⟨∘⟩⁻¹ᴰ (⟦p⟧.act ρ₁) (⟦u⟧.pres ρ₁₂) .[]coe
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₁) 
                            (⟦u⟧.pres ρ₁₂) .[]coe)
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₂ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₂) 
                            (⟦u⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) .[]coe)
    rewrite ↑≡ ⟦A⟧.∘∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) 
                       (⟦p⟧.act ρ₁) .[]coe
    rewrite ↑≡ sym (⟦p⟧.pres ρ₁₂ .lower .[]coe)
    rewrite ↑≡ sym (⟦p⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) .lower .[]coe)
    rewrite ↑≡ sym (⟦A⟧.⟨∘⟩⁻¹ᴰ (⟦t⟧.pres ρ₁₂) (⟦p⟧.act ρ₂) .[]coe)

    rewrite ↑≡ ⟦t⟧.id ρ₁
    rewrite ↑≡ ⟦t⟧.id ρ₂ 
    = ₁ ∙ ₂ ∙ ₃ ∙ ₄ ∙ ₅
    where
      cohG₁ = ⟦P⟧.cohG ((⟦Γ⟧.id ρ₁ , ⟦p⟧.act ρ₁) , lift refl[]) (⟦d⟧.act ρ₁)   
      cohG₂ = ⟦P⟧.cohG ((⟦Γ⟧.id ρ₂ , ⟦p⟧.act ρ₂) , lift refl[]) (⟦d⟧.act ρ₂)  

      ₁ = ap (λ □ → (cohG₂ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ (□ ⟦P⟧.∘ᴰ cohG₁)) (ρ₁₂ ⟦d⟧.⁻¹)
      ₂ = sym (⟦P⟧.∘∘ᴰ (cohG₂ ⟦P⟧.⁻¹ᴰ) (⟦d⟧.pres ρ₁₂ ⟦P⟧.⁻¹ᴰ) cohG₁ .[]coe)
      ₃ = ap (⟦P⟧._∘ᴰ cohG₁) (sym (⟦P⟧.⟨∘⟩⁻¹ᴰ (⟦d⟧.pres ρ₁₂) cohG₂ .[]coe))
      ₄ = ap (((⟦d⟧.pres ρ₁₂ ⟦P⟧.∘ᴰ cohG₂) ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ_) 
             (sym (⟦P⟧.⁻¹⁻¹ᴰ cohG₁ .[]coe))
      ₅ = sym (⟦P⟧.⟨∘⟩⁻¹ᴰ (cohG₁ ⟦P⟧.⁻¹ᴰ) (⟦d⟧.pres ρ₁₂ ⟦P⟧.∘ᴰ cohG₂) .[]coe)

  ⟦J⟧ ._∘_ {x₁ = ρ₁} {x₂ = ρ₂} {x₃ = ρ₃} ρ₁₂ ρ₂₃ 
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁)
    rewrite ↑≡ ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₂)
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₁
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₂
    rewrite ↑≡ ⟦Γ⟧.id⁻¹ ρ₃
    rewrite ↑≡ ⟦Γ⟧.∘id ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₁₂
    rewrite ↑≡ ⟦Γ⟧.∘id ρ₂₃
    rewrite ↑≡ ⟦Γ⟧.id∘ ρ₂₃
    rewrite ↑≡ ⟦Γ⟧.id∘ (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃)
    rewrite ↑≡ ⟦Γ⟧.∘id (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃)
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₁) .[]coe
    rewrite ↑≡ ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₂) .[]coe
    rewrite ↑≡ ⟦A⟧.∘⁻¹ᴰ  (⟦p⟧.act ρ₂) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦u⟧.pres ρ₁₂) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦u⟧.pres ρ₂₃) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) .[]coe
    rewrite ↑≡ ⟦A⟧.id∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₂₃) .[]coe
    rewrite ↑≡ sym (⟦p⟧ .pres ρ₁₂ .lower .[]coe)
    rewrite ↑≡ sym (⟦p⟧ .pres ρ₂₃ .lower .[]coe)
    rewrite ↑≡ ρ₁₂ ⟦t⟧.∘ ρ₂₃
    rewrite ↑≡ ρ₁₂ ⟦u⟧.∘ ρ₂₃
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₁) 
                            (⟦u⟧.pres ρ₁₂) .[]coe)
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₂ ⟦A⟧.⁻¹ᴰ) (⟦p⟧.act ρ₂) 
                            (⟦u⟧.pres ρ₂₃) .[]coe)
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) 
                            (⟦p⟧.act ρ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) 
                            (⟦u⟧.pres ρ₂₃) .[]coe)
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂) (⟦p⟧.act ρ₂) (⟦u⟧.pres ρ₂₃) .[]coe)
    rewrite ↑≡ ⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂) (⟦t⟧.pres ρ₂₃) (⟦p⟧.act ρ₃) .[]coe
    rewrite ↑≡ ⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) (⟦t⟧.pres ρ₁₂) (⟦p⟧.act ρ₂) .[]coe
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ ((⟦p⟧.act ρ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⟦t⟧.pres ρ₁₂) 
                            (⟦p⟧.act ρ₂) (⟦u⟧.pres ρ₂₃) .[]coe)
    rewrite ↑≡ sym (⟦A⟧.∘∘ᴰ (⟦p⟧.act ρ₁) (⟦u⟧.pres ρ₁₂) (⟦u⟧.pres ρ₂₃) .[]coe)

    rewrite ↑≡ ⟦t⟧.id ρ₁
    rewrite ↑≡ ⟦t⟧.id ρ₂
    rewrite ↑≡ ⟦t⟧.id ρ₃
    = ₁ ∙ ₂ ∙ ₃ ∙ ₄ ∙ ₅ ∙ ₆ ∙ ₇
    where 
      cohG₁ = ⟦P⟧.cohG ((⟦Γ⟧.id ρ₁ , ⟦p⟧.act ρ₁) , lift refl[]) (⟦d⟧.act ρ₁)
      cohG₂ = ⟦P⟧.cohG ((⟦Γ⟧.id ρ₂ , ⟦p⟧.act ρ₂) , lift refl[]) (⟦d⟧.act ρ₂)
      cohG₃ = ⟦P⟧.cohG ((⟦Γ⟧.id ρ₃ , ⟦p⟧.act ρ₃) , lift refl[]) (⟦d⟧.act ρ₃)

      ₁ = ap (λ □ → (cohG₁ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ (□ ⟦P⟧.∘ᴰ cohG₃)) (ρ₁₂ ⟦d⟧.∘ ρ₂₃)
      ₂ = ap ((cohG₁ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ_) 
             (⟦P⟧.∘∘ᴰ (⟦d⟧.pres ρ₁₂) (⟦d⟧.pres ρ₂₃) cohG₃ .[]coe)
      ₃ = sym (⟦P⟧.∘∘ᴰ (cohG₁ ⟦P⟧.⁻¹ᴰ) (⟦d⟧.pres ρ₁₂) 
              (⟦d⟧.pres ρ₂₃ ⟦P⟧.∘ᴰ cohG₃) .[]coe)
      ₄ = ap (((cohG₁ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ ⟦d⟧.pres ρ₁₂) ⟦P⟧.∘ᴰ_)
             (sym (⟦P⟧.⟨∘⁻¹⟩∘ᴰ cohG₂ (⟦d⟧.pres ρ₂₃ ⟦P⟧.∘ᴰ cohG₃) .[]coe))
      ₅ = ap (((cohG₁ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ ⟦d⟧.pres ρ₁₂) ⟦P⟧.∘ᴰ_) 
             (⟦P⟧.∘∘ᴰ cohG₂ (cohG₂ ⟦P⟧.⁻¹ᴰ) (⟦d⟧.pres ρ₂₃ ⟦P⟧.∘ᴰ cohG₃) .[]coe)
      ₆ = sym (⟦P⟧.∘∘ᴰ ((cohG₁ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ ⟦d⟧.pres ρ₁₂) cohG₂ 
                       ((cohG₂ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ (⟦d⟧.pres ρ₂₃ ⟦P⟧.∘ᴰ cohG₃)) 
                       .[]coe)
      ₇ = ap (⟦P⟧._∘ᴰ ((cohG₂ ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ (⟦d⟧.pres ρ₂₃ ⟦P⟧.∘ᴰ cohG₃))) 
             (⟦P⟧.∘∘ᴰ (cohG₁ ⟦P⟧.⁻¹ᴰ) (⟦d⟧.pres ρ₁₂) cohG₂ .[]coe)
