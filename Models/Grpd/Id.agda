{-# OPTIONS --rewriting --smart-with #-}

open import Utils
open import Utils.WithK
open import Utils.Macro

open import Models.Grpd.Grpd
open import Models.Grpd.Motives
open import Models.Grpd.Subst

-- Identity types
module Models.Grpd.Id where

-- Identity types
module _ (⟦A⟧ : ⟦Ty⟧ ⟦Γ⟧) (⟦t⟧ ⟦u⟧ : ⟦Tm⟧ ⟦Γ⟧ ⟦A⟧) where
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦t⟧ = _⇒ᴰ_ ⟦t⟧
    module ⟦u⟧ = _⇒ᴰ_ ⟦u⟧

  ⟦Id⟧ : ⟦Ty⟧ ⟦Γ⟧
  ⟦Id⟧ .fst .Carᴰ ρ 
    = ⟦A⟧ .fst .Relᴰ (⟦t⟧.act ρ) (⟦u⟧.act ρ) (⟦Γ⟧.id ρ)
  ⟦Id⟧ .fst .Relᴰ τ₁ τ₂ ρ₁₂ 
    = tr (⟦A⟧ .fst .Relᴰ _ _) (⟦Γ⟧.⁻¹∘id∘ ρ₁₂) 
         ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ₁ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ≡ τ₂
  ⟦Id⟧ .snd .idᴰ {x = ρ} τ
    rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    rewrite ⟦Γ⟧.id⁻¹ ρ
    -- Reflexive rewrites
    rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ) 
    rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ) =
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (⟦Γ⟧.id ρ) ⌝)
    ≡⟨ ap! (⟦u⟧.id ρ) ⟩
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ τ ⟦A⟧.∘ᴰ ⟦A⟧.idᴰ (⟦u⟧.act ρ) ⌝
    ≡⟨ ap! (⟦A⟧.∘idᴰ τ .[]coe) ⟩
    (⌜ ⟦t⟧.pres (⟦Γ⟧.id ρ) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (⟦t⟧.id ρ) ⟩
    ⌜ ⟦A⟧.idᴰ (⟦t⟧ .act ρ) ⟦A⟧.⁻¹ᴰ ⌝ ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ) .[]coe) ⟩
    ⟦A⟧.idᴰ (⟦t⟧ .act ρ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ⟦A⟧.id∘ᴰ τ .[]coe ⟩
    τ ∎
  ⟦Id⟧ .snd ._⁻¹ᴰ {x₁ = ρ₁} {x₂ = ρ₂} {x₁₂ = ρ₁₂} {x₁ᴰ = τ} refl
    rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
    rewrite ⟦Γ⟧.id∘ ρ₁₂
    rewrite ⟦Γ⟧.id∘ (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ⟦Γ⟧.∘id (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂
    rewrite ⟦Γ⟧.∘⁻¹ ρ₁₂
    rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁)
    -- Reflexive rewrites
    rewrite ⟦Γ⟧.⁻¹∘ (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ⟦Γ⟧.∘∘ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ⟦Γ⟧.∘∘ (⟦Γ⟧.id ρ₁) ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹)
    rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ₁) 
    rewrite ⟦Γ⟧.∘∘ ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹) (⟦Γ⟧.id ρ₁) =
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
    ⌜ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)) ⟦A⟧.∘ᴰ 
    ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝
    ≡⟨ ap! (⟦A⟧.∘∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂)
                    (⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹)) .[]coe) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    ⌜ (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂) ⟦A⟧.∘ᴰ ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝)
    ≡⟨ ap! (⟦A⟧.∘∘ᴰ τ (⟦u⟧.pres ρ₁₂) (⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹)) .[]coe) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    (τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝)))
    ≡⟨ ap! (ρ₁₂ ⟦u⟧.⁻¹) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ
    ⌜ τ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.∘ᴰ (⟦u⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⌝)
    ≡⟨ ap! (⟦A⟧.∘∘⁻¹ᴰ τ (⟦u⟧.pres ρ₁₂) .[]coe) ⟩
    (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ)
    ≡⟨ sym (⟦A⟧.∘∘ᴰ (⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⟦A⟧.⁻¹ᴰ) 
                    (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) τ .[]coe) ⟩
    ((⌜ ⟦t⟧.pres (ρ₁₂ ⟦Γ⟧.⁻¹) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (ρ₁₂ ⟦t⟧.⁻¹) ⟩
    ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ τ
    ≡⟨ ⟦A⟧.⁻¹∘∘ᴰ (⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) τ .[]coe ⟩
    τ ∎
  ⟦Id⟧ .snd ._∘ᴰ_ = {!   !}
  ⟦Id⟧ .snd .coeG   ρ₁₂ τ
    = tr (⟦A⟧ .fst .Relᴰ _ _) (⟦Γ⟧.⁻¹∘id∘ ρ₁₂)
      ((⟦t⟧.pres ρ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⟦u⟧.pres ρ₁₂))
  ⟦Id⟧ .snd .id∘ᴰ _     = coe[] uip
  ⟦Id⟧ .snd .∘idᴰ _     = coe[] uip
  ⟦Id⟧ .snd .∘∘ᴰ  _ _ _ = coe[] uip
  ⟦Id⟧ .snd .∘⁻¹ᴰ _     = coe[] uip
  ⟦Id⟧ .snd .⁻¹∘ᴰ _     = coe[] uip
  ⟦Id⟧ .snd .cohG _ _   = refl
  -- Literally identical to the "idᴰ" case...
  ⟦Id⟧ .snd .coe-id {x = ρ} τ 
    rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    rewrite ⟦Γ⟧.id⁻¹ ρ
    -- Reflexive rewrites
    rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ) 
    rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ) =
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (τ ⟦A⟧.∘ᴰ ⌜ ⟦u⟧.pres (⟦Γ⟧.id ρ) ⌝)
    ≡⟨ ap! (⟦u⟧.id ρ) ⟩
    (⟦t⟧.pres (⟦Γ⟧.id ρ) ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⌜ τ ⟦A⟧.∘ᴰ ⟦A⟧.idᴰ (⟦u⟧.act ρ) ⌝
    ≡⟨ ap! (⟦A⟧.∘idᴰ τ .[]coe) ⟩
    (⌜ ⟦t⟧.pres (⟦Γ⟧.id ρ) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (⟦t⟧.id ρ) ⟩
    ⌜ ⟦A⟧.idᴰ (⟦t⟧ .act ρ) ⟦A⟧.⁻¹ᴰ ⌝ ⟦A⟧.∘ᴰ τ
    ≡⟨ ap! (⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ) .[]coe) ⟩
    ⟦A⟧.idᴰ (⟦t⟧ .act ρ) ⟦A⟧.∘ᴰ τ
    ≡⟨ ⟦A⟧.id∘ᴰ τ .[]coe ⟩
    τ ∎
  ⟦Id⟧ .snd .coe-∘     = {!   !}
  ⟦Id⟧ .snd .coh-id  τ = coe[] uip
  ⟦Id⟧ .snd .coh-∘ _ _ _ = coe[] uip

⟦refl⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Id⟧ ⟦A⟧ ⟦t⟧ ⟦t⟧)
⟦refl⟧ {⟦A⟧ = ⟦A⟧} .act ρ = ⟦A⟧ .snd .idᴰ _
⟦refl⟧ {⟦Γ⟧ = ⟦Γ⟧} {⟦A⟧ = ⟦A⟧} {⟦t⟧ = ⟦t⟧} .pres ρ₁₂
  = {!!}
  -- = coe _ ((⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._⁻¹ᴰ (⟦t⟧ .pres ρ₁₂)))
  --                          (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd .idᴰ _) (⟦t⟧ .pres ρ₁₂)))
  --   ≡⟨ sym (exttr (⟦Γ⟧ .snd .∘∘ _ _ _) (⟦A⟧ .snd .∘∘ᴰ _ _ _) .[]coe) ⟩
  --   coe ⌜ _ ⌝ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._⁻¹ᴰ (⟦t⟧ .pres ρ₁₂))
  --                                             (⟦A⟧ .snd .idᴰ _))
  --                             (⟦t⟧ .pres ρ₁₂))
  --   ≡⟨ ap! uip ⟩
  --   coe _ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._∘ᴰ_ (⟦A⟧ .snd ._⁻¹ᴰ (⟦t⟧ .pres ρ₁₂))
  --                                         (⟦A⟧ .snd .idᴰ _))
  --                         (⟦t⟧ .pres ρ₁₂))
  --   ≡⟨ ⁻¹∘id∘ᴰ (⟦A⟧ .snd) _ .[]coe ⟩
  --   ⟦A⟧ .snd .idᴰ _ ∎
⟦refl⟧ .id  _   = uip
⟦refl⟧ ._⁻¹ _   = uip
⟦refl⟧ ._∘_ _ _ = uip

-- We have a few options for how we want to deal with substitution laws
-- I think using global rewrite rules is reasonable?
-- Of course, we should prove these... (but most are easy)
postulate
  ⟦[id]T⟧ : ⟦[]T⟧ ⟦A⟧ ⟦id⟧ ≡ ⟦A⟧
  ⟦[][]T⟧ : ⟦[]T⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧) ⟦σ⟧ ≡ ⟦[]T⟧ ⟦A⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧) 
  ⟦Id[]T⟧ : ⟦[]T⟧ (⟦Id⟧ ⟦A⟧ ⟦t⟧ ⟦u⟧) ⟦δ⟧ 
          ≡ ⟦Id⟧ (⟦[]T⟧ ⟦A⟧ ⟦δ⟧) (⟦[]⟧ ⟦t⟧ ⟦δ⟧) (⟦[]⟧ ⟦u⟧ ⟦δ⟧)
  ⟦wk,⟧   : ⟦⨾⟧ ⟦wk⟧ (⟦,⟧ ⟦δ⟧ ⟦t⟧) ≡ ⟦δ⟧
{-# REWRITE ⟦[id]T⟧ ⟦[][]T⟧ ⟦Id[]T⟧ ⟦wk,⟧ #-}

postulate
  ⟦[id]⟧ : ⟦[]⟧ ⟦t⟧ ⟦id⟧ ≡ ⟦t⟧
  ⟦[][]⟧ : ⟦[]⟧ (⟦[]⟧ ⟦t⟧ ⟦δ⟧) ⟦σ⟧ ≡ ⟦[]⟧ ⟦t⟧ (⟦⨾⟧ ⟦δ⟧ ⟦σ⟧) 
  ⟦vz,⟧  : ⟦[]⟧ ⟦vz⟧ (⟦,⟧ ⟦δ⟧ ⟦u⟧) ≡ ⟦u⟧
{-# REWRITE ⟦[id]⟧ ⟦[][]⟧ ⟦vz,⟧ #-}

-- The J rule
module _ (⟦P⟧ : ⟦Ty⟧ (⟦▷⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) 
                     (⟦Id⟧ (⟦[]T⟧ ⟦A⟧ ⟦wk⟧) (⟦[]⟧ ⟦t⟧ ⟦wk⟧) ⟦vz⟧)))
         (⟦d⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ (⟦,⟧ (⟦,⟧ ⟦id⟧ ⟦t⟧) ⟦refl⟧)))
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

  ⟦J⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦[]T⟧ ⟦P⟧ (⟦,⟧ (⟦,⟧ ⟦id⟧ ⟦u⟧) ⟦p⟧))
  ⟦J⟧ .act ρ 
    rewrite ⟦Γ⟧.id⁻¹ ρ
    rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    -- Reflexive rewrites
    rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ)
    -- Back to non-reflexive
    rewrite ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ) .[]coe
    rewrite ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ) .[]coe
    = ⟦P⟧.coeG ((⟦Γ⟧.id ρ , ⟦p⟧.act ρ) , 
      ((⌜ ⟦t⟧.pres (⟦Γ⟧.id ρ) ⌝ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ⟦p⟧.act ρ 
      ≡⟨ ap! (⟦t⟧.id ρ) ⟩
      ⌜ ⟦A⟧.idᴰ (⟦t⟧.act ρ) ⟦A⟧.⁻¹ᴰ ⌝ ⟦A⟧.∘ᴰ ⟦p⟧.act ρ 
      ≡⟨ ap! (⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ) .[]coe) ⟩ 
      ⟦p⟧.act ρ ∎)) 
      (⟦d⟧.act ρ)
  ⟦J⟧ .pres {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ 
    rewrite ⟦Γ⟧.id⁻¹ ρ₁ 
    rewrite ⟦Γ⟧.id⁻¹ ρ₂
    rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₁)
    rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₂)
    rewrite ⟦Γ⟧.∘id ρ₁₂
    rewrite ⟦Γ⟧.id∘ ρ₁₂
    rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂
    -- Reflexive rewrites
    rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ₁)
    rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ₂)
    -- Back to non-reflexive
    rewrite ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ₁) .[]coe
    rewrite ⟦A⟧.id∘ᴰ (⟦p⟧.act ρ₂) .[]coe
    rewrite ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₁) .[]coe
    rewrite ⟦A⟧.⁻¹∘ᴰ (⟦p⟧.act ρ₂) .[]coe
    rewrite ⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ₁) .[]coe
    rewrite ⟦A⟧.id⁻¹ᴰ (⟦t⟧.act ρ₂) .[]coe
    rewrite ⟦t⟧.id ρ₁
    rewrite ⟦t⟧.id ρ₂
    using tmp ← (⟦P⟧.cohG ((⟦Γ⟧.id ρ₁ , ⟦p⟧.act ρ₁) , refl) (⟦d⟧.act ρ₁) ⟦P⟧.⁻¹ᴰ) ⟦P⟧.∘ᴰ (⟦d⟧.pres ρ₁₂ ⟦P⟧.∘ᴰ ⟦P⟧.cohG ((⟦Γ⟧.id ρ₂ , ⟦p⟧.act ρ₂) , refl) (⟦d⟧.act ρ₂))
    = tr (⟦P⟧ .fst .Relᴰ 
         (⟦P⟧.coeG ((⟦Γ⟧.id ρ₁ , ⟦p⟧.act ρ₁) , refl) (⟦d⟧.act ρ₁)) 
         (⟦P⟧.coeG ((⟦Γ⟧.id ρ₂ , ⟦p⟧.act ρ₂) , refl) (⟦d⟧.act ρ₂))) 
         (apd₂ _,_ (apd₂ _,_ refl 
         {!⟦p⟧.pres ρ₁₂!}) 
         {!!}) 
         tmp
  ⟦J⟧ .id   = {!   !}
  ⟦J⟧ ._⁻¹  = {!   !}
  ⟦J⟧ ._∘_  = {!   !}
