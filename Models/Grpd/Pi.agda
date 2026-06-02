{-# OPTIONS --smart-with #-}

open import Utils
open import Utils.WithK
open import Utils.Macro

open import Models.Grpd.Grpd
open import Models.Grpd.Motives
open import Models.Grpd.Subst

-- Pi types
module Models.Grpd.Pi where

-- Pi types
module _ (⟦A⟧ : ⟦Ty⟧ ⟦Γ⟧) (⟦B⟧ : ⟦Ty⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧)) where
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦B⟧ = Grpdᴰ.Data (⟦B⟧ .snd)

  -- Dependent natural transformations from ⟦A⟧ to ⟦B⟧
  record ΠCar (ρ : ⟦Γ⟧ .fst .Car) : Set where
    constructor mk
    field
      act  : (υ : ⟦A⟧ .fst .Carᴰ ρ) → ⟦B⟧ .fst .Carᴰ (ρ , υ)
      pres : ∀ {υ₁ υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ (⟦Γ⟧.id ρ))
           → ⟦B⟧ .fst .Relᴰ (act υ₁) (act υ₂) (⟦Γ⟧.id ρ , υ₁₂)
      
      id   : (υ : ⟦A⟧ .fst .Carᴰ ρ) → pres (⟦A⟧.idᴰ υ) ≡ ⟦B⟧.idᴰ (act υ)
      _⁻¹  : ∀ {υ₁ υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ (⟦Γ⟧.id ρ))
           → pres (tr (⟦A⟧ .fst .Relᴰ _ _) (⟦Γ⟧.id⁻¹ ρ) (υ₁₂ ⟦A⟧.⁻¹ᴰ)) 
           ≡[ ap (⟦B⟧ .fst .Relᴰ _ _) 
                 (apd₂ _,_ (sym (⟦Γ⟧.id⁻¹ ρ)) (coe[] (sym-tr (⟦Γ⟧.id⁻¹ ρ)))) 
           ]≡ pres υ₁₂ ⟦B⟧.⁻¹ᴰ
      _∘_  : ∀ {υ₁ υ₂ υ₃} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ (⟦Γ⟧.id ρ))
                          (υ₂₃ : ⟦A⟧ .fst .Relᴰ υ₂ υ₃ (⟦Γ⟧.id ρ))
           → pres (tr (⟦A⟧ .fst .Relᴰ _ _) (⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)) (υ₁₂ ⟦A⟧.∘ᴰ υ₂₃))
           ≡[ ap (⟦B⟧ .fst .Relᴰ _ _) 
                 (apd₂ _,_ (sym (⟦Γ⟧.id∘ (⟦Γ⟧.id ρ))) 
                           (coe[] (sym-tr (⟦Γ⟧.id∘ (⟦Γ⟧.id ρ))))) 
           ]≡ pres υ₁₂ ⟦B⟧.∘ᴰ pres υ₂₃
      coeG : (ρ~ : ⟦Γ⟧ .fst .Rel ρ ρ) (υ : ⟦A⟧ .fst .Carᴰ ρ)
           → act (⟦A⟧.coeG ρ~ υ) ≡ ⟦B⟧.coeG (ρ~ , ⟦A⟧.cohG ρ~ υ) (act υ)
  open ΠCar public
  
  module ΠCarExtras {ρ : ⟦Γ⟧ .fst .Car} (τ : ΠCar ρ) where
    private module τ = ΠCar τ
    ΠcohG : (υ : ⟦A⟧ .fst .Carᴰ ρ)
          →  τ.pres (⟦A⟧.cohG (⟦Γ⟧.id ρ) υ) 
          ≡[ ap (λ □ → ⟦B⟧ .fst .Relᴰ _ □ _) (τ.coeG (⟦Γ⟧.id ρ) υ)
          ]≡ ⟦B⟧.cohG (⟦Γ⟧.id ρ , ⟦A⟧.cohG (⟦Γ⟧.id ρ) υ) (τ.act υ)
    ΠcohG υ 
      rewrite ⟦A⟧.coe-id υ
      rewrite ⟦A⟧.coh-id υ .[]coe
      rewrite ⟦B⟧.coe-id (τ.act υ)
      rewrite ⟦B⟧.coh-id (τ .act υ) .[]coe
      -- Reflexive rewrites
      rewrite τ.coeG (⟦Γ⟧.id ρ) υ 
      = coe[] (τ.id υ)

  -- Relating preservations involves a lot of transport hell, so we forward
  -- declare the type of that field (in order to use "smart rewrite")
  module ΠRelHelper {ρ₁ ρ₂} (τ₁ : ΠCar ρ₁) (τ₂ : ΠCar ρ₂) 
                    (ρ₁₂ : ⟦Γ⟧ .fst .Rel ρ₁ ρ₂) 
         where
    private
      module τ₁ = ΠCar τ₁
      module τ₂ = ΠCar τ₂
    module Fields (act₁ : (υ : ⟦A⟧ .fst .Carᴰ ρ₁) 
                        → ⟦B⟧ .fst .Relᴰ (τ₁.act υ) (τ₂.act (⟦A⟧.coeG ρ₁₂ υ)) 
                                         (ρ₁₂ , ⟦A⟧.cohG ρ₁₂ υ))
                  where
      act₂ : (υ : ⟦A⟧ .fst .Carᴰ ρ₂) 
           → ⟦B⟧ .fst .Relᴰ (τ₁.act (⟦A⟧.coeG⁻¹ ρ₁₂ υ)) (τ₂.act υ) 
                            (ρ₁₂ , ⟦A⟧.cohG⁻¹ ρ₁₂ υ)
      act₂ υ 
        rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂ 
        rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂
        rewrite ⟦A⟧.coe-id υ
        rewrite sym (⟦A⟧.coe-∘ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂ υ)
        = tr (λ □ → ⟦B⟧ .fst .Relᴰ (τ₁.act _) _ (ρ₁₂ , □)) 
             (⟦A⟧.coh-coe⁻¹ ρ₁₂ υ .[]coe) 
             (act₁ (⟦A⟧.coeG⁻¹ ρ₁₂ υ))

      Pres : ∀ {υ₁ υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ ρ₁₂) → Set
      Pres {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂ 
        rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂ 
        rewrite ⟦Γ⟧.∘⁻¹ ρ₁₂ 
        rewrite ⟦Γ⟧.id∘ ρ₁₂
        rewrite ⟦Γ⟧.∘id ρ₁₂
        rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
        -- Reflexive rewrites
        rewrite ⟦Γ⟧.∘∘ ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂
        rewrite ⟦Γ⟧.∘⁻¹ (ρ₁₂ ⟦Γ⟧.⁻¹)
        = act₁ υ₁ ⟦B⟧.∘ᴰ 
          τ₂.pres ((⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ υ₁₂) 
        ≡[ ap (λ □ → ⟦B⟧ .fst .Relᴰ _ _ (ρ₁₂ , □)) 
              (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.∘ᴰ ((⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ υ₁₂)
              ≡⟨ sym (⟦A⟧.∘∘ᴰ (⟦A⟧.cohG ρ₁₂ υ₁) 
                              (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ) υ₁₂ .[]coe) ⟩
              (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.∘ᴰ (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ υ₁₂
              ≡⟨ ⟦A⟧.⟨∘⁻¹⟩∘ᴰ (⟦A⟧.cohG ρ₁₂ υ₁) υ₁₂ .[]coe ⟩
              υ₁₂
              ≡⟨ sym (⟦A⟧.∘∘⁻¹ᴰ υ₁₂ (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂) .[]coe) ⟩
              υ₁₂ ⟦A⟧.∘ᴰ (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.∘ᴰ 
              (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ))
              ≡⟨ sym (⟦A⟧.∘∘ᴰ υ₁₂ (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂)
                              (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ) .[]coe) ⟩
              (υ₁₂ ⟦A⟧.∘ᴰ ⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂) ⟦A⟧.∘ᴰ
              (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ) ∎)
        ]≡ τ₁.pres (υ₁₂ ⟦A⟧.∘ᴰ ⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂)
           ⟦B⟧.∘ᴰ act₂ υ₂

  record ΠRel {ρ₁ ρ₂} (τ₁ : ΠCar ρ₁) (τ₂ : ΠCar ρ₂) 
              (ρ₁₂ : ⟦Γ⟧ .fst .Rel ρ₁ ρ₂) : Set where
    private
      module τ₁ = ΠCar τ₁
      module τ₂ = ΠCar τ₂
    field
      act₁ : (υ : ⟦A⟧ .fst .Carᴰ ρ₁) 
           → ⟦B⟧ .fst .Relᴰ (τ₁.act υ)(τ₂.act (⟦A⟧.coeG ρ₁₂ υ)) 
                            (ρ₁₂ , ⟦A⟧.cohG ρ₁₂ υ)
   
    open ΠRelHelper.Fields τ₁ τ₂ ρ₁₂ act₁ public

    field  
      pres : ∀ {υ₁ υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ ρ₁₂)
           → Pres υ₁₂
  open ΠRel public

  -- opaque
  --   πcar≡'' : ∀ {ρ} {τ₁ τ₂ : ΠCar ρ} (act≡ : τ₁ .act ≡ τ₂ .act) 
  --           →  (λ {υ₁ υ₂} → τ₁ .pres {υ₁} {υ₂}) 
  --           ≡[ ( piexti λ {υ₁} → piexti λ {υ₂} → piext λ υ₁₂ 
  --              → ap (λ □ → ⟦B⟧ .fst .Relᴰ (□ υ₁) (□ υ₂) _) act≡) 
  --           ]≡ τ₂ .pres
  --           → τ₁ ≡ τ₂
  --   πcar≡'' refl refl[] = refl

  --   πcar≡' : ∀ {ρ} {τ₁ τ₂ : ΠCar ρ} (act≡ : τ₁ .act ≡ τ₂ .act) 
  --          → (∀ {υ₁ υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ (⟦Γ⟧.id ρ))
  --             →  τ₁ .pres υ₁₂ 
  --             ≡[ ap (λ □ → ⟦B⟧ .fst .Relᴰ (□ υ₁) (□ υ₂) _) act≡ 
  --             ]≡ τ₂ .pres υ₁₂)
  --          → τ₁ ≡ τ₂
  --   πcar≡' refl pres≡ 
  --     = πcar≡'' refl 
  --       ( coe[] (funexti λ {υ₁} → funexti λ {υ₂} → funext λ υ₁₂ 
  --       → pres≡ υ₁₂ .[]coe))

  --   πcar≡ : ∀ {ρ} {τ₁ τ₂ : ΠCar ρ} (act≡ : ∀ υ → τ₁ .act υ ≡ τ₂ .act υ) 
  --          → (∀ {υ₁ υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ (⟦Γ⟧.id ρ))
  --             →  τ₁ .pres υ₁₂ 
  --             ≡[ ap₂ (λ □₁ □₂ → ⟦B⟧ .fst .Relᴰ □₁ □₂ _) (act≡ υ₁) (act≡ υ₂) 
  --             ]≡ τ₂ .pres υ₁₂)
  --          → τ₁ ≡ τ₂
  --   πcar≡ act≡ pres≡ = πcar≡' (funext λ υ → act≡ υ) λ υ₁₂ → reix[] (pres≡ υ₁₂)

  ⟦Π⟧ : ⟦Ty⟧ ⟦Γ⟧
  ⟦Π⟧ .fst .Carᴰ ρ         
    = ΠCar ρ
  ⟦Π⟧ .fst .Relᴰ τ₁ τ₂ ρ₁₂ 
    = ΠRel τ₁ τ₂ ρ₁₂
  ⟦Π⟧ .snd .idᴰ τ .act₁ υ 
    = τ .pres (⟦A⟧.cohG (⟦Γ⟧.id _) υ)
  ⟦Π⟧ .snd .idᴰ {x = ρ} τ .pres {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂ 
    = {!!}
    -- Below works, but takes like 10 seconds to typecheck...
    -- rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    -- rewrite ⟦Γ⟧.id⁻¹ ρ
    -- -- Reflexive rewrites
    -- rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ)
    -- rewrite ⟦Γ⟧.∘⁻¹ (⟦Γ⟧.id ρ)
    -- rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ)
    -- rewrite ⟦Γ⟧.⁻¹⁻¹ (⟦Γ⟧.id ρ)
    -- rewrite ⟦Γ⟧.∘∘ (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ)
    -- rewrite ⟦A⟧.id∘ᴰ υ₁₂ .[]coe
    -- rewrite ⟦A⟧.∘idᴰ υ₁₂ .[]coe
    -- rewrite ⟦A⟧.id∘ᴰ (⟦A⟧.idᴰ υ₁) .[]coe
    -- rewrite ⟦A⟧.id∘ᴰ (⟦A⟧.idᴰ υ₂) .[]coe
    -- rewrite ⟦A⟧.id⁻¹ᴰ υ₁ .[]coe
    -- rewrite ⟦A⟧.id⁻¹ᴰ υ₂ .[]coe
    -- rewrite ⟦A⟧.coe-id υ₁
    -- rewrite ⟦A⟧.coh-id υ₁ .[]coe
    -- rewrite ⟦A⟧.coe-id υ₂
    -- rewrite ⟦A⟧.coh-id υ₂ .[]coe
    -- -- Reflexive rewrites
    -- rewrite ⟦A⟧.∘idᴰ (⟦A⟧.idᴰ υ₂) .[]coe
    -- rewrite ⟦A⟧.∘⁻¹ᴰ (⟦A⟧.idᴰ υ₁) .[]coe
    -- rewrite ⟦A⟧.∘⁻¹ᴰ (⟦A⟧.idᴰ υ₂) .[]coe
    -- rewrite ⟦A⟧.∘∘ᴰ (⟦A⟧.idᴰ υ₁) (⟦A⟧.idᴰ υ₁) υ₁₂ .[]coe
    -- rewrite ⟦A⟧.∘∘ᴰ υ₁₂ (⟦A⟧.idᴰ υ₂) (⟦A⟧.idᴰ υ₂) .[]coe
    -- rewrite ⟦A⟧.∘∘ᴰ (⟦A⟧.idᴰ υ₂) (⟦A⟧.idᴰ υ₂) (⟦A⟧.idᴰ υ₂) .[]coe
    -- rewrite ⟦A⟧.coe-∘ (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ) υ₂
    -- rewrite ⟦A⟧.coh-∘ (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ) υ₂ .[]coe
    -- = coe[] 
    -- (⌜ τ .pres (⟦A⟧.idᴰ υ₁) ⌝ ⟦B⟧.∘ᴰ τ .pres υ₁₂
    -- ≡⟨ ap! (τ .id υ₁) ⟩
    -- ⟦B⟧.idᴰ (act τ υ₁) ⟦B⟧.∘ᴰ τ .pres υ₁₂
    -- ≡⟨ ⟦B⟧.id∘idᴰ (pres τ υ₁₂) .[]coe ⟩
    -- τ .pres υ₁₂ ⟦B⟧.∘ᴰ ⌜ ⟦B⟧.idᴰ (act τ υ₂) ⌝
    -- ≡⟨ ap! (sym (τ .id υ₂)) ⟩
    -- τ .pres υ₁₂ ⟦B⟧.∘ᴰ τ .pres (⟦A⟧.idᴰ υ₂) ∎)
  ⟦Π⟧ .snd ._⁻¹ᴰ {x₁₂ = ρ₁₂} {x₁ᴰ = τ₁} {x₂ᴰ = τ₂} τ₁₂ .act₁ υ
    = {!!}
  ⟦Π⟧ .snd ._⁻¹ᴰ {x₁₂ = ρ₁₂} {x₁ᴰ = τ₁} {x₂ᴰ = τ₂} τ₁₂ .pres 
    {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂ 
    = {!!} 
  --   = {!τ₁ .pres!}
  --   -- rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
  --   -- rewrite ⟦Γ⟧.⁻¹⁻¹ (ρ₁₂ ⟦Γ⟧.⁻¹)
  --   -- rewrite ⟦A⟧.⁻¹⁻¹ᴰ υ₁₂ .[]coe
  --   -- = τ₁₂ (υ₁₂ ⟦A⟧.⁻¹ᴰ) ⟦B⟧.⁻¹ᴰ
  --   -- > using υ₂₁ ← tr (⟦A⟧ .fst .Relᴰ _ _) (⁻¹⁻¹ (⟦Γ⟧ .snd)) (⟦A⟧ .snd ._⁻¹ᴰ υ₁₂)
  --   -- > = tr (⟦B⟧ .fst .Relᴰ _ _) (ap (_ ,_) 
  --   -- > (⟦A⟧ .snd ._⁻¹ᴰ υ₂₁
  --   -- > ≡⟨ sym (apdd₂-K (Relᴰ (⟦A⟧ .fst) υ₂ υ₁) (λ _ → ⟦A⟧ .snd ._⁻¹ᴰ)  
  --   -- >        (⁻¹⁻¹ (⟦Γ⟧ .snd)) .[]coe) ⟩ 
  --   -- > tr (⟦A⟧ .fst .Relᴰ _ _) (⁻¹⁻¹ (⟦Γ⟧ .snd)) 
  --   -- >        (⟦A⟧ .snd ._⁻¹ᴰ (⟦A⟧ .snd ._⁻¹ᴰ υ₁₂))
  --   -- > ≡⟨ ⁻¹⁻¹ᴰ (⟦A⟧ .snd) .[]coe ⟩
  --   -- > υ₁₂ ∎)) (⟦B⟧ .snd ._⁻¹ᴰ (τ₁₂ υ₂₁))
  ⟦Π⟧ .snd ._∘ᴰ_ {x₁₂ = ρ₁₂} {x₂₃ = ρ₂₃} {x₁ᴰ = τ₁} {x₂ᴰ = τ₂} {x₃ᴰ = τ₃} 
                 τ₁₂ τ₂₃ .act₁ υ
    = {!!}
  ⟦Π⟧ .snd ._∘ᴰ_ {x₁₂ = ρ₁₂} {x₂₃ = ρ₂₃} {x₁ᴰ = τ₁} {x₂ᴰ = τ₂} {x₃ᴰ = τ₃} 
                 τ₁₂ τ₂₃ .pres {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂ 
    = {!!}
  --   rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₂₃
  --   rewrite ⟦Γ⟧.∘id ρ₁₂
  --   rewrite ⟦Γ⟧.∘id (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃)
  --   rewrite ⟦Γ⟧.∘⁻¹ ρ₂₃
  --   rewrite ⟦Γ⟧.⁻¹∘ ρ₂₃ 
  --   rewrite ⟦Γ⟧.∘∘ ρ₁₂ ρ₂₃ (ρ₂₃ ⟦Γ⟧.⁻¹)
  --   -- Reflexive rewrites
  --   rewrite ⟦Γ⟧.∘⁻¹ (ρ₂₃ ⟦Γ⟧.⁻¹)
  --   rewrite ⟦Γ⟧.∘∘ (ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) (ρ₂₃ ⟦Γ⟧.⁻¹) ρ₂₃
  --   using τυ₁₃ ← τ₁₂ (υ₁₂ ⟦A⟧.∘ᴰ ⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) _) ⟦B⟧.∘ᴰ 
  --                τ₂₃ (⟦A⟧.cohG⁻¹ ρ₂₃ _) = 
  --   tr (λ □ → ⟦B⟧ .fst .Relᴰ _ _ ((ρ₁₂ ⟦Γ⟧.∘ ρ₂₃) , □)) 
  --   ((υ₁₂ ⟦A⟧.∘ᴰ ⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) υ₂) ⟦A⟧.∘ᴰ
  --    (⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ)
  --   ≡⟨ ⟦A⟧.∘∘ᴰ υ₁₂ (⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) υ₂) 
  --              (⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ) .[]coe ⟩
  --   υ₁₂ ⟦A⟧.∘ᴰ 
  --   (⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.∘ᴰ (⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ))
  --   ≡⟨ ⟦A⟧.∘∘⁻¹ᴰ υ₁₂ (⟦A⟧.cohG (ρ₂₃ ⟦Γ⟧.⁻¹) υ₂) .[]coe ⟩
  --   υ₁₂ ∎)
  --   τυ₁₃
  ⟦Π⟧ .snd .id∘ᴰ {x₁ = ρ₁} {x₂ = ρ₂} {x₁₂ = ρ₁₂} {x₁ᴰ = τ₁} {x₂ᴰ = τ₂} τ₁₂
    = {!!}
  --   = coe[] (funexti λ {υ₁} → funexti λ {υ₂} → funext λ υ₁₂ → go υ₁₂) where 
  --   go : ∀ {υ₁} {υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ ρ₁₂)
  --      → tr (Relᴰ (fst ⟦Π⟧) τ₁ τ₂) (⟦Γ⟧.id∘ ρ₁₂) 
  --           (⟦Π⟧ .snd ._∘ᴰ_ (⟦Π⟧ .snd .idᴰ τ₁) τ₁₂) υ₁₂
  --      ≡ τ₁₂ υ₁₂
  --   go {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂ 
  --     rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
  --     rewrite ⟦Γ⟧.id∘ ρ₁₂
  --     rewrite ⟦Γ⟧.∘id ρ₁₂
  --     rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ₁)
  --     rewrite ⟦Γ⟧.∘⁻¹ ρ₁₂
  --     rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂
  --     -- Reflexive rewrites
  --     rewrite ⟦Γ⟧.∘∘ (⟦Γ⟧.id ρ₁) ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹)
  --     rewrite ⟦Γ⟧.∘⁻¹ (ρ₁₂ ⟦Γ⟧.⁻¹)
  --     rewrite ⟦Γ⟧.∘∘ ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂
  --     -- Back to non-reflexive rewrites
  --     rewrite ⟦A⟧.∘idᴰ υ₁₂ .[]coe
  --     rewrite ⟦A⟧.∘⁻¹ᴰ (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂) .[]coe
  --     rewrite ⟦A⟧.∘∘ᴰ υ₁₂ (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂)
  --                         (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ) .[]coe = 
  --     τ₁ .pres (υ₁₂ ⟦A⟧.∘ᴰ ⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂) ⟦B⟧.∘ᴰ
  --     τ₁₂ (⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂ ⟦A⟧.⁻¹ᴰ)
  --     ≡⟨ {!!} ⟩
  --     τ₁₂ υ₁₂ ∎
  --     --   ∀ {υ₁} {υ₂} (υ₁₂ : ⟦A⟧ .fst .Relᴰ υ₁ υ₂ ρ₁₂) 
  --     --  → ⟦Π⟧ .snd ._∘ᴰ_ (⟦Π⟧ .snd .idᴰ τ₁) τ₁₂ υ₁₂ 
  --     --  ≡ τ₁₂ υ₁₂
  --   -- go
  --   --   rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
  --   --   rewrite ⟦Γ⟧.id∘ ρ₁₂
  --   --   rewrite ⟦Γ⟧.∘id ρ₁₂
  --   --   rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ₁) =
  --   -- -- -- Reflexive rewrites
  --   -- -- = coe[]
  --   -- -- (funexti λ {υ₁} → funexti λ {υ₂} → funext λ υ₁₂ → {!!})
  --   --   coe[] {!funexti λ {υ₁} → funexti λ {υ₂} → funext λ υ₁₂ → _!}
      
  ⟦Π⟧ .snd .∘idᴰ   = {!   !}
  ⟦Π⟧ .snd .∘∘ᴰ    = {!   !}
  ⟦Π⟧ .snd .∘⁻¹ᴰ   = {!   !}
  ⟦Π⟧ .snd .⁻¹∘ᴰ   = {!   !}
  ⟦Π⟧ .snd .coeG ρ₁₂ τ .act υ
    = {!!}
  --   = ⟦B⟧ .snd .coeG (ρ₁₂ , ⟦A⟧.cohG⁻¹ ρ₁₂ υ) 
  --                    (τ .act (⟦A⟧.coeG⁻¹ ρ₁₂ υ))
  ⟦Π⟧ .snd .coeG {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ τ .pres {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂
    = {!!}
  --   rewrite ⟦Γ⟧.id∘ ρ₁₂
  --   rewrite ⟦Γ⟧.id∘ (ρ₁₂ ⟦Γ⟧.⁻¹)
  --   rewrite ⟦Γ⟧.∘id ρ₁₂
  --   rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂
  --   rewrite ⟦Γ⟧.∘⁻¹ ρ₁₂
  --   rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
  --   rewrite (⟦Γ⟧.id∘ (⟦Γ⟧.id ρ₂))
  --   -- Reflexive rewrites
  --   rewrite ⟦Γ⟧.⁻¹∘ (ρ₁₂ ⟦Γ⟧.⁻¹)
  --   rewrite ⟦Γ⟧.∘∘ ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂
  --   rewrite ⟦Γ⟧.∘∘ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂ (⟦Γ⟧.id ρ₂)
  --   rewrite ⟦Γ⟧.∘∘ (⟦Γ⟧.id ρ₂) (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂
  --   rewrite ⟦Γ⟧.∘⁻¹ (ρ₁₂ ⟦Γ⟧.⁻¹)
  --   rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ₂)
  --   using τυ₁₂    ← τ .pres (coeG⁻¹~ (⟦A⟧ .snd) {x₂₁ = ρ₁₂} υ₁₂)
  --         | υcoh₁ ← ⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₁
  --         | υcoh₂ ← ⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂
  --   = tr (λ □ → ⟦B⟧ .fst .Relᴰ _ _ (_ , □)) 
  --        ((υcoh₁ ⟦A⟧.⁻¹ᴰ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
  --         ⌜ ((υcoh₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (υ₁₂ ⟦A⟧.∘ᴰ υcoh₂)) ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ) ⌝
  --        ≡⟨ ap! (⟦A⟧.∘∘ᴰ (υcoh₁ ⟦A⟧.⁻¹ᴰ) (υ₁₂ ⟦A⟧.∘ᴰ υcoh₂) 
  --                        (υcoh₂ ⟦A⟧.⁻¹ᴰ) .[]coe) ⟩
  --        (υcoh₁ ⟦A⟧.⁻¹ᴰ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ ((υcoh₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ 
  --        ((υ₁₂ ⟦A⟧.∘ᴰ υcoh₂) ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ)))
  --        ≡⟨ sym (⟦A⟧.∘∘ᴰ (υcoh₁ ⟦A⟧.⁻¹ᴰ ⟦A⟧.⁻¹ᴰ) (υcoh₁ ⟦A⟧.⁻¹ᴰ) 
  --                        ((υ₁₂ ⟦A⟧.∘ᴰ υcoh₂) ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ)) .[]coe) ⟩
  --        ((υcoh₁ ⟦A⟧.⁻¹ᴰ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ (υcoh₁ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ 
  --        ((υ₁₂ ⟦A⟧.∘ᴰ υcoh₂) ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ))
  --        ≡⟨ ⟦A⟧.⁻¹∘∘ᴰ (υcoh₁ ⟦A⟧.⁻¹ᴰ) _ .[]coe ⟩
  --        (υ₁₂ ⟦A⟧.∘ᴰ υcoh₂) ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ)
  --        ≡⟨ ⟦A⟧.∘∘ᴰ υ₁₂ υcoh₂ (υcoh₂ ⟦A⟧.⁻¹ᴰ) .[]coe ⟩
  --        υ₁₂ ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ))
  --        ≡⟨ ⟦A⟧.∘∘⁻¹ᴰ υ₁₂ υcoh₂ .[]coe ⟩
  --        υ₁₂ ∎)
  --        ((⟦B⟧.cohG _ _ ⟦B⟧.⁻¹ᴰ) ⟦B⟧.∘ᴰ (τυ₁₂ ⟦B⟧.∘ᴰ ⟦B⟧.cohG _ _))
  ⟦Π⟧ .snd .coeG {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ τ .id   = {!   !}
  ⟦Π⟧ .snd .coeG {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ τ ._⁻¹  = {!   !}
  ⟦Π⟧ .snd .coeG {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ τ ._∘_  = {!   !}
  ⟦Π⟧ .snd .coeG {x₁ = ρ₁} {x₂ = ρ₂} ρ₁₂ τ .coeG = {!   !}
  ⟦Π⟧ .snd .cohG ρ₁₂ τ .act₁ υ = {!!}
  ⟦Π⟧ .snd .cohG ρ₁₂ τ .pres {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂ = {!!}
  --   rewrite ⟦Γ⟧.⁻¹⁻¹ ρ₁₂
  --   rewrite ⟦Γ⟧.∘⁻¹ ρ₁₂
  --   rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂
  --   rewrite ⟦Γ⟧.id∘ ρ₁₂
  --   rewrite ⟦Γ⟧.∘id ρ₁₂
  --   -- Reflexive rewrites
  --   rewrite ⟦Γ⟧.∘∘ ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂
  --   rewrite ⟦Γ⟧.∘⁻¹ (ρ₁₂ ⟦Γ⟧.⁻¹)
  --   using υcoe₂ ← ⟦A⟧.coeG⁻¹ ρ₁₂ υ₂
  --       | υcoh₂ ← ⟦A⟧.cohG (ρ₁₂ ⟦Γ⟧.⁻¹) υ₂
  --       | τυ~   ← τ .pres (υ₁₂ ⟦A⟧.∘ᴰ υcoh₂) ⟦B⟧.∘ᴰ 
  --                 ⟦B⟧.cohG (ρ₁₂ , υcoh₂ ⟦A⟧.⁻¹ᴰ) (τ .act υcoe₂)
  --   = tr (λ □ → ⟦B⟧ .fst .Relᴰ _ _ (ρ₁₂ , □)) 
  --        ((υ₁₂ ⟦A⟧.∘ᴰ υcoh₂) ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ)
  --        ≡⟨ ⟦A⟧.∘∘ᴰ υ₁₂ υcoh₂ (υcoh₂ ⟦A⟧.⁻¹ᴰ) .[]coe ⟩
  --        υ₁₂ ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.∘ᴰ (υcoh₂ ⟦A⟧.⁻¹ᴰ))
  --        ≡⟨ ⟦A⟧.∘∘⁻¹ᴰ υ₁₂ υcoh₂ .[]coe ⟩
  --        υ₁₂ ∎) τυ~
  ⟦Π⟧ .snd .coe-id {x = ρ} τ = {!!}
  --   = πcar≡ go₁ go₂ where
  --   go₁ : ∀ υ 
  --       → ⟦B⟧.coeG 
  --         (⟦Γ⟧.id ρ , tr (Relᴰ (fst ⟦A⟧) (⟦A⟧.coeG (⟦Γ⟧.id ρ ⟦Γ⟧.⁻¹) υ) υ)
  --         (⟦Γ⟧.⁻¹⁻¹ (⟦Γ⟧.id ρ)) (⟦A⟧.cohG (⟦Γ⟧.id ρ ⟦Γ⟧.⁻¹) _ ⟦A⟧.⁻¹ᴰ))
  --         (τ .act (⟦A⟧.coeG (⟦Γ⟧.id ρ ⟦Γ⟧.⁻¹) υ))
  --       ≡ τ .act υ
  --   go₁ υ 
  --     rewrite ⟦Γ⟧.id⁻¹ ρ
  --     rewrite ⟦Γ⟧.⁻¹⁻¹ (⟦Γ⟧.id ρ)
  --     rewrite ⟦A⟧.coe-id υ
  --     rewrite ⟦A⟧.coh-id υ .[]coe
  --     rewrite ⟦A⟧.id⁻¹ᴰ υ .[]coe
  --     = ⟦B⟧.coe-id (τ .act υ)
  --   go₂ : {υ₁ υ₂ : Carᴰ (⟦A⟧ .fst) ρ}
  --         (υ₁₂ : Relᴰ (⟦A⟧ .fst) υ₁ υ₂ (⟦Γ⟧.id ρ)) 
  --       →  ⟦Π⟧ .snd .coeG (⟦Γ⟧.id ρ) τ .pres υ₁₂
  --       ≡[ ap₂ (λ □₁ □₂ → Relᴰ (⟦B⟧ .fst) □₁ □₂ (⟦Γ⟧.id ρ , υ₁₂)) 
  --              (go₁ υ₁) (go₁ υ₂)
  --       ]≡ τ .pres υ₁₂
  --   go₂ {υ₁ = υ₁} {υ₂ = υ₂} υ₁₂ = {!!} 
  --     -- rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ)
  --     -- rewrite ⟦Γ⟧.id⁻¹ ρ
  --     -- -- Reflexive rewrites
  --     -- rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
  --     -- rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ)
  --     -- rewrite ⟦Γ⟧.∘⁻¹ (⟦Γ⟧.id ρ)
  --     -- rewrite ⟦Γ⟧.⁻¹⁻¹ (⟦Γ⟧.id ρ)
  --     -- rewrite ⟦Γ⟧.∘∘ (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ)
  --     -- -- Back to non-reflexive
  --     -- rewrite ⟦A⟧.coe-id υ₁
  --     -- rewrite ⟦A⟧.coh-id υ₁ .[]coe
  --     -- rewrite ⟦A⟧.coe-id υ₂
  --     -- rewrite ⟦A⟧.coh-id υ₂ .[]coe
  --     -- rewrite ⟦A⟧.∘idᴰ (⟦A⟧.idᴰ υ₁) .[]coe
  --     -- rewrite ⟦A⟧.id⁻¹ᴰ υ₁ .[]coe
  --     -- rewrite ⟦A⟧.∘idᴰ (⟦A⟧.idᴰ υ₂) .[]coe
  --     -- rewrite ⟦A⟧.id⁻¹ᴰ υ₂ .[]coe
  --     -- rewrite ⟦A⟧.id∘ᴰ υ₁₂ .[]coe
  --     -- rewrite ⟦A⟧.∘idᴰ υ₁₂ .[]coe
  --     -- -- Some more reflexive rewrites...
  --     -- rewrite ⟦A⟧.∘∘ᴰ (⟦A⟧.idᴰ υ₁) (⟦A⟧.idᴰ υ₁) υ₁₂ .[]coe
  --     -- rewrite ⟦A⟧.∘∘ᴰ υ₁₂ (⟦A⟧.idᴰ υ₂) (⟦A⟧.idᴰ υ₂) .[]coe
  --     -- rewrite ⟦A⟧.∘∘ᴰ (⟦A⟧.idᴰ υ₁) υ₁₂ (⟦A⟧.idᴰ υ₂) .[]coe
  --     -- rewrite ⟦A⟧.⁻¹∘ᴰ (⟦A⟧.idᴰ υ₁) .[]coe
  --     -- rewrite ⟦A⟧.∘⁻¹ᴰ (⟦A⟧.idᴰ υ₂) .[]coe
  --     -- -- And finally some more non-reflexive rewrites
  --     -- rewrite ⟦B⟧.coe-id (τ .act υ₁)
  --     -- rewrite ⟦B⟧.coe-id (τ .act υ₂)
  --     -- = coe[] 
  --     -- ((⟦B⟧.cohG (⟦Γ⟧.id ρ , ⟦A⟧.idᴰ υ₁) (τ .act υ₁) ⟦B⟧.⁻¹ᴰ) ⟦B⟧.∘ᴰ
  --     --  (τ .nat υ₁₂ ⟦B⟧.∘ᴰ ⌜ ⟦B⟧.cohG (⟦Γ⟧.id ρ , ⟦A⟧.idᴰ υ₂) (τ .act υ₂) ⌝)
  --     -- ≡⟨ ap! (⟦B⟧.coh-id (τ .act υ₂) .[]coe) ⟩
  --     -- (⌜ ⟦B⟧.cohG (⟦Γ⟧.id ρ , ⟦A⟧.idᴰ υ₁) (τ .act υ₁) ⌝ ⟦B⟧.⁻¹ᴰ) ⟦B⟧.∘ᴰ
  --     -- (τ .nat υ₁₂ ⟦B⟧.∘ᴰ ⟦B⟧.idᴰ (τ .act υ₂))
  --     -- ≡⟨ ap! (⟦B⟧.coh-id (τ .act υ₁) .[]coe) ⟩
  --     -- (⟦B⟧.idᴰ (τ .act υ₁) ⟦B⟧.⁻¹ᴰ) ⟦B⟧.∘ᴰ 
  --     -- ⌜ τ .nat υ₁₂ ⟦B⟧.∘ᴰ ⟦B⟧.idᴰ (τ .act υ₂) ⌝
  --     -- ≡⟨ ap! (⟦B⟧.∘idᴰ (τ .nat υ₁₂) .[]coe) ⟩ 
  --     -- ⌜ ⟦B⟧.idᴰ (τ .act υ₁) ⟦B⟧.⁻¹ᴰ ⌝ ⟦B⟧.∘ᴰ τ .nat υ₁₂
  --     -- ≡⟨ ap! (sym coe-K ∙ ⟦B⟧.id⁻¹ᴰ (τ .act υ₁) .[]coe) ⟩ 
  --     -- ⟦B⟧.idᴰ (τ .act υ₁) ⟦B⟧.∘ᴰ τ .nat υ₁₂
  --     -- ≡⟨ ⟦B⟧.id∘ᴰ (τ .nat υ₁₂) .[]coe ⟩ 
  --     -- τ .nat υ₁₂ ∎)
  ⟦Π⟧ .snd .coe-∘  = {!   !}
  ⟦Π⟧ .snd .coh-id = {!   !}
  ⟦Π⟧ .snd .coh-∘  = {!   !}

⟦lam⟧ : ⟦Tm⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧ → ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧)
⟦lam⟧ ⟦t⟧ .act ρ .act υ    = ⟦t⟧ .act (ρ , υ)

⟦lam⟧ ⟦t⟧ .act ρ .pres υ₁₂ = ⟦t⟧ .pres (_ , υ₁₂)
⟦lam⟧ ⟦t⟧ .act ρ .id = {!   !}
⟦lam⟧ ⟦t⟧ .act ρ ._⁻¹ = {!   !}
⟦lam⟧ ⟦t⟧ .act ρ ._∘_ = {!   !}
⟦lam⟧ ⟦t⟧ .act ρ .coeG = {!   !}
⟦lam⟧ {⟦A⟧ = ⟦A⟧} ⟦t⟧ .pres ρ₁₂ .act₁ υ 
  = pres ⟦t⟧ (ρ₁₂ , ⟦A⟧ .snd .cohG ρ₁₂ υ)
⟦lam⟧ ⟦t⟧ .pres ρ₁₂ .pres υ₁₂ = {!   !}
⟦lam⟧ ⟦t⟧ .id  _   = {!!}
⟦lam⟧ ⟦t⟧ ._⁻¹ _   = {!  !}
⟦lam⟧ ⟦t⟧ ._∘_ _ _ = {!   !}

-- Application
module _ (⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧)) where
  private
    module ⟦Γ⟧ = Grpd.Data (⟦Γ⟧ .snd)
    module ⟦A⟧ = Grpdᴰ.Data (⟦A⟧ .snd)
    module ⟦B⟧ = Grpdᴰ.Data (⟦B⟧ .snd)
    module ⟦t⟧ = _⇒ᴰ_ ⟦t⟧
        
  ⟦app⟧ : ⟦Tm⟧ (⟦▷⟧ ⟦Γ⟧ ⟦A⟧) ⟦B⟧
  ⟦app⟧ .act  (ρ , υ)      = ⟦t⟧ .act ρ .act υ
  ⟦app⟧ .pres {x₁ = ρ₁ , υ₁} {x₂ = ρ₂ , υ₂} (ρ₁₂ , υ₁₂)
    rewrite ⟦Γ⟧.∘⁻¹ ρ₁₂  
    rewrite ⟦Γ⟧.⁻¹∘ ρ₁₂  
    rewrite ⟦Γ⟧.∘id ρ₁₂
    rewrite ⟦Γ⟧.id∘ ρ₁₂
    -- Reflexive equations
    rewrite ⟦Γ⟧.∘∘ ρ₁₂ (ρ₁₂ ⟦Γ⟧.⁻¹) ρ₁₂
    = tr (λ □ → ⟦B⟧ .fst .Relᴰ _ _ (ρ₁₂ , □)) 
         (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.∘ᴰ ((⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ υ₁₂)
         ≡⟨ sym (⟦A⟧.∘∘ᴰ (⟦A⟧.cohG ρ₁₂ υ₁) 
                         (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ) υ₁₂ .[]coe) ⟩ 
         (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.∘ᴰ (⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ)) ⟦A⟧.∘ᴰ υ₁₂
         ≡⟨ ⟦A⟧.⟨∘⁻¹⟩∘ᴰ (⟦A⟧.cohG ρ₁₂ υ₁) υ₁₂ .[]coe ⟩ 
         υ₁₂ ∎)
         (⟦t⟧.pres ρ₁₂ .act₁ υ₁ ⟦B⟧.∘ᴰ 
          pres (⟦t⟧.act ρ₂) ((⟦A⟧.cohG ρ₁₂ υ₁ ⟦A⟧.⁻¹ᴰ) ⟦A⟧.∘ᴰ υ₁₂))
  ⟦app⟧ .id  (ρ , τ)  
    rewrite ⟦Γ⟧.id⁻¹ ρ 
    rewrite ⟦Γ⟧.id∘ (⟦Γ⟧.id ρ)
    -- Reflexive rewrites
    rewrite ⟦Γ⟧.∘⁻¹ (⟦Γ⟧.id ρ)
    rewrite ⟦Γ⟧.⁻¹∘ (⟦Γ⟧.id ρ)
    rewrite ⟦Γ⟧.∘id (⟦Γ⟧.id ρ)
    rewrite ⟦Γ⟧.∘∘ (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ) (⟦Γ⟧.id ρ)
    -- Back to non-reflexive rewrites
    rewrite ⟦A⟧.coe-id τ
    rewrite ⟦A⟧.coh-id τ .[]coe
    rewrite ⟦A⟧.id∘ᴰ (⟦A⟧.idᴰ τ) .[]coe
    rewrite ⟦A⟧.id⁻¹ᴰ τ .[]coe
    -- More reflexive rewrites
    rewrite ⟦A⟧.∘∘ᴰ (⟦A⟧.idᴰ τ) (⟦A⟧.idᴰ τ) (⟦A⟧.idᴰ τ) .[]coe
    rewrite ⟦A⟧.∘⁻¹ᴰ (⟦A⟧.idᴰ τ) .[]coe = 
    ⌜ ⟦t⟧.pres (⟦Γ⟧.id ρ) ⌝ .act₁ τ ⟦B⟧.∘ᴰ ⟦t⟧.act ρ .pres (⟦A⟧.idᴰ τ)
    ≡⟨ ap! (⟦t⟧.id ρ) ⟩
    ⌜ ⟦t⟧.act ρ .pres (⟦A⟧.idᴰ τ) ⌝ ⟦B⟧.∘ᴰ ⟦t⟧.act ρ .pres (⟦A⟧.idᴰ τ)
    ≡⟨ ap! (⟦t⟧.act ρ .id τ) ⟩
    ⟦B⟧.idᴰ (⟦t⟧.act ρ .act τ) ⟦B⟧.∘ᴰ ⌜ ⟦t⟧.act ρ .pres (⟦A⟧.idᴰ τ) ⌝
    ≡⟨ ap! (⟦t⟧.act ρ .id τ) ⟩
    ⟦B⟧.idᴰ (⟦t⟧.act ρ .act τ) ⟦B⟧.∘ᴰ ⟦B⟧.idᴰ (⟦t⟧.act ρ .act τ)
    ≡⟨ ⟦B⟧.id∘ᴰ (⟦B⟧.idᴰ (act (⟦t⟧.act ρ) τ)) .[]coe ⟩
    ⟦B⟧.idᴰ (⟦t⟧.act ρ .act τ) ∎
  ⟦app⟧ ._⁻¹ _   = {!  !}
  ⟦app⟧ ._∘_ _ _ = {!   !}

⟦β⟧ : ⟦app⟧ (⟦lam⟧ ⟦t⟧) .act ≡ ⟦t⟧ .act
⟦β⟧ = refl

⟦η⟧ : ∀ {ρ : ⟦Γ⟧ .fst .Car}
        {⟦t⟧ : ⟦Tm⟧ ⟦Γ⟧ (⟦Π⟧ ⟦A⟧ ⟦B⟧)}
    → ⟦lam⟧ (⟦app⟧ ⟦t⟧) .act ρ .act ≡ ⟦t⟧ .act ρ .act
⟦η⟧ = refl
