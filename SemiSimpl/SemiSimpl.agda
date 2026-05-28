{-# OPTIONS --without-K #-}
-- {-# OPTIONS --show-implicit #-}

open import Utils

-- Minimal type theory for describing semi-simplicial types
-- Originally due to András Kovács 
-- (I translated into graph-of-the-function-style)

-- Defining the model is not easy (transport hell), but I still think it might 
-- be do-able. In an effort to avoid dealing with a bunch of path algebra, I am 
-- trying to stick only to pattern-matching on identity proofs (writing
-- helper functions to manually abstract over stuff when necessary).

module SemiSimpl.SemiSimpl where

data Top : Set
data Loc : Top → Set
data Var : ∀ Γ → Loc Γ → Set
data Emb : ∀ {Γ} → Loc Γ → Loc Γ → Set 

variable
  Γ Δ Θ Γ' : Top
  Ξ Ψ Φ Ω Ξ' Ψ' Φ' Ω' : Loc _
  x y z : Var _ _
  δ σ γ θ φ ψ δ' σ' γ' θ' φ' ψ' φ'' : Emb _ _

data _⨾_≔_ : Emb Ψ Ξ → Emb Φ Ψ → Emb Φ Ξ → Set

variable
  δ𝒢 σ𝒢 γ𝒢 φ𝒢 ψ𝒢 φ𝒢' : _ ⨾ _ ≔ _

data Top where
  •   : Top
  _▷_ : (Γ : Top) → Loc Γ → Top

data wkLoc_≔_ {Γ} {Ξ} : Loc Γ → Loc (Γ ▷ Ξ) → Set

data wkEmb_⟨_⟩⟨_⟩≔_ : Emb Ψ Ξ → wkLoc Ψ ≔ Ψ' → wkLoc Ξ ≔ Ξ' 
                    → Emb {Γ = Γ ▷ Φ} Ψ' Ξ' → Set

variable
  Ξ𝒢 Ψ𝒢 Φ𝒢 : wkLoc _ ≔ _

data Loc where
  []     : Loc Γ
  _-,_∣_ : (Ξ : Loc Γ) → Var Γ Ψ → Emb Ξ Ψ → Loc Γ

data Emb where
  ε     : Emb {Γ} [] []
  _⁺_∣_ : Emb Ξ Ψ → (x : Var Γ Φ) (φ : Emb Ξ Φ) 
        → Emb (Ξ -, x ∣ φ) Ψ
  _^_   : (δ : Emb Ξ Ψ) → φ ⨾ δ ≔ γ
        → Emb (Ξ -, x ∣ γ) (Ψ -, x ∣ φ)

data Var where
  vz : wkLoc Ξ ≔ Ξ' → Var (Γ ▷ Ξ) Ξ'
  vs : Var Γ Ξ → wkLoc Ξ ≔ Ξ' → Var (Γ ▷ Ψ) Ξ'

data wkLoc_≔_ where
  wk[] : wkLoc [] ≔ []
  wk-, : (δ𝒢 : wkEmb δ ⟨ Ξ𝒢 ⟩⟨ Ψ𝒢 ⟩≔ δ')
       → wkLoc (Ξ -, x ∣ δ) ≔ (Ξ' -, vs x Ψ𝒢 ∣ δ')

data _⨾_≔_ where
  ⨾ε  : δ ⨾ ε ≔ δ
  ⨾⁺  : δ ⨾ σ ≔ γ → δ ⨾ (σ ⁺ x ∣ φ) ≔ (γ ⁺ x ∣ φ)
  ⁺⨾^ : (σ𝒢 : φ ⨾ σ ≔ φ') → δ ⨾ σ ≔ γ → (δ ⁺ x ∣ φ) ⨾ (σ ^ σ𝒢) ≔ (γ ⁺ x ∣ φ')
  ^⨾^ : (δ𝒢 : φ ⨾ δ ≔ φ') (σ𝒢 : φ' ⨾ σ ≔ φ'') (γ𝒢 : φ ⨾ γ ≔ φ'') → δ ⨾ σ ≔ γ 
      → (_^_ {x = x} δ δ𝒢) ⨾ (σ ^ σ𝒢) ≔ (γ ^ γ𝒢)

data wkEmb_⟨_⟩⟨_⟩≔_ where
  wkε : wkEmb ε ⟨ wk[] {Ξ = Ξ} ⟩⟨ wk[] ⟩≔ ε
  wk⁺ : (δ𝒢 : wkEmb δ ⟨ Ξ𝒢 ⟩⟨ Ψ𝒢 ⟩≔ δ')
        (φ𝒢 : wkEmb φ ⟨ Ξ𝒢 ⟩⟨ Φ𝒢 ⟩≔ φ')
      → wkEmb (δ ⁺ x ∣ φ) ⟨ wk-, φ𝒢 ⟩⟨ Ψ𝒢 ⟩≔ (δ' ⁺ vs x Φ𝒢 ∣ φ')
  wk^ : wkEmb δ ⟨ Ξ𝒢 ⟩⟨ Ψ𝒢 ⟩≔ δ'
      → (φ𝒢 : wkEmb φ ⟨ Ψ𝒢 ⟩⟨ Φ𝒢 ⟩≔ φ')
      → (γ𝒢 : wkEmb γ ⟨ Ξ𝒢 ⟩⟨ Φ𝒢 ⟩≔ γ')
      → (⨾δ𝒢  : φ  ⨾ δ  ≔ γ)
      → (⨾δ𝒢' : φ' ⨾ δ' ≔ γ')
      → wkEmb (_^_ {x = x} δ ⨾δ𝒢) ⟨ wk-, γ𝒢 ⟩⟨ wk-, φ𝒢 ⟩≔ (δ' ^ ⨾δ𝒢')

π₁ : Emb Ψ (Ξ -, x ∣ φ) → Emb Ψ Ξ
π₁ (δ ⁺ y ∣ ψ) = π₁ δ ⁺ y ∣ ψ
π₁ (δ ^ δ𝒢)    = δ ⁺ _ ∣ _

⁺⨾ : (δ ⁺ x ∣ φ) ⨾ σ ≔ γ → δ ⨾ π₁ σ ≔ γ
⁺⨾ (⨾⁺ δ𝒢)     = ⨾⁺ (⁺⨾ δ𝒢)
⁺⨾ (⁺⨾^ σ𝒢 γ𝒢) = ⨾⁺ γ𝒢

-- I am not convinced the below utilities are useful, but they are kinda fun...
_⨾π₁_ : (φ : Emb Ξ Φ) → Emb Ψ (Ξ -, x ∣ φ) → Emb Ψ Φ
φ ⨾π₁ (δ ⁺ y ∣ ψ)        = (φ ⨾π₁ δ) ⁺ _ ∣ _
φ ⨾π₁ (_^_ {γ = γ} δ δ𝒢) = γ ⁺ _ ∣ _

π₁≔ : (δ : Emb Ψ (Ξ -, x ∣ φ)) → φ ⨾ π₁ δ ≔ (φ ⨾π₁ δ)
π₁≔ (δ ⁺ y ∣ ψ) = ⨾⁺ (π₁≔ δ)
π₁≔ (δ ^ δ𝒢)    = ⨾⁺ δ𝒢

⟦Top⟧ : Set₁
⟦Top⟧ = Set

⟦Loc⟧ : ⟦Top⟧ → Set₁
⟦Loc⟧ ⟦Γ⟧ = ⟦Γ⟧ → Set

⟦Var⟧ : (⟦Γ⟧ : ⟦Top⟧) → ⟦Loc⟧ ⟦Γ⟧ → Set₁
⟦Var⟧ ⟦Γ⟧ ⟦Ξ⟧ = (ρ : ⟦Γ⟧) → ⟦Ξ⟧ ρ → Set

variable
  ⟦Γ⟧ ⟦Δ⟧ ⟦Θ⟧ : ⟦Top⟧
  ⟦Ξ⟧ ⟦Ψ⟧ ⟦Φ⟧ ⟦Ξ'⟧ ⟦Ψ'⟧ ⟦Φ'⟧ : ⟦Loc⟧ _
  ⟦x⟧ ⟦y⟧ ⟦z⟧ : ⟦Var⟧ _ _

⟦Emb⟧ : ⟦Loc⟧ ⟦Γ⟧ → ⟦Loc⟧ ⟦Γ⟧ → Set
⟦Emb⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦Ξ⟧ ⟦Ψ⟧ = (ρ : ⟦Γ⟧) → ⟦Ξ⟧ ρ → ⟦Ψ⟧ ρ

variable
  ⟦δ⟧ ⟦σ⟧ ⟦γ⟧ ⟦φ⟧ ⟦ψ⟧ ⟦δ'⟧ ⟦σ'⟧ ⟦γ'⟧ ⟦φ'⟧ ⟦φ''⟧ ⟦ψ'⟧ : ⟦Emb⟧ _ _
  δ≡ σ≡ γ≡ δσ≡ : _≡_ {A = ⟦Emb⟧ _ _} _ _

⟦⨾⟧ : ⟦Emb⟧ ⟦Ψ⟧ ⟦Ξ⟧ → ⟦Emb⟧ ⟦Φ⟧ ⟦Ψ⟧ → ⟦Emb⟧ ⟦Φ⟧ ⟦Ξ⟧
⟦⨾⟧ ⟦δ⟧ ⟦σ⟧ ρ ξ = ⟦δ⟧ ρ (⟦σ⟧ ρ ξ)

⟦•⟧ : ⟦Top⟧
⟦•⟧ = 𝟙

⟦▷⟧ : (⟦Γ⟧ : ⟦Top⟧) → ⟦Loc⟧ ⟦Γ⟧ → ⟦Top⟧
⟦▷⟧ ⟦Γ⟧ ⟦Ξ⟧ = Σ ⟦Γ⟧ ⟦Ξ⟧

⟦[]⟧ : ⟦Loc⟧ ⟦Γ⟧
⟦[]⟧ ρ = 𝟙

⟦-,⟧ : (⟦Ξ⟧ : ⟦Loc⟧ ⟦Γ⟧) → ⟦Var⟧ ⟦Γ⟧ ⟦Ψ⟧ → ⟦Emb⟧ ⟦Ξ⟧ ⟦Ψ⟧ → ⟦Loc⟧ ⟦Γ⟧
⟦-,⟧ ⟦Ξ⟧ ⟦x⟧ ⟦φ⟧ ρ = Σ (⟦Ξ⟧ ρ) λ ξ → ⟦x⟧ ρ (⟦φ⟧ ρ ξ)

⟦ε⟧ : ⟦Emb⟧ {⟦Γ⟧ = ⟦Γ⟧} ⟦[]⟧ ⟦[]⟧
⟦ε⟧ ρ ⟨⟩ = ⟨⟩

⟦⁺⟧ : ⟦Emb⟧ ⟦Ξ⟧ ⟦Ψ⟧ → (⟦x⟧ : ⟦Var⟧ ⟦Γ⟧ ⟦Φ⟧) (⟦φ⟧ : ⟦Emb⟧ ⟦Ξ⟧ ⟦Φ⟧)
    → ⟦Emb⟧ (⟦-,⟧ ⟦Ξ⟧ ⟦x⟧ ⟦φ⟧) ⟦Ψ⟧
⟦⁺⟧ ⟦δ⟧ ⟦x⟧ ⟦φ⟧ ρ (ξ , τ) = ⟦δ⟧ ρ ξ

⟦^⟧ : (⟦δ⟧ : ⟦Emb⟧ ⟦Ξ⟧ ⟦Ψ⟧) → ⟦⨾⟧ ⟦φ⟧ ⟦δ⟧ ≡ ⟦γ⟧
    → ⟦Emb⟧ (⟦-,⟧ ⟦Ξ⟧ ⟦x⟧ ⟦γ⟧) (⟦-,⟧ ⟦Ψ⟧ ⟦x⟧ ⟦φ⟧)
⟦^⟧ ⟦δ⟧ refl ρ (ξ , τ) = ⟦δ⟧ ρ ξ , τ

⟦π₁⟧ : ∀ ⟦x⟧ → ⟦Emb⟧ ⟦Ψ⟧ (⟦-,⟧ ⟦Ξ⟧ ⟦x⟧ ⟦φ⟧) → ⟦Emb⟧ ⟦Ψ⟧ ⟦Ξ⟧
⟦π₁⟧ ⟦x⟧ ⟦δ⟧ ρ ξ = ⟦δ⟧ ρ ξ .fst

⟦⨾ε⟧ : ⟦⨾⟧ ⟦δ⟧ ⟦ε⟧ ≡ ⟦δ⟧
⟦⨾ε⟧ = refl

⟦⨾⁺⟧ : ∀ ⟦δ⟧ ⟦x⟧ → ⟦⨾⟧ ⟦δ⟧ ⟦σ⟧ ≡ ⟦γ⟧
     → ⟦⨾⟧ ⟦δ⟧ (⟦⁺⟧ ⟦σ⟧ ⟦x⟧ ⟦φ⟧) ≡ ⟦⁺⟧ ⟦γ⟧ ⟦x⟧ ⟦φ⟧
⟦⨾⁺⟧ ⟦δ⟧ ⟦x⟧ refl = refl

⟦⁺⨾^⟧ : (φ≡ : ⟦⨾⟧ ⟦φ⟧ ⟦σ⟧ ≡ ⟦φ'⟧)
      → ⟦⨾⟧ ⟦δ⟧ ⟦σ⟧ ≡ ⟦γ⟧ 
      → ⟦⨾⟧ (⟦⁺⟧ ⟦δ⟧ ⟦x⟧ ⟦φ⟧) (⟦^⟧ {⟦x⟧ = ⟦x⟧} ⟦σ⟧ φ≡) ≡ ⟦⁺⟧ ⟦γ⟧ ⟦x⟧ ⟦φ'⟧
⟦⁺⨾^⟧ refl refl = refl
      
⟦^⨾^⟧ : (δ≡ : ⟦⨾⟧ ⟦φ⟧ ⟦δ⟧ ≡ ⟦φ'⟧) (σ≡ : ⟦⨾⟧ ⟦φ'⟧ ⟦σ⟧ ≡ ⟦φ''⟧)
        (γ≡ : ⟦⨾⟧ ⟦φ⟧ ⟦γ⟧ ≡ ⟦φ''⟧)
        (δσ≡ : ⟦⨾⟧ ⟦δ⟧ ⟦σ⟧ ≡ ⟦γ⟧)
      -- Extra coherence
      → ap (⟦⨾⟧ ⟦φ⟧) (sym δσ≡) ∙ ap (λ □ → ⟦⨾⟧ □ ⟦σ⟧) δ≡ ∙ σ≡ ≡ γ≡
      → ⟦⨾⟧ (⟦^⟧ {⟦φ⟧ = ⟦φ⟧} {⟦x⟧ = ⟦x⟧} ⟦δ⟧ δ≡) 
            (⟦^⟧ {⟦x⟧ = ⟦x⟧} ⟦σ⟧ σ≡) 
      ≡ ⟦^⟧ {⟦x⟧ = ⟦x⟧} ⟦γ⟧ γ≡
⟦^⨾^⟧ refl refl refl refl refl = refl

⟦⁺⨾⟧ : ⟦⨾⟧ (⟦⁺⟧ ⟦δ⟧ ⟦x⟧ ⟦φ⟧) ⟦σ⟧ ≡ ⟦γ⟧ 
     → ⟦⨾⟧ ⟦δ⟧ (⟦π₁⟧ ⟦x⟧ ⟦σ⟧) ≡ ⟦γ⟧
⟦⁺⨾⟧ refl = refl

⟦wkLoc⟧ : ⟦Loc⟧ ⟦Γ⟧ → ⟦Loc⟧ (⟦▷⟧ ⟦Γ⟧ ⟦Ψ⟧)
⟦wkLoc⟧ ⟦Ξ⟧ (ρ , τ) = ⟦Ξ⟧ ρ

⟦wkEmb⟧ : ⟦Emb⟧ ⟦Ψ⟧ ⟦Ξ⟧ → ⟦wkLoc⟧ ⟦Ψ⟧ ≡ ⟦Ψ'⟧ → ⟦wkLoc⟧ ⟦Ξ⟧ ≡ ⟦Ξ'⟧
        → ⟦Emb⟧ {⟦Γ⟧ = ⟦▷⟧ ⟦Γ⟧ ⟦Φ⟧} ⟦Ψ'⟧ ⟦Ξ'⟧
⟦wkEmb⟧ ⟦δ⟧ refl refl (ρ , τ) ξ = ⟦δ⟧ ρ ξ

-- I am not sure the zero variable case here is actually what we want. I should
-- spend some time working out how to actually write down semi-simplicial types 
-- with this syntax at some point...
⟦vz⟧ : ⟦wkLoc⟧ ⟦Ξ⟧ ≡ ⟦Ξ'⟧ → ⟦Var⟧ (⟦▷⟧ ⟦Γ⟧ ⟦Ξ⟧) ⟦Ξ'⟧
⟦vz⟧ refl (ρ , ξ) ξ' = ξ ≡ ξ'

⟦vs⟧ : ⟦Var⟧ ⟦Γ⟧ ⟦Ξ⟧ → ⟦wkLoc⟧ ⟦Ξ⟧ ≡ ⟦Ξ'⟧ → ⟦Var⟧ (⟦▷⟧ ⟦Γ⟧ ⟦Ψ⟧) ⟦Ξ'⟧
⟦vs⟧ ⟦x⟧ refl (ρ , τ) ξ = ⟦x⟧ ρ ξ

⟦_⟧Top : Top → ⟦Top⟧
⟦_⟧Loc : Loc Γ → ⟦Loc⟧ ⟦ Γ ⟧Top
⟦_⟧Var : Var Γ Ξ → ⟦Var⟧ ⟦ Γ ⟧Top ⟦ Ξ ⟧Loc
⟦_⟧Emb : Emb Ξ Ψ → ⟦Emb⟧ ⟦ Ξ ⟧Loc ⟦ Ψ ⟧Loc

⟦_⟧⨾ : δ ⨾ σ ≔ γ → ⟦⨾⟧ ⟦ δ ⟧Emb ⟦ σ ⟧Emb ≡ ⟦ γ ⟧Emb

-- Coherence required for ⟦^⨾^⟧
coh₁ : (δ𝒢  : φ ⨾ δ ≔ φ')
       (σ𝒢  : φ' ⨾ σ ≔ φ'')
       (γ𝒢  : φ ⨾ γ ≔ φ'')
       (δσ𝒢 : δ ⨾ σ ≔ γ)
      → ap (⟦⨾⟧ ⟦ φ ⟧Emb) (sym ⟦ δσ𝒢 ⟧⨾) 
      ∙ ap (λ □ → ⟦⨾⟧ □ ⟦ σ ⟧Emb) ⟦ δ𝒢 ⟧⨾ 
      ∙ ⟦ σ𝒢 ⟧⨾
      ≡ ⟦ γ𝒢 ⟧⨾

⟦ •     ⟧Top = ⟦•⟧
⟦ Γ ▷ Ξ ⟧Top = ⟦▷⟧ ⟦ Γ ⟧Top ⟦ Ξ ⟧Loc

⟦ []         ⟧Loc = ⟦[]⟧
⟦ Ξ -, x ∣ φ ⟧Loc = ⟦-,⟧ ⟦ Ξ ⟧Loc ⟦ x ⟧Var ⟦ φ ⟧Emb

⟦ ε                ⟧Emb = ⟦ε⟧
⟦ δ ⁺ x ∣ φ        ⟧Emb = ⟦⁺⟧ ⟦ δ ⟧Emb ⟦ x ⟧Var ⟦ φ ⟧Emb 
⟦ _^_ {x = x} δ φ𝒢 ⟧Emb = ⟦^⟧ {⟦x⟧ = ⟦ x ⟧Var} ⟦ δ ⟧Emb ⟦ φ𝒢 ⟧⨾

⟦ ⨾ε                        ⟧⨾ = ⟦⨾ε⟧
⟦ ⨾⁺ {δ = δ} {x = x} δ𝒢     ⟧⨾ = ⟦⨾⁺⟧ ⟦ δ ⟧Emb ⟦ x ⟧Var ⟦ δ𝒢 ⟧⨾
⟦ ⁺⨾^ {φ = φ} {δ = δ} σ𝒢 γ𝒢 ⟧⨾ 
  = ⟦⁺⨾^⟧ {⟦φ⟧ = ⟦ φ ⟧Emb} {⟦δ⟧ = ⟦ δ ⟧Emb} ⟦ σ𝒢 ⟧⨾ ⟦ γ𝒢 ⟧⨾
⟦ ^⨾^ δ𝒢 σ𝒢 γ𝒢 δσ𝒢          ⟧⨾ 
  = ⟦^⨾^⟧ ⟦ δ𝒢 ⟧⨾ ⟦ σ𝒢 ⟧⨾ ⟦ γ𝒢 ⟧⨾ ⟦ δσ𝒢 ⟧⨾ (coh₁ δ𝒢 σ𝒢 γ𝒢 δσ𝒢)

⟦_⟧wkLoc : wkLoc Ξ ≔ Ξ' → ⟦wkLoc⟧ ⟦ Ξ ⟧Loc ≡ ⟦ Ξ' ⟧Loc

⟦_⟧wkEmb : wkEmb δ ⟨ Ψ𝒢 ⟩⟨ Ξ𝒢 ⟩≔ δ' 
         → ⟦wkEmb⟧ ⟦ δ ⟧Emb ⟦ Ψ𝒢 ⟧wkLoc ⟦ Ξ𝒢 ⟧wkLoc ≡ ⟦ δ' ⟧Emb

⟦ vz Ξ𝒢   ⟧Var = ⟦vz⟧ ⟦ Ξ𝒢 ⟧wkLoc
⟦ vs x Ξ𝒢 ⟧Var = ⟦vs⟧ ⟦ x ⟧Var ⟦ Ξ𝒢 ⟧wkLoc

⟦π₁⟧≡ : {x : Var Γ Φ} {δ : Emb Ψ (Ξ -, x ∣ φ)} 
      → ⟦ π₁ δ ⟧Emb ≡ ⟦π₁⟧ ⟦ x ⟧Var ⟦ δ ⟧Emb

⟦⁺⨾⟧≡ : ∀ {x : Var Γ Ξ'} {δ : Emb Ψ Ξ} 
          {σ : Emb Φ (Ψ -, x ∣ φ)} {γ} 
      → (δ𝒢 : (δ ⁺ x ∣ φ) ⨾ σ ≔ γ) 
      → ⟦ ⁺⨾ δ𝒢 ⟧⨾ 
      ≡ ap (⟦⨾⟧ ⟦ δ ⟧Emb) (⟦π₁⟧≡ {δ = σ}) 
      ∙ ⟦⁺⨾⟧ {⟦δ⟧ = ⟦ δ ⟧Emb} {⟦x⟧ = ⟦ x ⟧Var} {⟦σ⟧ = ⟦ σ ⟧Emb} ⟦ δ𝒢 ⟧⨾

⟦π₁^⟧ : (δ≡ : ⟦⨾⟧ ⟦φ⟧ ⟦δ⟧ ≡ ⟦φ'⟧) 
      → ⟦⁺⟧ ⟦δ⟧ ⟦x⟧ ⟦φ'⟧ 
      ≡ ⟦π₁⟧ {⟦φ⟧ = ⟦φ⟧} ⟦x⟧ (⟦^⟧ {⟦x⟧ = ⟦x⟧} ⟦δ⟧ δ≡)
⟦π₁^⟧ refl = refl

⟦π₁⁺⟧ : ⟦δ'⟧ ≡ ⟦π₁⟧ {⟦φ⟧ = ⟦φ⟧} ⟦x⟧ ⟦δ⟧
      → ⟦⁺⟧ ⟦δ'⟧ ⟦y⟧ ⟦ψ⟧ 
      ≡ ⟦π₁⟧ ⟦x⟧ (⟦⁺⟧ ⟦δ⟧ ⟦y⟧ ⟦ψ⟧)
⟦π₁⁺⟧ refl = refl

⟦π₁⟧≡ {x = x} {δ = δ ⁺ y ∣ ψ} 
  = ⟦π₁⁺⟧ {⟦x⟧ = ⟦ x ⟧Var} {⟦δ⟧ = ⟦ δ ⟧Emb} {⟦y⟧ = ⟦ y ⟧Var} {⟦ψ⟧ = ⟦ ψ ⟧Emb} 
          (⟦π₁⟧≡ {δ = δ})
⟦π₁⟧≡ {δ = _^_ {φ = φ} {x = x} δ δ𝒢} 
  = ⟦π₁^⟧ {⟦φ⟧ = ⟦ φ ⟧Emb} {⟦x⟧ = ⟦ x ⟧Var} ⟦ δ𝒢 ⟧⨾

⟦⁺⨾⟧≡ (⨾⁺ δ𝒢)     = {!   !}
⟦⁺⨾⟧≡ (⁺⨾^ σ𝒢 γ𝒢) = {!   !}
 
coh₁₁ : {⟦φ⟧ : ⟦Emb⟧ ⟦[]⟧ ⟦Ξ⟧}
        (σ≡ : ⟦⨾⟧ ⟦φ⟧ ⟦σ⟧ ≡ ⟦γ⟧)
        (σ≡' : ⟦⨾⟧ ⟦φ⟧ ⟦σ'⟧ ≡ ⟦γ⟧)
        (σσ≡ : ⟦⨾⟧ ⟦ε⟧ ⟦σ⟧ ≡ ⟦σ'⟧)
      → ap (⟦⨾⟧ ⟦φ⟧) (sym σσ≡) ∙ σ≡ ≡ σ≡'
      → ap (⟦⨾⟧ ⟦φ⟧) (sym (⟦⨾⁺⟧ ⟦ε⟧ ⟦x⟧ σσ≡))
      ∙ ⟦⨾⁺⟧ ⟦φ⟧ ⟦x⟧ σ≡
      ≡ ⟦⨾⁺⟧ {⟦φ⟧ = ⟦ψ⟧} ⟦φ⟧ ⟦x⟧ σ≡'
coh₁₁ refl refl refl refl = refl

coh₁₂ 
  : {⟦x⟧ : ⟦Var⟧ ⟦Γ⟧ ⟦Φ'⟧}
    {⟦y⟧ : ⟦Var⟧ ⟦Γ⟧ ⟦Ψ'⟧}
    {⟦δ⟧ : ⟦Emb⟧ ⟦Ψ⟧ ⟦Ξ⟧} 
    {⟦σ⟧ : ⟦Emb⟧ ⟦Φ⟧ (⟦-,⟧ ⟦Ψ⟧ ⟦y⟧ ⟦ψ⟧)}
    (δ≡ : ⟦⨾⟧ ⟦φ⟧ ⟦δ⟧ ≡ ⟦φ'⟧)
    (σ≡ : ⟦⨾⟧ (⟦⁺⟧ ⟦φ'⟧ ⟦y⟧ ⟦ψ⟧) ⟦σ⟧ ≡ ⟦φ''⟧)
    (σ≡' : ⟦⨾⟧ ⟦φ'⟧ ⟦σ'⟧ ≡ ⟦φ''⟧)
    (γ≡ : ⟦⨾⟧ ⟦φ⟧ ⟦γ⟧ ≡ ⟦φ''⟧)
    (δσ≡ : ⟦⨾⟧ (⟦⁺⟧ ⟦δ⟧ ⟦y⟧ ⟦ψ⟧) ⟦σ⟧ ≡ ⟦γ⟧)
    (δσ≡' : ⟦⨾⟧ ⟦δ⟧ ⟦σ'⟧ ≡ ⟦γ⟧)
  → (πσ : ⟦σ'⟧ ≡ ⟦π₁⟧ ⟦y⟧ ⟦σ⟧) 
  → σ≡' ≡ ap (⟦⨾⟧ ⟦φ'⟧) πσ ∙ ⟦⁺⨾⟧ {⟦δ⟧ = ⟦φ'⟧} {⟦x⟧ = ⟦y⟧} {⟦σ⟧ = ⟦σ⟧} σ≡
  → δσ≡' ≡ ap (⟦⨾⟧ ⟦δ⟧) πσ ∙ ⟦⁺⨾⟧ {⟦δ⟧ = ⟦δ⟧} {⟦x⟧ = ⟦y⟧} {⟦σ⟧ = ⟦σ⟧} δσ≡
  → ap (⟦⨾⟧ ⟦φ⟧) (sym δσ≡') ∙ ap (λ □ → ⟦⨾⟧ □ ⟦σ'⟧) δ≡ ∙ σ≡'
  ≡ γ≡
  → ap (⟦⨾⟧ ⟦φ⟧) 
       (sym (⟦⨾⁺⟧ {⟦σ⟧ = ⟦σ⟧} (⟦⁺⟧ ⟦δ⟧ ⟦y⟧ ⟦ψ⟧) ⟦x⟧ δσ≡)) 
  ∙ ap (λ □ → ⟦⨾⟧ □ (⟦⁺⟧ ⟦σ⟧ ⟦x⟧ ⟦ψ'⟧)) (⟦⨾⁺⟧ ⟦φ⟧ ⟦y⟧ δ≡) 
  ∙ ⟦⨾⁺⟧ {⟦σ⟧ = ⟦σ⟧} (⟦⁺⟧ ⟦φ'⟧ ⟦y⟧ ⟦ψ⟧) ⟦x⟧ σ≡
  ≡ ⟦⨾⁺⟧ ⟦φ⟧ ⟦x⟧ γ≡
coh₁₂ refl refl refl refl refl refl refl refl refl refl = refl

-- The syntax is an hSet so we should be able to get that 'γ𝒢' is '⨾ε' here
coh₁ ⨾ε ⨾ε γ𝒢 ⨾ε = {!   !}

coh₁ {φ = φ} ⨾ε (⨾⁺ σ𝒢) (⨾⁺ γ𝒢) (⨾⁺ δσ𝒢) 
  using hyp ← coh₁ ⨾ε σ𝒢 γ𝒢 δσ𝒢
  = coh₁₁ {⟦φ⟧ = ⟦ φ ⟧Emb} ⟦ σ𝒢 ⟧⨾ ⟦ γ𝒢 ⟧⨾ ⟦ δσ𝒢 ⟧⨾ hyp

coh₁ {φ = φ} (⨾⁺ {σ = δ} {γ = φ'} {x = y} {φ = ψ} δ𝒢) 
             (⨾⁺ {σ = σ} {x = x} {φ = ψ'} σ𝒢) 
             (⨾⁺ {σ = γ} {γ = φ''} γ𝒢) 
             (⨾⁺ δσ𝒢) 
  using hyp ← coh₁ δ𝒢 (⁺⨾ σ𝒢) γ𝒢 (⁺⨾ δσ𝒢) 
  = coh₁₂ ⟦ δ𝒢 ⟧⨾ ⟦ σ𝒢 ⟧⨾ ⟦ ⁺⨾ σ𝒢 ⟧⨾ ⟦ γ𝒢 ⟧⨾ ⟦ δσ𝒢 ⟧⨾ ⟦ ⁺⨾ δσ𝒢 ⟧⨾ 
          -- Uncommenting these arguments hits a termination error...
          {!⟦π₁⟧≡ {δ = σ}!} {!⟦⁺⨾⟧≡ σ𝒢!} {!⟦⁺⨾⟧≡ δσ𝒢!} 
          hyp

coh₁ (⨾⁺ δ𝒢) (⁺⨾^ σ𝒢₀ σ𝒢₁) (⨾⁺ γ𝒢) (⁺⨾^ δσ𝒢₀ δσ𝒢₁)
  using hyp ← coh₁ δ𝒢 σ𝒢₁ γ𝒢 δσ𝒢₁
  = {!!}

coh₁ (⁺⨾^ δ𝒢₀ δ𝒢₁) (⨾⁺ σ𝒢) (⨾⁺ γ𝒢) (⨾⁺ δσ𝒢)
  using hyp ← coh₁ (⁺⨾^ δ𝒢₀ δ𝒢₁) σ𝒢 γ𝒢 δσ𝒢
  = {!!}

coh₁ (⁺⨾^ δ𝒢₀ δ𝒢₁) (⁺⨾^ σ𝒢₀ σ𝒢₁) (⁺⨾^ γ𝒢₀ γ𝒢₁) (^⨾^ δσ𝒢₀ δσ𝒢₁ δσ𝒢₂ δσ𝒢₃) 
  using hyp ← coh₁ δ𝒢₁ σ𝒢₁ γ𝒢₁ δσ𝒢₃
  = {!   !}

coh₁ (^⨾^ δ𝒢₀ δ𝒢₁ δ𝒢₂ δ𝒢₃) (⨾⁺ σ𝒢) (⨾⁺ γ𝒢) (⨾⁺ δσ𝒢) 
  using hyp ← coh₁ (^⨾^ δ𝒢₀ δ𝒢₁ δ𝒢₂ δ𝒢₃) σ𝒢 γ𝒢 δσ𝒢
  = {!!}

coh₁ (^⨾^ δ𝒢₀ δ𝒢₁ δ𝒢₂ δ𝒢₃) (^⨾^ σ𝒢₀ σ𝒢₁ σ𝒢₂ σ𝒢₃) γ𝒢 (^⨾^ δσ𝒢₀ δσ𝒢₁ δσ𝒢₂ δσ𝒢₃) 
  = {!  γ𝒢 !} -- Stuck pattern matching... probably need to ford

⟦ wk[]    ⟧wkLoc = refl
⟦ wk-, δ𝒢 ⟧wkLoc = {!   !}

⟦ wkε                      ⟧wkEmb = refl
⟦ wk⁺ δ𝒢₀ δ𝒢₁              ⟧wkEmb = {!   !}
⟦ wk^ δ𝒢₀ δ𝒢₁ δ𝒢₂ ⨾δ𝒢 ⨾δ𝒢' ⟧wkEmb = {!   !}
