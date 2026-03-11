{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality.Rewrite

open import Utils renaming (_,_ to _Σ,_)
open import Utils.WithK
open import Utils.Rw

open import NonLinNbE.SyntaxEta

module NonLinNbE.NbE where

_⁺_ : Tms Δ Γ → ∀ A → Tms (Δ ▷ A) Γ
δ ⁺ A = δ ⨾ p

data Thin : ∀ Δ Γ → Tms Δ Γ → Set where
  εTh   : Thin • • ε
  _⁺Th_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ A) Γ (δ ⁺ A)
  _^Th_ : Thin Δ Γ δ → ∀ A → Thin (Δ ▷ (A [ δ ]T)) (Γ ▷ A) (δ ^ A)

variable
  δTh σTh γTh : Thin _ _ _

idTh : Thin Γ Γ id
idTh {Γ = •}     = εTh
idTh {Γ = Γ ▷ A} = idTh ^Th A

_⨾Th_ : Thin Δ Γ δ → Thin Θ Δ σ → Thin Θ Γ (δ ⨾ σ)
εTh         ⨾Th σTh                   = σTh
(δTh ^Th A) ⨾Th (σTh ^Th .(A [ _ ]T)) = (δTh ⨾Th σTh) ^Th A
(δTh ⁺Th A) ⨾Th (σTh ^Th A)           = (δTh ⨾Th σTh) ⁺Th (A [ _ ]T)
δTh         ⨾Th (σTh ⁺Th A)           = (δTh ⨾Th σTh) ⁺Th A

⨾⁺Th : {δTh : Thin Δ Γ δ} {σTh : Thin Θ Δ σ} {A : Ty Θ} 
     → δTh ⨾Th (σTh ⁺Th A) ≡ (δTh ⨾Th σTh) ⁺Th A
⨾⁺Th {δTh = εTh}       = refl
⨾⁺Th {δTh = δTh ⁺Th A} = refl
⨾⁺Th {δTh = δTh ^Th A} = refl

⨾⁺Th' : {δTh : Thin Δ Γ δ} {σTh : Thin Θ Δ σ} {A : Ty Θ} 
      → _⨾Th_ {σ = ⟨ _ ⟩} δTh (σTh ⁺Th A) ≡ (δTh ⨾Th σTh) ⁺Th A
⨾⁺Th' = ⨾⁺Th
{-# REWRITE ⨾⁺Th' #-}

id⨾Th : idTh {Γ = Γ} ⨾Th σTh ≡ σTh
id⨾Th {Γ = •}                       = refl
id⨾Th {Γ = Γ ▷ A} {σTh = σTh ⁺Th B} = ap (_⁺Th B) id⨾Th
id⨾Th {Γ = Γ ▷ A} {σTh = σTh ^Th A} = ap (_^Th A) id⨾Th

⨾idTh : δTh ⨾Th idTh {Γ = Γ} ≡ δTh
⨾idTh {δTh = εTh}       = refl
⨾idTh {δTh = δTh ⁺Th A} = ap (_⁺Th A) ⨾idTh
⨾idTh {δTh = δTh ^Th A} = ap (_^Th A) ⨾idTh

⨾⨾Th : {δTh : Thin Δ Γ δ} {σTh : Thin Θ Δ σ} {γTh : Thin Λ Θ γ}
     → (δTh ⨾Th σTh) ⨾Th γTh ≡ δTh ⨾Th (σTh ⨾Th γTh)
⨾⨾Th {δTh = εTh}       = refl
⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh ⁺Th A} 
  = ap (_⁺Th A) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh})
⨾⨾Th {δTh = δTh} {σTh = σTh ⁺Th A} {γTh = γTh ^Th A} 
  = ap (_⁺Th (A [ _ ]T)) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh}) 
⨾⨾Th {δTh = δTh ⁺Th A} {σTh = σTh ^Th A} {γTh = γTh ^Th .(A [ _ ]T)} 
  = ap (_⁺Th (A [ _ ]T)) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh}) 
⨾⨾Th {δTh = δTh ^Th A} {σTh = σTh ^Th _} {γTh = γTh ^Th _}    
  = ap (_^Th A) (⨾⨾Th {δTh = δTh} {σTh = σTh} {γTh = γTh})

{-# REWRITE id⨾Th ⨾idTh ⨾⨾Th #-}

-- Environments are presheaves on thinnings
record Env (Γ : Ctx) : Set₁ where
  constructor mk
  eta-equality
  field
    El    : ∀ Δ → Tms Δ Γ → Set
    _[_]E : El Δ δ → Thin Θ Δ σ → El Θ (δ ⨾ σ)
    [id]E : ∀ {ρ : El Δ δ} → ρ [ idTh ]E ≡ ρ
    [][]E : ∀ {ρ : El Δ δ} → ρ [ σTh ]E [ γTh ]E ≡ ρ [ σTh ⨾Th γTh ]E

-- Values are displayed presheaves
module _ (Γᴹ : Env Γ) (A : Ty Γ) where
  open Env Γᴹ hiding (El)
  variable
    ρ ρ' ρ'' ρ''' : Γᴹ .Env.El _ _

  record Val : Set₁ where
    constructor mk
    eta-equality
    field
      El    : ∀ {Δ δ} → Γᴹ .Env.El Δ δ → Tm Δ (A [ δ ]T) → Set
      _[_]V : El ρ t → (σTh : Thin Θ Δ σ) → El (ρ [ σTh ]E) (t [ σ ])
      
      [id]V : ∀ {τ : El ρ t} 
            → τ [ idTh ]V ≡[ ap (λ □ → El □ t) [id]E ]≡ τ
      [][]V : ∀ {τ : El ρ t} {σTh : Thin Θ Δ σ} {γTh : Thin Λ Θ γ}
            →  τ [ σTh ]V [ γTh ]V
            ≡[ ap (λ □ → El □ (t [ σ ⨾ γ ])) [][]E 
            ]≡ τ [ σTh ⨾Th γTh ]V
    
    _[_]_V : El ρ t → (σTh : Thin Θ Δ σ) → ρ [ σTh ]E ≡ ρ'
           → El ρ' (t [ σ ])
    τ [ σTh ] ρ≡ V = transp (λ □ → El □ _) ρ≡ (τ [ σTh ]V)

    [id]V' : ∀ {τ : El ρ t} {ρ≡ : ρ [ idTh ]E ≡ ρ'} {El≡} 
            → τ [ idTh ] ρ≡ V ≡[ El≡ ]≡ τ
    [id]V' {ρ≡ = refl} = reix[] [id]V

    [][]V' : ∀ {τ : El ρ t} 
               {ρ≡ : ρ [ σTh ]E ≡ ρ'} {ρ≡' : ρ' [ γTh ]E ≡ ρ''} 
               {ρ≡'' : ρ [ σTh ⨾Th γTh ]E ≡ ρ'''}
               {El≡} 
            →  τ [ σTh ] ρ≡ V [ γTh ] ρ≡' V
            ≡[ El≡
            ]≡ τ [ σTh ⨾Th γTh ] ρ≡'' V
    [][]V' {ρ≡ = refl} {ρ≡' = refl} {ρ≡'' = refl} {El≡ = El≡}
      = reix[] [][]V

module _ (Δᴹ : Env Δ) (Γᴹ : Env Γ) (δ : Tms Δ Γ) where
  private
    module Δ = Env Δᴹ
    module Γ = Env Γᴹ

  record eval* : Set where
    eta-equality
    constructor mk
    field
      act : ∀ {Θ σ} (ρ : Δ.El Θ σ) → Γ.El Θ (δ ⨾ σ)
      nat : {ρ : Δ.El Θ σ} → act ρ Γ.[ γTh ]E ≡ act (ρ Δ.[ γTh ]E)

module _ (Γᴹ : Env Γ) (Aᴹ : Val Γᴹ A) (t : Tm Γ A) where
  private
    module Γ = Env Γᴹ
    module A = Val Aᴹ

  record eval : Set where
    eta-equality
    constructor mk
    field
      act : ∀ {Δ δ} (ρ : Γ.El Δ δ) → A.El ρ (t [ δ ])
      nat : {ρ : Γ.El Δ δ} → act ρ A.[ σTh ]V ≡ act (ρ Γ.[ σTh ]E)

open Env 
open Val
open eval*
open eval

env≡' : {Γ₁ᴹ Γ₂ᴹ : Env Γ}
      → (El≡ : Γ₁ᴹ .El ≡ Γ₂ᴹ .El)
      →  (λ {Δ} {δ} {Θ} {σ} → Γ₁ᴹ ._[_]E {Δ} {δ} {Θ} {σ}) 
      ≡[ (piexti λ {_} → piexti λ {_} → piexti λ {_} → piexti λ {_} 
         → piext[] (happly₂ El≡) λ {ρ₁} {ρ₂} ρ≡ 
         → piext λ σTh → happly₂ El≡) 
      ]≡ Γ₂ᴹ ._[_]E
      → Γ₁ᴹ ≡ Γ₂ᴹ
env≡' refl refl[] 
  = ap₂ (mk _ _) 
    (funexti λ {_} → funexti λ {_} → funexti λ {_} → uip) 
    ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
    → funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
    → funexti λ {_} → uip) 

-- Proper version of 'env≡' (awful)
env≡'' : {Γ₁ᴹ Γ₂ᴹ : Env Γ}
     → (El≡ : ∀ Δ (δ : Tms Δ Γ) → Γ₁ᴹ .El Δ δ ≡ Γ₂ᴹ .El Δ δ)
     → (∀ {Δ δ Θ σ} {ρ₁ : Γ₁ᴹ .El Δ δ} {ρ₂ : Γ₂ᴹ .El Δ δ} 
          (ρ≡ : ρ₁ ≡[ El≡ Δ δ ]≡ ρ₂) (σTh : Thin Θ Δ σ) 
        → (Γ₁ᴹ ._[_]E ρ₁ σTh) ≡[ El≡ Θ (δ ⨾ σ) ]≡ (Γ₂ᴹ ._[_]E ρ₂ σTh))
     → Γ₁ᴹ ≡ Γ₂ᴹ
env≡'' El≡ []E≡ 
  = env≡' (funext λ Δ → funext λ δ → El≡ Δ δ) 
          {!!}
          -- ( funexti λ {_} → funexti λ {_} → funexti λ {_} → funexti λ {_} 
          -- → funext λ ρ → funext λ σTh → {!!})

env≡ : {Γ₁ᴹ Γ₂ᴹ : Env Γ}
     → Γ₁ᴹ .El ≡ Γ₂ᴹ .El
     → Γ₁ᴹ ≡ Γ₂ᴹ
env≡ El≡ = {!!}
-- env≡ refl = {!!}


val≡' : {Γᴹ : Env Γ} {A₁ᴹ A₂ᴹ : Val Γᴹ A}
      → _≡_ {A = ∀ {Δ δ} → Γᴹ .El Δ δ → Tm Δ (A [ δ ]T) → Set} 
            (A₁ᴹ .El) (A₂ᴹ .El) 
      → A₁ᴹ ≡ A₂ᴹ
-- val≡' refl = {!!}

val≡ : {Γᴹ : Env Γ} {A₁ᴹ A₂ᴹ : Val Γᴹ A}
     → (∀ {Δ δ} (ρ : Γᴹ .El Δ δ) (t : Tm Δ (A [ δ ]T)) 
        → A₁ᴹ .El ρ t ≡ A₂ᴹ .El ρ t)
     → A₁ᴹ ≡ A₂ᴹ
-- val≡ p = {!!}

eval*≡' : {Δᴹ : Env Δ} {Γᴹ : Env Γ} {δ₁ᴹ δ₂ᴹ : eval* Δᴹ Γᴹ δ}
        → _≡_ {A = ∀ {Θ σ} (ρ : Δᴹ .El Θ σ) → Γᴹ .El Θ (δ ⨾ σ)} 
              (δ₁ᴹ .act) (δ₂ᴹ .act) → δ₁ᴹ ≡ δ₂ᴹ
eval*≡' refl 
  = ap (mk _) (funexti (funexti (funexti (funexti (funexti (funexti uip))))))

eval*≡ : {Δᴹ : Env Δ} {Γᴹ : Env Γ} {δ₁ᴹ δ₂ᴹ : eval* Δᴹ Γᴹ δ}
       → (∀ {Θ σ} (ρ : Δᴹ .El Θ σ) → δ₁ᴹ .act ρ ≡ δ₂ᴹ .act ρ) 
       → δ₁ᴹ ≡ δ₂ᴹ
eval*≡ p = eval*≡' (funexti (funexti (funext p)))

eval≡ : {Γᴹ : Env Γ} {Aᴹ : Val Γᴹ A} {t₁ᴹ t₂ᴹ : eval Γᴹ Aᴹ t}
      → _≡_ {A = ∀ {Δ δ} (ρ : Γᴹ .El Δ δ) → Aᴹ .El ρ (t [ δ ])}
            (t₁ᴹ .act) (t₂ᴹ .act) → t₁ᴹ ≡ t₂ᴹ
eval≡ refl
  = ap (mk _) (funexti (funexti (funexti (funexti (funexti (funexti uip))))))

eval≡[] : {Γᴹ : Env Γ} {A₁ᴹ A₂ᴹ : Val Γᴹ A} {A≡ᴹ : A₁ᴹ ≡ A₂ᴹ}
          {t₁ᴹ : eval Γᴹ A₁ᴹ t} {t₂ᴹ : eval Γᴹ A₂ᴹ t} 
        →  (λ {_} {_} → t₁ᴹ .act) 
        ≡[ ap (λ □ → ∀ {Δ δ} (ρ : Γᴹ .El Δ δ) → □ .El ρ (t [ δ ])) A≡ᴹ 
        ]≡ (λ {_} {_} → t₂ᴹ .act)
        → t₁ᴹ ≡[ ap (λ □ → eval Γᴹ □ t) A≡ᴹ ]≡ t₂ᴹ
eval≡[] {A≡ᴹ = refl} p .[]coe = eval≡ (p .[]coe)

eval𝕄 : Motives _ _ _ _
eval𝕞 : Methods eval𝕄

eval𝕄 .Ctxᴹ Γ       = Env Γ
eval𝕄 .Tyᴹ  Γᴹ A    = Val Γᴹ A
eval𝕄 .Tmᴹ  Γᴹ Aᴹ t = eval Γᴹ Aᴹ t
eval𝕄 .Tmsᴹ Δᴹ Γᴹ δ = eval* Δᴹ Γᴹ δ

postulate
  cheat : ∀ {A : Set ℓ} → A

{-# NON_COVERING #-}
eval𝕞 .idᴹ        .act ρ = ρ
eval𝕞 .idᴹ        .nat   = refl
eval𝕞 ._⨾ᴹ_ δᴹ σᴹ .act ρ = δᴹ .act (σᴹ .act ρ)
eval𝕞 ._⨾ᴹ_ δᴹ σᴹ .nat   = δᴹ .nat ∙ ap (δᴹ .act) (σᴹ .nat)

eval𝕞 .id⨾ᴹ = eval*≡' refl
eval𝕞 .⨾idᴹ = eval*≡' refl
eval𝕞 .⨾⨾ᴹ  = eval*≡' refl

eval𝕞 ._[_]Tᴹ Aᴹ δᴹ .El ρ t 
  = Aᴹ .El (δᴹ .act ρ) t
eval𝕞 ._[_]Tᴹ Aᴹ δᴹ ._[_]V τ σTh 
  = τ A.[ σTh ] (δᴹ .nat) V
  where module A = Val Aᴹ
eval𝕞 ._[_]Tᴹ Aᴹ δᴹ .[id]V = [id]V' Aᴹ
eval𝕞 ._[_]Tᴹ Aᴹ δᴹ .[][]V = [][]V' Aᴹ
eval𝕞 ._[_]ᴹ  tᴹ δᴹ .act ρ = tᴹ .act (δᴹ .act ρ)
eval𝕞 ._[_]ᴹ {Γᴹ = Γᴹ} {Aᴹ = Aᴹ} {Δᴹ = Δᴹ} tᴹ δᴹ .nat {σTh = σTh} {ρ = ρ} = 
  coe _ (tᴹ .act (δᴹ .act ρ) A.[ σTh ]V)
  ≡⟨ ap (coe _) (tᴹ .nat) ⟩
  coe _ (tᴹ .act (δᴹ .act ρ Γ.[ σTh ]E))
  ≡⟨ apd (tᴹ .act) (nat δᴹ) .[]coe ⟩
  tᴹ .act (δᴹ .act (ρ Δ.[ σTh ]E)) ∎
  where module Γ = Env Γᴹ
        module Δ = Env Δᴹ
        module A = Val Aᴹ
eval𝕞 .[id]Tᴹ = val≡' refl
eval𝕞 .[id]ᴹ  = eval≡[] refl[]-K
eval𝕞 .[][]Tᴹ = val≡' refl
eval𝕞 .[][]ᴹ  = eval≡[] refl[]-K

eval𝕞 .•ᴹ .El    Δ δ   = 𝟙
eval𝕞 .•ᴹ ._[_]E ρ δTh = ⟨⟩
eval𝕞 .•ᴹ .[id]E       = refl
eval𝕞 .•ᴹ .[][]E       = refl

eval𝕞 .εᴹ .act ρ = ⟨⟩
eval𝕞 .εᴹ .nat   = refl
eval𝕞 .•ηᴹ       = eval*≡' refl

eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ .El Δ δ = Σ (Γᴹ .El Δ (π₁ δ)) λ ρ → Aᴹ .El ρ (π₂ δ)
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ ._[_]E (ρ Σ, τ) δTh .fst = ρ Γ.[ δTh ]E
  where module Γ = Env Γᴹ
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ ._[_]E (ρ Σ, τ) δTh .snd = τ A.[ δTh ]V
  where module A = Val Aᴹ
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ .[id]E = apd₂ _Σ,_ (Γᴹ .[id]E) (Aᴹ .[id]V)
eval𝕞 ._▷ᴹ_ Γᴹ Aᴹ .[][]E = apd₂ _Σ,_ (Γᴹ .[][]E) (Aᴹ .[][]V)

eval𝕞 ._,ᴹ_ δᴹ tᴹ .act ρ .fst = δᴹ .act ρ
eval𝕞 ._,ᴹ_ δᴹ tᴹ .act ρ .snd = tᴹ .act ρ
eval𝕞 ._,ᴹ_ δᴹ tᴹ .nat        = apd₂ _Σ,_ (δᴹ .nat) (coe[] (tᴹ .nat))

eval𝕞 .pᴹ .act (ρ Σ, τ) = ρ
eval𝕞 .pᴹ .nat          = refl
eval𝕞 .qᴹ .act (ρ Σ, τ) = τ
eval𝕞 .qᴹ .nat          = refl

eval𝕞 .,⨾ᴹ {δᴹ = δᴹ} {tᴹ = tᴹ} {σᴹ = σᴹ} = eval*≡ λ ρ → ap (_ Σ,_) (
  tᴹ .act (act σᴹ ρ)
  -- TODO: Can we combine apdd₂ and coe-K into a sensible utility?
  ≡⟨ sym coe-K ⟩
  coe _ (tᴹ .act (act σᴹ ρ))
  ≡⟨ apdd₂ (λ □ → eval _ □ _) (λ _ □ → □ .act ρ) (val≡' refl) .[]coe ⟩ 
  _ ∎)
eval𝕞 .p,ᴹ = eval*≡' refl
eval𝕞 .q,ᴹ = eval≡[] refl[]-K
eval𝕞 .▷ηᴹ {Aᴹ = Aᴹ} {δᴹ = δᴹ} = eval*≡ λ ρ → ap (_ Σ,_) (
  δᴹ .act ρ .snd
  ≡⟨ sym coe-K ⟩
  coe _ (δᴹ .act ρ .snd)
  ≡⟨ apdd₂ (λ □ → eval _ □ _) (λ _ □ → □ .act ρ) (val≡' refl) .[]coe ⟩
  _ ∎)

-- eval𝕞 .Πᴹ {Γᴹ = Γᴹ} Aᴹ Bᴹ .El ρ t 
--   = Σ (∀ {Θ σ} (σTh : Thin Θ _ σ) {u} (υ : Aᴹ .El (ρ Γ.[ σTh ]E) u) 
--        → Bᴹ .El ((ρ Γ.[ σTh ]E) Σ, υ) (app t [ σ , u ]))
--     -- Naturality
--     λ apply → ∀ {Θ Λ σ γ} (σTh : Thin Θ _ σ) (γTh : Thin Λ Θ γ) 
--                 {u} (υ : Aᴹ .El (ρ Γ.[ σTh ]E) u)
--               →  apply σTh υ B.[ γTh ]V 
--               ≡[ ap (λ □ → B.El □ (app t [ (σ ⨾ γ) , (u [ γ ]) ])) 
--                     (apd₂ _Σ,_ Γ.[][]E refl[])
--               ]≡ apply (σTh ⨾Th γTh) 
--                        (transp (λ □ → A.El □ _) Γ.[][]E (υ A.[ γTh ]V))
--   where module Γ = Env Γᴹ
--         module A = Val Aᴹ
--         module B = Val Bᴹ
-- eval𝕞 .Πᴹ {Γᴹ = Γᴹ} Aᴹ Bᴹ ._[_]V {t = t} τ σTh .fst γTh υ 
--   = transp (λ □ → Bᴹ .El □ (app t [ _ , _ ])) 
--            (apd₂ _Σ,_ (sym (Γᴹ .[][]E)) sym-transp[]) 
--            (τ .fst (σTh ⨾Th γTh) (transp (λ □ → Aᴹ .El □ _) (Γᴹ .[][]E) υ))
-- eval𝕞 .Πᴹ Aᴹ Bᴹ ._[_]V τ σTh .snd γTh θTh υ = cheat
-- eval𝕞 .Πᴹ Aᴹ Bᴹ .[id]V = cheat
-- eval𝕞 .Πᴹ Aᴹ Bᴹ .[][]V = cheat
-- eval𝕞 .lamᴹ tᴹ .act ρ .fst σTh υ     = tᴹ .act (_ Σ, υ)
-- eval𝕞 .lamᴹ tᴹ .act ρ .snd σTh γTh υ = cheat
-- eval𝕞 .appᴹ {Γᴹ = Γᴹ} {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} tᴹ .act (ρ Σ, υ)
--   = transp (λ □ → Bᴹ .El □ _) (apd₂ _Σ,_ (Γᴹ .[id]E) transp-sym[])
--            (tᴹ .act ρ .fst idTh (transp (λ □ → Aᴹ .El □ _) (sym (Γᴹ .[id]E)) υ))
-- eval𝕞 .appᴹ {Γᴹ = Γᴹ} {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} tᴹ .nat = cheat
-- eval𝕞 .Π[]ᴹ {Aᴹ = Aᴹ} {Bᴹ = Bᴹ} {Δᴹ = Δᴹ} {δᴹ = δᴹ} 
--   = val≡ λ ρ t → apd₂ Σ (piexti λ {_} → piexti λ {_} → piext λ σTh 
--   → piexti λ {_} → piext[] (ap (λ □ → Aᴹ .El □ _) (δᴹ .nat)) λ {υ₁ υ₂} υ≡ 
--   → ap (λ □ → Bᴹ .El □ (app t [ _ ])) (apd₂ _Σ,_ (δᴹ .nat) (coe[] (
--   transp (λ □ → El Aᴹ □ _) (δᴹ .nat) υ₁
--   ≡⟨ υ≡ .[]coe ⟩
--   υ₂
--   ≡⟨ sym coe-K ⟩
--   coe _ υ₂
--   ≡⟨ apdd₂ (λ □ → eval (eval𝕞 ._▷ᴹ_ Δᴹ (eval𝕞 ._[_]Tᴹ Aᴹ δᴹ)) □ q) 
--            (λ _ □ → □ .act ((ρ Δ.[ σTh ]E) Σ, υ₂)) (val≡' refl) .[]coe ⟩
--   _ ∎)
--   ))) 
--   cheat -- I think we could prove this with propext if need be
--   where module Δ = Env Δᴹ
-- eval𝕞 .lam[]ᴹ = {!!}
-- eval𝕞 .βᴹ {tᴹ = tᴹ}
--   = eval≡ (funexti λ {_} → funexti λ {_} → funext λ (ρ Σ, υ) → 
--   ({!!}
--   ≡⟨ {!!} ⟩
--   tᴹ .act (ρ Σ, υ) ∎))
-- eval𝕞 .ηᴹ     = {!!}

-- eval𝕞 .ℤᴹ     = {!   !}
-- eval𝕞 .zeᴹ    = {!   !}
-- eval𝕞 .suᴹ    = {!   !}
-- eval𝕞 ._-ᴹ_   = {!   !}
-- eval𝕞 .IF-ZEᴹ = {!   !}

-- eval𝕞 .ℤ[]ᴹ = {!   !}
-- eval𝕞 .ze[]ᴹ = {!   !}
-- eval𝕞 .su[]ᴹ = {!   !}
-- eval𝕞 .-[]ᴹ = {!   !}
-- eval𝕞 .IF-ZE[]ᴹ = {!   !}

-- eval𝕞 .-zeᴹ = {!   !}
-- eval𝕞 .-cancelᴹ = {!   !}
-- eval𝕞 .-suᴹ = {!   !}
-- eval𝕞 .IF-ZE-zeᴹ = {!   !}
-- eval𝕞 .IF-ZE-suᴹ = {!   !}
-- eval𝕞 .IF-ZE-ze-ᴹ = {!   !}
