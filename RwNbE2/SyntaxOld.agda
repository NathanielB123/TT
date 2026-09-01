{-# OPTIONS --rewriting #-}
-- Confluence check passes!
-- But slows down downstream typechecking... (not sure why)
-- {-# OPTIONS --local-confluence-check #-}

open import Agda.Builtin.Equality.Rewrite renaming (primRewriteNoMatch to ⟨_⟩)

open import Utils hiding (tt; ff) hiding (Σ; fst; snd; _,_)
open import Utils.WithK
open import Utils.Macro

-- We postulate a strictified syntax
module RwNbE2.Syntax where

-- We define signatures and contexts as inductive datatypes in order to get
-- pattern matching and automatic disjointness/injectivity
--
-- Contexts also feature a signature weakening operator |_[_]C| plus equations, 
-- so it is technically not immediate that all contexts can be formed purely in
-- terms of |•|, |_▷_| and |_▷_~_| and that these operators are 
-- disjoint/injective.
-- We could show this manually by way of a simple context-normalisation model.
data Sig           : Set
data Ctx (Ξ : Sig) : Set

variable
  Ξ Ψ Φ : Sig

postulate
  SigWk : Sig → Sig → Set
  Sub   : Ctx Φ → Ctx Ψ → Set
  Ty    : Ctx Ξ → Set
  Tm    : (Γ : Ctx Ξ) → Ty Γ → Set

variable  
  Γ Δ Θ Λ Γ₁ Γ₂ Δ₁ Δ₂ Θ₁ Θ₂ : Ctx _
  A B C D A₁ A₂ A₃ B₁ B₂ B₃ P : Ty _
  t u v t₁ t₂ t₃ u₁ u₂ u₃ : Tm _ _
  φ ψ ξ : SigWk _ _
  δ σ γ δ₁ δ₂ : Sub _ _
  t₁₂ u₁₂ : _≡_ {A = Tm _ _} _ _

-- We define contexts as a datatype to allow pattern matching and get easy
-- disjointness and injectivity of constructors
data Ctx Ξ where
  •     : Ctx Ξ
  _▷_   : (Γ : Ctx Ξ) → Ty Γ → Ctx Ξ
  _▷_~_ : ∀ (Γ : Ctx Ξ) {A} → Tm Γ A → Tm Γ A → Ctx Ξ

-- Signature weakenings are a category
postulate
  idᵂᵏ  : SigWk Ψ Ψ
  _⨾ᵂᵏ_ : SigWk Φ Ψ → SigWk Ξ Φ → SigWk Ξ Ψ

  id⨾ᵂᵏ : idᵂᵏ ⨾ᵂᵏ ψ ≡ ψ
  {-# REWRITE id⨾ᵂᵏ #-}
  ⨾idᵂᵏ : ψ ⨾ᵂᵏ idᵂᵏ ≡ ψ
  {-# REWRITE ⨾idᵂᵏ #-}
  ⨾⨾ᵂᵏ  : (ψ ⨾ᵂᵏ φ) ⨾ᵂᵏ ξ ≡ ψ ⨾ᵂᵏ (φ ⨾ᵂᵏ ξ)
  {-# REWRITE ⨾⨾ᵂᵏ #-}

-- Contexts are a presheaf over signature weakenings
postulate
  _[_]C : Ctx Ψ → SigWk Φ Ψ → Ctx Φ

  [id]C : Γ [ idᵂᵏ ]C ≡ Γ
  {-# REWRITE [id]C #-}
  [][]C : Γ [ ψ ]C [ φ ]C ≡ Γ [ ψ ⨾ᵂᵏ φ ]C
  {-# REWRITE [][]C #-}

-- Substitutions are a category
postulate
  id  : Sub Γ Γ
  _⨾_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ

  id⨾ : id ⨾ δ ≡ δ
  {-# REWRITE id⨾ #-}
  ⨾id : δ ⨾ id ≡ δ
  {-# REWRITE ⨾id #-}
  ⨾⨾  : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
  {-# REWRITE ⨾⨾ #-}

-- Substitutions embed signature weakenings
postulate
  ⇑ᵂᵏ  : (ψ : SigWk Φ Ψ) → Sub (Γ [ ψ ]C) Γ
  
  ⇑idᵂᵏ : ⇑ᵂᵏ {Γ = Γ} idᵂᵏ ≡ id
  {-# REWRITE ⇑idᵂᵏ #-}

  ⇑⨾ᵂᵏ  : {ψ : SigWk Φ Ψ} {φ : SigWk Ξ Φ}
        → ⇑ᵂᵏ {Γ = Γ} (ψ ⨾ᵂᵏ φ) ≡ ⇑ᵂᵏ ψ ⨾ ⇑ᵂᵏ φ
  {-# REWRITE ⇑⨾ᵂᵏ #-}

_[_]S : Sub Δ Γ → (ψ : SigWk Φ Ψ) → Sub (Δ [ ψ ]C) Γ
δ [ ψ ]S = δ ⨾ ⇑ᵂᵏ ψ

-- Types and terms are presheaves over substitutions

postulate
  _[_]T : Ty Γ → Sub Δ Γ → Ty Δ
  _[_]  : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)

  [id]T : A [ id ]T ≡ A
  {-# REWRITE [id]T  #-}
  [id]  : t [ id ] ≡ t
  {-# REWRITE [id] #-}

  [][]T : A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T
  {-# REWRITE [][]T #-}
  [][]  : t [ δ ] [ σ ] ≡ t [ δ ⨾ σ ]

[][]' : _[_] {A = ⟨ _ ⟩} (t [ δ ]) σ ≡ t [ δ ⨾ σ ]
[][]' {t = t} {δ = δ} = [][] {t = t} {δ = δ}
{-# REWRITE [][]' #-}

-- Specialised congruence with extra computation rules for confluence
_[_]≡ : _≡_ {A = Tm Γ A} t₁ t₂ → (δ : Sub Δ Γ) → t₁ [ δ ] ≡ t₂ [ δ ]
refl [ δ ]≡ = refl

[id]≡ : t₁₂ [ id ]≡ ≡ t₁₂
[id]≡ {t₁₂ = refl} = refl

[][]≡ : _[_]≡ {A = ⟨ _ ⟩} {t₁ = ⟨ _ ⟩} {t₂ = ⟨ _ ⟩} (t₁₂ [ δ ]≡) σ
      ≡ t₁₂ [ δ ⨾ σ ]≡
[][]≡ {t₁₂ = refl} = refl

{-# REWRITE [id]≡ [][]≡ #-}

-- Context operator are natural w.r.t. signature weakening
postulate
  •[] : • [ ψ ]C ≡ •
  {-# REWRITE •[] #-}

  ▷[] : (Γ ▷ A) [ ψ ]C ≡ (Γ [ ψ ]C) ▷ (A [ ⇑ᵂᵏ ψ ]T)
  {-# REWRITE ▷[] #-}

  ▷~[] : (Γ ▷ t₁ ~ t₂) [ ψ ]C ≡ (Γ [ ψ ]C) ▷ (t₁ [ ⇑ᵂᵏ ψ ]) ~ (t₂ [ ⇑ᵂᵏ ψ ])
  {-# REWRITE ▷~[] #-}

-- Context comprehension (for ordinary context extension, and extension
-- by convertibility assumptions)
postulate
  _,_  : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
  _,~_ : (δ : Sub Δ Γ) → t₁ [ δ ] ≡ t₂ [ δ ]
       → Sub Δ (Γ ▷ t₁ ~ t₂)
  π₁   : Sub Δ (Γ ▷ A) → Sub Δ Γ
  π₂   : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
  π₁~  : Sub Δ (Γ ▷ t₁ ~ t₂) → Sub Δ Γ
  π₂~  : (δ : Sub Δ (Γ ▷ t₁ ~ t₂)) → t₁ [ π₁~ δ ] ≡ t₂ [ π₁~ δ ]

  ,⨾  : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , (t [ σ ])
  {-# REWRITE ,⨾ #-}

  ,~⨾ : (δ ,~ t₁₂) ⨾ σ ≡ (δ ⨾ σ) ,~ (t₁₂ [ σ ]≡)
  {-# REWRITE ,~⨾ #-}

  π₁⨾ : π₁ δ ⨾ σ ≡ π₁ (δ ⨾ σ)
  {-# REWRITE π₁⨾ #-}

  π₂[] : π₂ δ [ σ ] ≡ π₂ (δ ⨾ σ)

π₂[]' : _[_] {A = ⟨ _ ⟩} (π₂ δ) σ ≡ π₂ (δ ⨾ σ)
π₂[]' {δ = δ} = π₂[] {δ = δ}
{-# REWRITE π₂[]' #-}

postulate
  π₁~⨾ : π₁~ δ ⨾ σ ≡ π₁~ (δ ⨾ σ)
  {-# REWRITE π₁~⨾ #-}

  π₂~[] : π₂~ δ [ σ ]≡ ≡ π₂~ (δ ⨾ σ)

π₂~[]' : _[_]≡ {A = ⟨ _ ⟩} {t₁ = ⟨ _ ⟩} {t₂ = ⟨ _ ⟩} (π₂~ δ) σ
       ≡ π₂~ (δ ⨾ σ)
π₂~[]' {δ = δ} = π₂~[] {δ = δ}
{-# REWRITE π₂~[]' #-}

postulate
  ▷β₁ : π₁ (δ , t) ≡ δ
  {-# REWRITE ▷β₁ #-}
  ▷β₂ : π₂ (δ , t) ≡ t
  {-# REWRITE ▷β₂ #-}

  ▷~β₁ : π₁~ (δ ,~ t₁₂) ≡ δ
  {-# REWRITE ▷~β₁ #-}
  ▷~β₂ : π₂~ (δ ,~ t₁₂) ≡ t₁₂
  {-# REWRITE ▷~β₂ #-}

  ▷η  : π₁ δ , π₂ δ ≡ δ
  ▷~η : π₁~ δ ,~ π₂~ δ ≡ δ
  {-# REWRITE ▷η ▷~η #-}

wk : Sub (Γ ▷ A) Γ
wk = π₁ id

vz : Tm (Γ ▷ A) (A [ wk ]T)
vz = π₂ id

wk~ : Sub (_▷_~_ Γ {A = A} t₁ t₂) Γ
wk~ = π₁~ id

ez~ : t₁ [ wk~ {t₁ = t₁} {t₂ = t₂} ] ≡ t₂ [ wk~ ]
ez~ = π₂~ id

postulate
  ε  : SigWk Φ Ψ → Sub {Φ} {Ψ} Δ •
  •η : δ ≡ ε ψ

_^_ : ∀ δ A → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ A = (δ ⨾ wk) , vz

_^_~_ : ∀ δ (t₁ t₂ : Tm Γ A) → Sub (Δ ▷ t₁ [ δ ] ~ (t₂ [ δ ])) (Γ ▷ t₁ ~ t₂)
δ ^ t₁ ~ t₂ = (δ ⨾ wk~) ,~ 
  (t₁ [ δ ⨾ wk~ ]
  ≡⟨⟩
  t₁ [ δ ] [ wk~ ]
  ≡⟨ ez~ ⟩
  t₂ [ δ ] [ wk~ ]
  ≡⟨⟩
  t₂ [ δ ⨾ wk~ ] ∎)


postulate
  -- Π types
  Π     : ∀ A → Ty (Γ ▷ A) → Ty Γ
  lam   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → Tm (Γ ▷ A) B

  Π[]   : Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Π[] #-}
  lam[] : lam t [ δ ] ≡ lam (t [ δ ^ A ])
  {-# REWRITE lam[] #-}

  Πβ : app (lam t) ≡ t
  {-# REWRITE Πβ #-}
  Πη : t ≡ lam (app t)

app[] : {t : Tm Γ (Π A B)}
      → app (t [ δ ]) ≡ app t [ δ ^ A ]
app[] {A = A} {δ = δ} {t = t} = 
  app (⌜ t ⌝ [ δ ])
  ≡⟨ ap! (Πη {t = t}) ⟩
  app (lam (app t) [ δ ])
  ≡⟨⟩
  app (lam (app t [ δ ^ A ]))
  ≡⟨⟩
  app t [ δ ^ A ] ∎

-- Identity types
postulate
  Id  : (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ
  rfl : Tm Γ (Id A t t)

  Id[] : Id A t₁ t₂ [ δ ]T ≡ Id (A [ δ ]T) (t₁ [ δ ]) (t₂ [ δ ])
  {-# REWRITE Id[] #-}

  rfl[] : rfl {t = t} [ δ ] ≡ rfl 
  {-# REWRITE rfl[] #-}

  -- Note we don't need the J rule because it is derivable (in a sense) from 
  -- local equality reflection

variable
  eq eq' eq₁ eq₂ : Tm _ (Id _ _ _)

rflℱ : t₁ ≡ t₂ → Tm Γ (Id A t₁ t₂)
rflℱ refl = rfl

rflℱ[] : rflℱ t₁₂ [ δ ] ≡ rflℱ (t₁₂ [ δ ]≡)
rflℱ[] {t₁₂ = refl} = refl
{-# REWRITE rflℱ[] #-}

-- Signatures
data Sig where
  []                  : Sig
  -- Paper uses separator 'in' but Agda reserves that identifier
  -- I think 'begin' is cute
  _def_to_reflect_begin_end 
    : ∀ (Ξ : Sig) (Γ : Ctx Ξ) B {A} {t₁ t₂ : Tm Γ A} (eq : Tm Γ (Id A t₁ t₂)) 
    → Tm ((Γ ▷ t₁ ~ t₂) ▷ eq [ wk~ ] ~ rflℱ ez~) 
         (B [ wk~ ⨾ wk~ ]T)
    → Sig

-- Single definition weakening
postulate
  defᵂᵏ : SigWk (Ξ def Γ to B reflect eq begin u end) Ξ

-- Calls to definitions
postulate
  call : Tm {Ξ = Ξ def Γ to B reflect t begin u end} 
            (Γ [ defᵂᵏ ]C) (B [ ⇑ᵂᵏ defᵂᵏ ]T)

  defβ : {eq : Tm Γ (Id A t₁ t₂)}
         {u : Tm ((Γ ▷ t₁ ~ t₂) ▷ (eq [ wk~ ]) ~ rflℱ ez~) (B [ wk~ ⨾ wk~ ]T)} 
         {δ : Sub Δ (Γ [ defᵂᵏ {B = B} {u = u} ]C)} 
         (t₁₂ : t₁ [ ⇑ᵂᵏ defᵂᵏ ⨾ δ ] ≡ t₂ [ ⇑ᵂᵏ defᵂᵏ ⨾ δ ])
         (eqrfl : eq [ ⇑ᵂᵏ defᵂᵏ ⨾ δ ] ≡ rflℱ t₁₂)
       → call {t = eq} [ δ ] 
       ≡ u [ ((⇑ᵂᵏ defᵂᵏ ⨾ δ) ,~ t₁₂) ,~ eqrfl ]

-- Booleans and large elimination
postulate
  𝔹     : Ty Γ
  tt ff : Tm Γ 𝔹
  if    : (P : Ty (Γ ▷ 𝔹)) → Tm Γ (P [ id , tt ]T) → Tm Γ (P [ id , ff ]T)
        → (b : Tm Γ 𝔹) → Tm Γ (P [ id , b ]T)
  IF    : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ

  𝔹[]  : 𝔹 [ δ ]T ≡ 𝔹
  {-# REWRITE 𝔹[] #-}

  tt[] : tt [ δ ] ≡ tt
  {-# REWRITE tt[] #-}

  ff[] : ff [ δ ] ≡ ff
  {-# REWRITE ff[] #-}

  if[] : if P t u v [ δ ] ≡ if (P [ δ ^ 𝔹 ]T) (t [ δ ]) (u [ δ ]) (v [ δ ])

if[]' : _[_] {A = ⟨ _ ⟩} (if P t u v) δ 
      ≡ if (P [ δ ^ 𝔹 ]T) (t [ δ ]) (u [ δ ]) (v [ δ ])
if[]' {P = P} = if[] {P = P}
{-# REWRITE if[]' #-}

postulate
  IF[] : IF t A B [ δ ]T ≡ IF (t [ δ ]) (A [ δ ]T) (B [ δ ]T)
  {-# REWRITE IF[] #-}

  IF-tt : IF tt A B ≡ A
  {-# REWRITE IF-tt #-}

  IF-ff : IF ff A B ≡ B
  {-# REWRITE IF-ff #-}

  𝔹β₁ : if P t u tt ≡ t
  {-# REWRITE 𝔹β₁ #-}

  𝔹β₂ : if P t u ff ≡ u
  {-# REWRITE 𝔹β₂ #-}

-- Dependent sums
postulate
  Σ    : (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
  pair : (B : Ty (Γ ▷ A)) → (t : Tm Γ A) → Tm Γ (B [ id , t ]T) → Tm Γ (Σ A B)
  fst  : Tm Γ (Σ A B) → Tm Γ A
  snd  : (t : Tm Γ (Σ A B)) → Tm Γ (B [ id , fst t ]T)

  Σ[]  : Σ A B [ δ ]T ≡ Σ (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Σ[] #-} 

  pair[] : pair B t u [ δ ] ≡ pair (B [ δ ^ A ]T) (t [ δ ]) (u [ δ ])
  {-# REWRITE pair[] #-}

  fst[] : fst t [ δ ] ≡ fst (t [ δ ])
  {-# REWRITE fst[] #-}

  snd[] : snd t [ δ ] ≡ snd (t [ δ ])

snd[]' : _[_] {A = ⟨ _ ⟩} (snd t) δ ≡ snd (t [ δ ])
snd[]' {t = t} = snd[] {t = t}
{-# REWRITE snd[]' #-}

postulate
  Σβ₁ : fst (pair B t u) ≡ t
  {-# REWRITE Σβ₁ #-}

  Σβ₂ : snd (pair B t u) ≡ u
  {-# REWRITE Σβ₂ #-}

  Ση : t ≡ pair B (fst t) (snd t)
  
Ση' : pair B (fst t) (snd t) ≡ t
Ση' = sym Ση
{-# REWRITE Ση' #-}

-- Natural numbers and induction
postulate
  ℕ   : Ty Γ
  ze  : Tm Γ ℕ
  su  : Tm Γ ℕ → Tm Γ ℕ

  ℕ[] : ℕ [ δ ]T ≡ ℕ
  {-# REWRITE ℕ[] #-}
  
  ze[] : ze [ δ ] ≡ ze
  {-# REWRITE ze[] #-}
  
  su[] : su t [ δ ] ≡ su (t [ δ ])
  {-# REWRITE su[] #-}
  
  
  ind : (P : Ty {Ξ} (Γ ▷ ℕ)) 
      → Tm Γ (P [ id , ze ]T) 
      → Tm ((Γ ▷ ℕ) ▷ P) (P [ (wk , su vz) ⨾ wk ]T)
      → (t : Tm Γ ℕ)
      → Tm Γ (P [ id , t ]T)

  ind[] : ind P t u v [ δ ] 
        ≡ ind (P [ δ ^ ℕ ]T) (t [ δ ]) (u [ (δ ^ ℕ) ^ P ]) (v [ δ ])

ind[]' : _[_] {A = ⟨ _ ⟩} (ind P t u v) δ
       ≡ ind (P [ δ ^ ℕ ]T) (t [ δ ]) (u [ (δ ^ ℕ) ^ P ]) (v [ δ ])
ind[]' {P = P} = ind[] {P = P}
{-# REWRITE ind[]' #-}

postulate
  ℕβ₁ : ind P t u ze     ≡ t
  {-# REWRITE ℕβ₁ #-}
  ℕβ₂ : ind P t u (su v) ≡ u [ (id , v) , ind P t u v ]
  {-# REWRITE ℕβ₂ #-}

-- Disjoint unions and dependent case
-- (I am removing these from the paper because they are not so different
-- from Booleans - in fact, we can essentially get disjoint unions just from
-- dependent sums and large IF!)
postulate
  _⊎_  : Ty Γ → Ty Γ → Ty Γ
  inL  : Tm Γ A → Tm Γ (A ⊎ B)
  inR  : Tm Γ B → Tm Γ (A ⊎ B)

  ⊎[] : (A ⊎ B) [ δ ]T ≡ (A [ δ ]T) ⊎ (B [ δ ]T)
  {-# REWRITE ⊎[] #-}

  inL[]  : inL {B = B} t [ δ ] ≡ inL (t [ δ ])
  {-# REWRITE inL[] #-}

  inR[] : inR {A = A} t [ δ ] ≡ inR (t [ δ ])
  {-# REWRITE inR[] #-}

  case : (P : Ty (Γ ▷ (A ⊎ B))) 
       → Tm (Γ ▷ A) (P [ wk , inL vz ]T)
       → Tm (Γ ▷ B) (P [ wk , inR vz ]T)
       → (t : Tm Γ (A ⊎ B))
       → Tm Γ (P [ id , t ]T)

  case[] : case P t u v [ δ ] 
         ≡ case (P [ δ ^ (A ⊎ B) ]T) (t [ δ ^ A ]) (u [ δ ^ B ]) (v [ δ ])

case[]' : _[_] {A = ⟨ _ ⟩} (case P t u v) δ 
        ≡ case (P [ δ ^ (A ⊎ B) ]T) (t [ δ ^ A ]) (u [ δ ^ B ]) (v [ δ ])
case[]' {P = P} = case[] {P = P} 
{-# REWRITE case[]' #-}

postulate
  ⊎β₁ : case P t u (inL v) ≡ (t [ id , v ])
  {-# REWRITE ⊎β₁ #-}
  ⊎β₂ : case P t u (inR v) ≡ (u [ id , v ])
  {-# REWRITE ⊎β₂ #-}
