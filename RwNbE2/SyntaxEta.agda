{-# OPTIONS --rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality.Rewrite renaming (primRewriteNoMatch to ⟨_⟩)

open import Utils renaming (_,_ to _Σ,_)
open import Utils.WithK
open import Utils.Macro

-- We postulate a strictified syntax
module RwNbE2.SyntaxEta where

data Sig           : Set
data Ctx (Ξ : Sig) : Set

variable
  Ξ Ψ Φ : Sig

postulate
  SigWk : Sig → Sig → Set
  Sub   : Ctx Φ → Ctx Ψ → Set
  Ty  : Ctx Ξ → Set
  Tm  : (Γ : Ctx Ξ) → Ty Γ → Set

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

-- Substitutions are a category, and embed signature weakenings
postulate
  ⇑ᵂᵏ  : (ψ : SigWk Φ Ψ) → Sub (Γ [ ψ ]C) Γ
id    : Sub Γ Γ
id = ⇑ᵂᵏ idᵂᵏ
{-# DISPLAY ⇑ᵂᵏ idᵂᵏ = id #-}
postulate
  _⨾_  : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ

  id⨾ : id ⨾ δ ≡ δ
  {-# REWRITE id⨾ #-}
  ⨾id : δ ⨾ id ≡ δ
  {-# REWRITE ⨾id #-}
  ⨾⨾  : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
  {-# REWRITE ⨾⨾ #-}
  ⇑⨾ᵂᵏ : {ψ : SigWk Φ Ψ} {φ : SigWk Ξ Φ}
       → ⇑ᵂᵏ {Γ = Γ} (ψ ⨾ᵂᵏ φ) ≡ ⇑ᵂᵏ ψ ⨾ ⇑ᵂᵏ φ
  {-# REWRITE ⇑⨾ᵂᵏ #-}

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

-- Context comprehension (for ordinary context extension, and extension
-- by convertibility assumptions)
-- We use |p|/|q| as opposed to |π₁|/|π₂| style to get a confluent 
-- rewrite system
postulate
  _,_  : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
  _,~_ : (δ : Sub Δ Γ) → t₁ [ δ ] ≡ t₂ [ δ ]
       → Sub Δ (Γ ▷ t₁ ~ t₂)
  p   : Sub (Γ ▷ A) Γ
  q   : Tm (Γ ▷ A) (A [ p ]T)
  p~  : Sub (_▷_~_ Γ {A = A} t₁ t₂) Γ
  q~  : t₁ [ p~ {t₁ = t₁} {t₂ = t₂} ] ≡ t₂ [ p~ ]

  ,⨾  : (δ , t) ⨾ σ ≡ (δ ⨾ σ) , (t [ σ ])
  {-# REWRITE ,⨾ #-}

  ,~⨾ : (δ ,~ t₁₂) ⨾ σ ≡ (δ ⨾ σ) ,~ (t₁₂ [ σ ]≡)
  {-# REWRITE ,~⨾ #-}

  p, : p ⨾ (δ , t) ≡ δ
  {-# REWRITE p, #-}
  q, : q [ δ , t ] ≡ t

q,' : _[_] {A = ⟨ _ ⟩} q (δ , t) ≡ t
q,' {δ = δ} = q, {δ = δ}
{-# REWRITE q,' #-}

postulate
  p,~ : p~ ⨾ (δ ,~ t₁₂) ≡ δ
  {-# REWRITE p,~ #-}

q,~ : q~ [ δ ,~ t₁₂ ]≡ ≡ t₁₂
q,~ = uip

q,~' : _[_]≡ {A = ⟨ _ ⟩} {t₁ = ⟨ _ ⟩} {t₂ = ⟨ _ ⟩} q~ (δ ,~ t₁₂) ≡ t₁₂
q,~' {δ = δ} = q,~ {δ = δ}
{-# REWRITE q,~' #-}

postulate
  id▷  : id {Γ = Γ ▷ A} ≡ p , q
  id▷~ : id {Γ = Γ ▷ t₁ ~ t₂} ≡ p~ ,~ q~ 

π₁ : Sub Δ (Γ ▷ A) → Sub Δ Γ
π₁ δ = p ⨾ δ

π₂ : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ δ = q [ δ ]

π₁~ : Sub Δ (Γ ▷ t₁ ~ t₂) → Sub Δ Γ
π₁~ δ = p~ ⨾ δ

π₂~ : (δ : Sub Δ (Γ ▷ t₁ ~ t₂)) → t₁ [ π₁~ δ ] ≡ t₂ [ π₁~ δ ]
π₂~ δ = q~ [ δ ]≡

▷η : δ ≡ (π₁ δ) , (π₂ δ)
▷η {δ = δ} =
  δ
  ≡⟨⟩
  ⌜ id ⌝ ⨾ δ
  ≡⟨ ap! id▷ ⟩
  (p , q) ⨾ δ
  ≡⟨⟩
  (p ⨾ δ) , (q [ δ ])
  ≡⟨⟩ 
  (π₁ δ) , (π₂ δ) ∎

▷η~ : δ ≡ (π₁~ δ) ,~ (π₂~ δ)
▷η~ {δ = δ} =
  δ
  ≡⟨⟩
  ⌜ id ⌝ ⨾ δ
  ≡⟨ ap! id▷~ ⟩
  (p~ ,~ q~) ⨾ δ
  ≡⟨⟩
  (p~ ⨾ δ) ,~ (q~ [ δ ]≡)
  ≡⟨⟩ 
  (π₁~ δ) ,~ (π₂~ δ) ∎

id▷' : p , q ≡ id {Γ = Γ ▷ A}
id▷' = sym id▷

▷η' : (p ⨾ δ) , (_[_] {A = ⟨ _ ⟩} q δ) ≡ δ
▷η' = sym ▷η
{-# REWRITE id▷' ▷η' #-}

id▷~' : p~ ,~ q~ ≡ id {Γ = Γ ▷ t₁ ~ t₂}
id▷~' = sym id▷~

▷η~' : (p~ ⨾ δ) ,~ (_[_]≡ {A = ⟨ _ ⟩} {t₁ = ⟨ _ ⟩} {t₂ = ⟨ _ ⟩} q~ δ) ≡ δ
▷η~' = sym ▷η~
{-# REWRITE id▷~' ▷η~' #-}

postulate
  ε  : SigWk Φ Ψ → Sub {Φ} {Ψ} Δ •
  •η : δ ≡ ε ψ

_^_ : ∀ δ A → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ A = (δ ⨾ p) , q

_^_~_ : ∀ δ (t₁ t₂ : Tm Γ A) → Sub (Δ ▷ t₁ [ δ ] ~ (t₂ [ δ ])) (Γ ▷ t₁ ~ t₂)
δ ^ t₁ ~ t₂ = (δ ⨾ p~) ,~ 
  (t₁ [ δ ⨾ p~ ]
  ≡⟨⟩
  t₁ [ δ ] [ p~ ]
  ≡⟨ q~ ⟩
  t₂ [ δ ] [ p~ ]
  ≡⟨⟩
  t₂ [ δ ⨾ p~ ] ∎)


postulate
  -- Π types
  Π     : ∀ A → Ty (Γ ▷ A) → Ty Γ
  lam   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → Tm (Γ ▷ A) B

  Π[]   : Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Π[] #-}
  lam[] : lam t [ δ ] ≡ lam (t [ δ ^ A ])
  {-# REWRITE lam[] #-}

  β : app (lam t) ≡ t
  {-# REWRITE β #-}
  η : t ≡ lam (app t)

app[] : {t : Tm Γ (Π A B)}
      → app (t [ δ ]) ≡ app t [ δ ^ A ]
app[] {A = A} {δ = δ} {t = t} = 
  app (⌜ t ⌝ [ δ ])
  ≡⟨ ap! (η {t = t}) ⟩
  app (lam (app t) [ δ ])
  ≡⟨⟩
  app (lam (app t [ δ ^ A ]))
  ≡⟨ β ⟩
  app t [ δ ^ A ] ∎

app[]' : {t : Tm Γ (Π A B)}
       → app {A = ⟨ _ ⟩} {B = ⟨ _ ⟩} (t [ δ ]) ≡ app t [ δ ^ A ]
app[]' {t = t} = app[] {t = t}

{-# REWRITE app[]' #-}

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
  eq : Tm _ (Id _ _ _)

rflℱ : t₁ ≡ t₂ → Tm Γ (Id A t₁ t₂)
rflℱ refl = rfl

rflℱ[] : rflℱ t₁₂ [ δ ] ≡ rflℱ (t₁₂ [ δ ]≡)
rflℱ[] {t₁₂ = refl} = refl
{-# REWRITE rflℱ[] #-}

-- Signatures
data Sig where
  []                  : Sig
  _def_to_reflect_begin_end 
    : ∀ (Ξ : Sig) (Γ : Ctx Ξ) B {A} {t₁ t₂ : Tm Γ A} (eq : Tm Γ (Id A t₁ t₂)) 
    → Tm ((Γ ▷ t₁ ~ t₂) ▷ eq [ p~ ] ~ rflℱ q~) 
         (B [ p~ ⨾ p~ ]T)
    → Sig

-- Single definition weakening
postulate
  defᵂᵏ : SigWk (Ξ def Γ to B reflect eq begin u end) Ξ

-- Calls to definitions
postulate
  call : Tm {Ξ = Ξ def Γ to B reflect t begin u end} 
            (Γ [ defᵂᵏ ]C) (B [ ⇑ᵂᵏ defᵂᵏ ]T)

  defβ : {eq : Tm Γ (Id A t₁ t₂)}
         {u : Tm ((Γ ▷ t₁ ~ t₂) ▷ (eq [ p~ ]) ~ rflℱ q~) (B [ p~ ⨾ p~ ]T)} 
         {δ : Sub Δ (Γ [ defᵂᵏ {B = B} {u = u} ]C)} 
         (t₁₂ : t₁ [ ⇑ᵂᵏ defᵂᵏ ⨾ δ ] ≡ t₂ [ ⇑ᵂᵏ defᵂᵏ ⨾ δ ])
         (eqrfl : eq [ ⇑ᵂᵏ defᵂᵏ ⨾ δ ] ≡ rflℱ t₁₂)
       → call {t = eq} [ δ ] 
       ≡ u [ ((⇑ᵂᵏ defᵂᵏ ⨾ δ) ,~ t₁₂) ,~ eqrfl ]

-- Booleans and large elimination
postulate
  𝔹     : Ty Γ
  TT FF : Tm Γ 𝔹
  IF    : Tm Γ 𝔹 → Ty Γ → Ty Γ → Ty Γ

  𝔹[]  : 𝔹 [ δ ]T ≡ 𝔹
  {-# REWRITE 𝔹[] #-}

  TT[] : TT [ δ ] ≡ TT
  {-# REWRITE TT[] #-}

  FF[] : FF [ δ ] ≡ FF
  {-# REWRITE FF[] #-}

  IF[] : IF t A B [ δ ]T ≡ IF (t [ δ ]) (A [ δ ]T) (B [ δ ]T)
  {-# REWRITE IF[] #-}

  IF-TT : IF TT A B ≡ A
  {-# REWRITE IF-TT #-}

  IF-FF : IF FF A B ≡ B
  {-# REWRITE IF-FF #-}

-- Sums and dependent case
postulate
  _⊎_  : Ty Γ → Ty Γ → Ty Γ
  in1  : Tm Γ A → Tm Γ (A ⊎ B)
  in2  : Tm Γ B → Tm Γ (A ⊎ B)

  ⊎[] : (A ⊎ B) [ δ ]T ≡ (A [ δ ]T) ⊎ (B [ δ ]T)
  {-# REWRITE ⊎[] #-}

  in1[]  : in1 {B = B} t [ δ ] ≡ in1 (t [ δ ])
  {-# REWRITE in1[] #-}

  in2[] : in2 {A = A} t [ δ ] ≡ in2 (t [ δ ])
  {-# REWRITE in2[] #-}

  case : (P : Ty (Γ ▷ (A ⊎ B))) 
       → Tm (Γ ▷ A) (P [ p , in1 q ]T)
       → Tm (Γ ▷ B) (P [ p , in2 q ]T)
       → (t : Tm Γ (A ⊎ B))
       → Tm Γ (P [ id , t ]T)

  case[] : case P t u v [ δ ] 
         ≡ case (P [ δ ^ (A ⊎ B) ]T) (t [ δ ^ A ]) (u [ δ ^ B ]) (v [ δ ])

case[]' : _[_] {A = ⟨ _ ⟩} (case P t u v) δ 
        ≡ case (P [ δ ^ (A ⊎ B) ]T) (t [ δ ^ A ]) (u [ δ ^ B ]) (v [ δ ])
case[]' {P = P} = case[] {P = P} 
{-# REWRITE case[]' #-}

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
      → Tm ((Γ ▷ ℕ) ▷ P) (P [ (p , su q) ⨾ p ]T)
      → (t : Tm Γ ℕ)
      → Tm Γ (P [ id , t ]T)

  ind[] : ind P t u v [ δ ] 
        ≡ ind (P [ δ ^ ℕ ]T) (t [ δ ]) (u [ (δ ^ ℕ) ^ P ]) (v [ δ ])

ind[]' : _[_] {A = ⟨ _ ⟩} (ind P t u v) δ
       ≡ ind (P [ δ ^ ℕ ]T) (t [ δ ]) (u [ (δ ^ ℕ) ^ P ]) (v [ δ ])
ind[]' {P = P} = ind[] {P = P}
{-# REWRITE ind[]' #-}
