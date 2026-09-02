{-# OPTIONS --rewriting --prop #-}
-- Confluence check passes!
-- But slows down downstream typechecking... (not sure why)
-- {-# OPTIONS --local-confluence-check #-}

open import Agda.Builtin.Equality.Rewrite renaming (primRewriteNoMatch to ⟨_⟩)

open import Utils.Prop hiding (tt; ff; Σ; fst; snd; _,_)
open import Utils.MacroProp

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
  Tms   : Ctx Ξ → Ctx Ξ → Set
  Ty    : Ctx Ξ → Set
  Tm    : (Γ : Ctx Ξ) → Ty Γ → Set
record Sub (Δ : Ctx Φ) (Γ : Ctx Ψ) : Set

variable  
  Γ Δ Θ Λ Γ₁ Γ₂ Δ₁ Δ₂ Θ₁ Θ₂ : Ctx _
  A B C D A₁ A₂ A₃ B₁ B₂ B₃ P A[] : Ty _
  t u v t₁ t₂ t₃ u₁ u₂ u₃ : Tm _ _
  ts us vs ts₁ ts₂ : Tms _ _
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

  id⨾ᵂᵏ : idᵂᵏ ⨾ᵂᵏ ψ ≡S ψ
  {-# REWRITE id⨾ᵂᵏ #-}
  ⨾idᵂᵏ : ψ ⨾ᵂᵏ idᵂᵏ ≡S ψ
  {-# REWRITE ⨾idᵂᵏ #-}
  ⨾⨾ᵂᵏ  : (ψ ⨾ᵂᵏ φ) ⨾ᵂᵏ ξ ≡S ψ ⨾ᵂᵏ (φ ⨾ᵂᵏ ξ)
  {-# REWRITE ⨾⨾ᵂᵏ #-}

-- Contexts are a presheaf over signature weakenings
postulate
  _[_]C : Ctx Ψ → SigWk Φ Ψ → Ctx Φ

  [id]C : Γ [ idᵂᵏ ]C ≡S Γ
  {-# REWRITE [id]C #-}
  [][]C : Γ [ ψ ]C [ φ ]C ≡S Γ [ ψ ⨾ᵂᵏ φ ]C
  {-# REWRITE [][]C #-}

-- Global substitutions are pairs of signature weakenings and local 
-- substitutions
record Sub {Φ} {Ψ} Δ Γ where
  constructor _⇑_
  eta-equality
  field
    ⇓ᵂᵏ  : SigWk Φ Ψ
    ⇓ᵀᵐˢ : Tms Δ (Γ [ ⇓ᵂᵏ ]C)
open Sub public

-- Local substitutions are both displayed presheaves over signature weakenings 
-- and form a category
-- We can achieve this with a single operator (which folds substitution over
-- the list of terms)
postulate
  idᵀᵐˢ : Tms Γ Γ
  _[_]* : Tms Δ Γ → (δ : Sub Θ Δ) → Tms Θ (Γ [ δ .⇓ᵂᵏ ]C)

id : Sub Γ Γ
id = idᵂᵏ ⇑ idᵀᵐˢ

⇑ᵂᵏ : (ψ : SigWk Φ Ψ) → Sub (Γ [ ψ ]C) Γ
⇑ᵂᵏ ψ = ψ ⇑ idᵀᵐˢ

⇑ᵀᵐˢ : Tms Δ Γ → Sub Δ Γ
⇑ᵀᵐˢ δ = idᵂᵏ ⇑ δ

_⨾_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
(δ ⨾ σ) .⇓ᵂᵏ  = δ .⇓ᵂᵏ ⨾ᵂᵏ σ .⇓ᵂᵏ
(δ ⨾ σ) .⇓ᵀᵐˢ = δ .⇓ᵀᵐˢ [ σ ]*

_⨾ᵀᵐˢ_ : Tms Δ Γ → Tms Θ Δ → Tms Θ Γ
ts ⨾ᵀᵐˢ us = ts [ ⇑ᵀᵐˢ us ]*

postulate
  [id]* : ts [ id ]* ≡S ts
  {-# REWRITE [id]* #-}

  id[]* : idᵀᵐˢ [ δ ]* ≡S δ .⇓ᵀᵐˢ
  {-# REWRITE id[]* #-}

  [][]* : ts [ δ ]* [ σ ]* ≡S ts [ δ ⨾ σ ]*

[][]*' : _[_]* {Γ = ⟨ _ ⟩} (ts [ δ ]*) σ ≡S ts [ δ ⨾ σ ]*
[][]*' {ts = ts} {δ = δ} = [][]* {ts = ts} {δ = δ}
{-# REWRITE [][]*' #-}

-- Global substitutions are a category
id⨾ : id ⨾ δ ≡ δ
id⨾ = refl
⨾id : δ ⨾ id ≡ δ
⨾id = refl
⨾⨾  : (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ)
⨾⨾ = refl

-- Local substitutions are a category
id⨾ᵀᵐˢ : idᵀᵐˢ ⨾ᵀᵐˢ ts ≡S ts
id⨾ᵀᵐˢ = refl
⨾idᵀᵐˢ : ts ⨾ᵀᵐˢ idᵀᵐˢ ≡S ts
⨾idᵀᵐˢ = refl
⨾⨾ᵀᵐˢ  : (ts ⨾ᵀᵐˢ us) ⨾ᵀᵐˢ vs ≡S ts ⨾ᵀᵐˢ (us ⨾ᵀᵐˢ vs)
⨾⨾ᵀᵐˢ = refl

-- Types and terms are presheaves over substitutions
postulate
  _[_]T : Ty Γ → Sub Δ Γ → Ty Δ
  _[_]  : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)

  [id]T : A [ id ]T ≡S A
  {-# REWRITE [id]T  #-}
  [id]  : t [ id ] ≡S t
  {-# REWRITE [id] #-}

  [][]T : A [ δ ]T [ σ ]T ≡S A [ δ ⨾ σ ]T
  {-# REWRITE [][]T #-}
  [][]  : t [ δ ] [ σ ] ≡S t [ δ ⨾ σ ]

[][]' : _[_] {A = ⟨ _ ⟩} (t [ δ ]) σ ≡S t [ δ ⨾ σ ]
[][]' {t = t} {δ = δ} = [][] {t = t} {δ = δ}
{-# REWRITE [][]' #-}
-- Context operator are natural w.r.t. signature weakening
postulate
  •[] : • [ ψ ]C ≡S •
  {-# REWRITE •[] #-}

  ▷[] : (Γ ▷ A) [ ψ ]C ≡S (Γ [ ψ ]C) ▷ (A [ ⇑ᵂᵏ ψ ]T)
  {-# REWRITE ▷[] #-}

  ▷~[] : (Γ ▷ t₁ ~ t₂) [ ψ ]C ≡S (Γ [ ψ ]C) ▷ (t₁ [ ⇑ᵂᵏ ψ ]) ~ (t₂ [ ⇑ᵂᵏ ψ ])
  {-# REWRITE ▷~[] #-}

-- Context comprehension (for ordinary context extension, and extension
-- by convertibility assumptions)
-- We take |wk|/|vz| as primitive as opposed to |π₁|/|π₂| to get a confluent 
-- rewrite system
postulate
  εᵀᵐˢ    : Tms Δ •
  _,ᵀᵐˢ_  : (ts : Tms Δ Γ) → Tm Δ (A [ ⇑ᵀᵐˢ ts ]T) → Tms Δ (Γ ▷ A)
  _,~ᵀᵐˢ_ : {t₁ t₂ : Tm Γ A} (ts : Tms Δ Γ)
          → t₁ [ ⇑ᵀᵐˢ ts ] ≡ t₂ [ ⇑ᵀᵐˢ ts ]
          → Tms Δ (Γ ▷ t₁ ~ t₂)
  π₁ᵀᵐˢ   : Tms Δ (Γ ▷ A) → Tms Δ Γ
  π₁~ᵀᵐˢ  : Tms Δ (Γ ▷ t₁ ~ t₂) → Tms Δ Γ
  π₂ᵀᵐˢ   : (ts : Tms Δ (Γ ▷ A)) → Tm Δ (A [ ⇑ᵀᵐˢ (π₁ᵀᵐˢ ts) ]T)
  π₂~ᵀᵐˢ  : (ts : Tms Δ (Γ ▷ t₁ ~ t₂)) 
          → t₁ [ ⇑ᵀᵐˢ (π₁~ᵀᵐˢ ts) ] ≡ t₂ [ ⇑ᵀᵐˢ (π₁~ᵀᵐˢ ts) ]

  •ηᵀᵐˢ : ts ≡ εᵀᵐˢ

ε[]* : εᵀᵐˢ {Δ = Δ} [ δ ]* ≡S εᵀᵐˢ
ε[]* = ↑≡ •ηᵀᵐˢ
{-# REWRITE ε[]* #-}

postulate
  ,[]*  : (ts ,ᵀᵐˢ t) [ δ ]* ≡S (ts [ δ ]*) ,ᵀᵐˢ (t [ δ ])
  {-# REWRITE ,[]* #-}

  ,~[]*  : {ts : Tms {Ψ} Δ Γ}
           {t₁ t₂ : Tm Γ A}
           {t₁₂ : t₁ [ ⇑ᵀᵐˢ ts ] ≡ t₂ [ ⇑ᵀᵐˢ ts ]}
           {δ : Sub {Φ} {Ψ} Θ Δ} 
         → (_,~ᵀᵐˢ_ {t₁ = t₁} {t₂ = t₂} ts t₁₂) [ δ ]* 
         ≡S (ts [ δ ]*) ,~ᵀᵐˢ (ap (_[ δ ]) t₁₂)
  {-# REWRITE ,~[]* #-}

  π₁[]*  : π₁ᵀᵐˢ ts [ δ ]* ≡S π₁ᵀᵐˢ (ts [ δ ]*)
  {-# REWRITE π₁[]* #-}

  π₂[] : π₂ᵀᵐˢ ts [ δ ] ≡S π₂ᵀᵐˢ (ts [ δ ]*)

π₂[]' : _[_] {A = ⟨ _ ⟩} (π₂ᵀᵐˢ ts) δ ≡S π₂ᵀᵐˢ (ts [ δ ]*)
π₂[]' {ts = ts} = π₂[] {ts = ts}
{-# REWRITE π₂[]' #-}

postulate
  π₁~[]*  : π₁~ᵀᵐˢ ts [ δ ]* ≡S π₁~ᵀᵐˢ (ts [ δ ]*)
  {-# REWRITE π₁~[]* #-}

  ▷β₁ᵀᵐˢ : π₁ᵀᵐˢ (ts ,ᵀᵐˢ t) ≡S ts
  {-# REWRITE ▷β₁ᵀᵐˢ #-}
  ▷β₂ᵀᵐˢ : π₂ᵀᵐˢ (ts ,ᵀᵐˢ t) ≡S t
  {-# REWRITE ▷β₂ᵀᵐˢ #-}

  ▷~β₁ᵀᵐˢ : π₁~ᵀᵐˢ (ts ,~ᵀᵐˢ t₁₂) ≡S ts
  {-# REWRITE ▷~β₁ᵀᵐˢ #-}

  ▷ηᵀᵐˢ : π₁ᵀᵐˢ ts ,ᵀᵐˢ π₂ᵀᵐˢ ts ≡S ts
  {-# REWRITE ▷ηᵀᵐˢ #-}
  ▷~ηᵀᵐˢ : π₁~ᵀᵐˢ ts ,~ᵀᵐˢ π₂~ᵀᵐˢ ts ≡S ts
  {-# REWRITE ▷~ηᵀᵐˢ #-}

ε : (ψ : SigWk Φ Ψ) → Sub {Φ} {Ψ} Δ •
ε ψ = ψ ⇑ εᵀᵐˢ

_,_  : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
(δ , t) .⇓ᵂᵏ  = δ .⇓ᵂᵏ
(δ , t) .⇓ᵀᵐˢ = δ .⇓ᵀᵐˢ ,ᵀᵐˢ t

_,~_ : (δ : Sub Δ Γ) → t₁ [ δ ] ≡ t₂ [ δ ]
      → Sub Δ (Γ ▷ t₁ ~ t₂)
(δ ,~ t₁₂) .⇓ᵂᵏ  = δ .⇓ᵂᵏ
(δ ,~ t₁₂) .⇓ᵀᵐˢ = δ .⇓ᵀᵐˢ ,~ᵀᵐˢ t₁₂

π₁ : Sub Δ (Γ ▷ A) → Sub Δ Γ
π₁ δ .⇓ᵂᵏ  = δ .⇓ᵂᵏ
π₁ δ .⇓ᵀᵐˢ = π₁ᵀᵐˢ (δ .⇓ᵀᵐˢ)

π₂ : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ δ = π₂ᵀᵐˢ (δ .⇓ᵀᵐˢ)

π₁~ : Sub Δ (Γ ▷ t₁ ~ t₂) → Sub Δ Γ
π₁~ δ .⇓ᵂᵏ  = δ .⇓ᵂᵏ
π₁~ δ .⇓ᵀᵐˢ = π₁~ᵀᵐˢ (δ .⇓ᵀᵐˢ)

π₂~ : (δ : Sub Δ (Γ ▷ t₁ ~ t₂)) → t₁ [ π₁~ δ ] ≡ t₂ [ π₁~ δ ]
π₂~ δ = π₂~ᵀᵐˢ (δ .⇓ᵀᵐˢ)

•η : δ ≡ ε (δ .⇓ᵂᵏ)
•η {δ = δ} = ap (δ .⇓ᵂᵏ ⇑_) •ηᵀᵐˢ

wk : Sub (Γ ▷ A) Γ
wk = π₁ id

vz : Tm (Γ ▷ A) (A [ wk ]T)
vz = π₂ id

wk~ : Sub (_▷_~_ Γ {A = A} t₁ t₂) Γ
wk~ = π₁~ id

ez~ : t₁ [ wk~ {t₁ = t₁} {t₂ = t₂} ] ≡ t₂ [ wk~ ]
ez~ = π₂~ id

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
  -- Dependent function types
  Π     : ∀ A → Ty (Γ ▷ A) → Ty Γ
  lam   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → Tm (Γ ▷ A) B

  Π[]   : Π A B [ δ ]T ≡S Π (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Π[] #-}
  lam[] : lam t [ δ ] ≡S lam (t [ δ ^ A ])
  {-# REWRITE lam[] #-}

  Πβ : app (lam t) ≡S t
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

  Id[] : Id A t₁ t₂ [ δ ]T ≡S Id (A [ δ ]T) (t₁ [ δ ]) (t₂ [ δ ])
  {-# REWRITE Id[] #-}

  rfl[] : rfl {t = t} [ δ ] ≡S rfl 
  {-# REWRITE rfl[] #-}

  -- Note we don't need the J rule because it is derivable (in a sense) from 
  -- local equality reflection

variable
  eq eq' eq₁ eq₂ : Tm _ (Id _ _ _)

rflℱ : t₁ ≡ t₂ → Tm Γ (Id A t₁ t₂)
rflℱ t₁₂ with refl ← ↑≡ t₁₂ 
  = rfl

rflℱ[] : rflℱ t₁₂ [ δ ] ≡S rflℱ (ap (_[ δ ]) t₁₂)
rflℱ[] {t₁₂ = t₁₂}
  with refl ← ↑≡ t₁₂  
  = refl
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

  𝔹[]  : 𝔹 [ δ ]T ≡S 𝔹
  {-# REWRITE 𝔹[] #-}

  tt[] : tt [ δ ] ≡S tt
  {-# REWRITE tt[] #-}

  ff[] : ff [ δ ] ≡S ff
  {-# REWRITE ff[] #-}

  if[] : if P t u v [ δ ] ≡S if (P [ δ ^ 𝔹 ]T) (t [ δ ]) (u [ δ ]) (v [ δ ])

if[]' : _[_] {A = ⟨ _ ⟩} (if P t u v) δ 
      ≡S if (P [ δ ^ 𝔹 ]T) (t [ δ ]) (u [ δ ]) (v [ δ ])
if[]' {P = P} = if[] {P = P}
{-# REWRITE if[]' #-}

postulate
  IF[] : IF t A B [ δ ]T ≡S IF (t [ δ ]) (A [ δ ]T) (B [ δ ]T)
  {-# REWRITE IF[] #-}

  IF-tt : IF tt A B ≡S A
  {-# REWRITE IF-tt #-}

  IF-ff : IF ff A B ≡S B
  {-# REWRITE IF-ff #-}

  𝔹β₁ : if P t u tt ≡S t
  {-# REWRITE 𝔹β₁ #-}

  𝔹β₂ : if P t u ff ≡S u
  {-# REWRITE 𝔹β₂ #-}

-- Dependent sums
postulate
  Σ    : (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
  pair : (B : Ty (Γ ▷ A)) → (t : Tm Γ A) → Tm Γ (B [ id , t ]T) → Tm Γ (Σ A B)
  fst  : Tm Γ (Σ A B) → Tm Γ A
  snd  : (t : Tm Γ (Σ A B)) → Tm Γ (B [ id , fst t ]T)

  Σ[]  : Σ A B [ δ ]T ≡S Σ (A [ δ ]T) (B [ δ ^ A ]T)
  {-# REWRITE Σ[] #-} 

  pair[] : {δ : Sub Δ Γ}
         → pair B t u [ δ ] ≡S pair (B [ δ ^ A ]T) (t [ δ ]) (u [ δ ])
  {-# REWRITE pair[] #-}

  fst[] : fst t [ δ ] ≡S fst (t [ δ ])
  {-# REWRITE fst[] #-}

  snd[] : {δ : Sub Δ Γ}
        → snd t [ δ ] ≡S snd (t [ δ ])

snd[]' : {δ : Sub Δ Γ}
       → _[_] {A = ⟨ _ ⟩} (snd t) δ ≡S snd (t [ δ ])
snd[]' {t = t} = snd[] {t = t}
{-# REWRITE snd[]' #-}

postulate
  Σβ₁ : fst (pair B t u) ≡S t
  {-# REWRITE Σβ₁ #-}

  Σβ₂ : snd (pair B t u) ≡S u
  {-# REWRITE Σβ₂ #-}

  Ση : pair B (fst t) (snd t) ≡S t
  {-# REWRITE Ση #-}

-- Natural numbers and induction
postulate
  ℕ   : Ty Γ
  ze  : Tm Γ ℕ
  su  : Tm Γ ℕ → Tm Γ ℕ

  ℕ[] : ℕ [ δ ]T ≡S ℕ
  {-# REWRITE ℕ[] #-}
  
  ze[] : ze [ δ ] ≡S ze
  {-# REWRITE ze[] #-}
  
  su[] : su t [ δ ] ≡S su (t [ δ ])
  {-# REWRITE su[] #-}
  
  
  ind : (P : Ty {Ξ} (Γ ▷ ℕ)) 
      → Tm Γ (P [ id , ze ]T) 
      → Tm ((Γ ▷ ℕ) ▷ P) (P [ (wk , su vz) ⨾ wk ]T)
      → (t : Tm Γ ℕ)
      → Tm Γ (P [ id , t ]T)

  ind[] : ind P t u v [ δ ] 
        ≡S ind (P [ δ ^ ℕ ]T) (t [ δ ]) (u [ (δ ^ ℕ) ^ P ]) (v [ δ ])

ind[]' : _[_] {A = ⟨ _ ⟩} (ind P t u v) δ
       ≡S ind (P [ δ ^ ℕ ]T) (t [ δ ]) (u [ (δ ^ ℕ) ^ P ]) (v [ δ ])
ind[]' {P = P} = ind[] {P = P}
{-# REWRITE ind[]' #-}

postulate
  ℕβ₁ : ind P t u ze     ≡S t
  {-# REWRITE ℕβ₁ #-}
  ℕβ₂ : ind P t u (su v) ≡S u [ (id , v) , ind P t u v ]
  {-# REWRITE ℕβ₂ #-}
