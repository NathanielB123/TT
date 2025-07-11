{-# OPTIONS --prop --show-irrelevant --rewriting #-}

open import Utils
open import Utils.IdExtras
open import Common.Sort
open import Common.SortEq

-- Weak Type Theory (no definitional β/η) defined inductive-inductively without 
-- setoids or quotients
--
-- We use single substitutions as in 
-- https://raw.githubusercontent.com/szumixie/single-subst/main/lfmtp/p.pdf
-- (also https://github.com/NathanielB123/dep-ty-chk)
-- as this drastically cuts down on the number of operations
module RelSSub where

data Ctx    : Set
data Ty     : Ctx → Set
data Tm[_] : Sort → ∀ Γ → Ty Γ → Set
data Sub[_] : Sort → Ctx → Ctx → Set

Tm  = Tm[ T ]
Var = Tm[ V ]

variable
  Γ Δ Θ Γ₁ Γ₂         : Ctx
  A B A₁ A₂ A[] A[]₁ A[]₂ A[][] B₁ B₂ B[]   : Ty Γ
  δ σ  δ₁ δ₂          : Sub[ q ] Δ Γ
  t u v t[] t[]₁ t[]₂ t[][] u[] i[] i[][] t₁ t₂ t₃ u₁ u₂ : Tm[ q ] Γ A
  i j k i₁ i₂        : Var Γ A
  
data Ctx where
  •   : Ctx
  _▷_ : ∀ Γ → Ty Γ → Ctx

-- Substitution as a relation ("graph of the function")
data _[_]T≔_   : Ty Γ → Sub[ q ] Δ Γ → Ty Δ → Prop
data _[_]_≔_   : Tm[ q ] Γ A → ∀ (δ : Sub[ r ] Δ Γ) → A [ δ ]T≔ A[] 
               → Tm[ q ⊔ r ] Δ A[] → Prop

variable
  A𝒢 B𝒢 A𝒢₁ A𝒢₂ A𝒢₃ A𝒢₄ B𝒢₁ B𝒢₂ B𝒢₃ : A [ δ ]T≔ A[]

data Ty where
  U  : Ty Γ
  El : Tm Γ U → Ty Γ
  Π  : ∀ A → Ty (Γ ▷ A) → Ty Γ

data Sub[_] where
  wk  : Sub[ V ] (Γ ▷ A) Γ
  <_> : Tm Γ A → Sub[ T ] Γ (Γ ▷ A)
  _^_ : ∀ (δ : Sub[ q ] Δ Γ) → A [ δ ]T≔ A[] → Sub[ q ] (Δ ▷ A[]) (Γ ▷ A)

data Tm[_] where 
  vz    : A [ wk ]T≔ A[] → Var (Γ ▷ A) A[]
  vs    : Var Γ A → A [ wk ]T≔ A[] → Var (Γ ▷ B) A[]
  `_    : Var Γ A → Tm Γ A
  lam   : Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → ∀ (u : Tm Γ A)
        → B [ < u > ]T≔ B[] → Tm Γ B[]

-- Subsingleton elim
-- I don't think |Prop| is essential to the technique anyhow though
coeTm : A₁ ≡ᴾ A₂ → Tm[ q ] Γ A₁ → Tm[ q ] Γ A₂
coeTm A≡ t with refl ← ≡↑ A≡ = t

tm⊑ : q ⊑ r → Tm[ q ] Γ A → Tm[ r ] Γ A
tm⊑ {q = V} {r = V} _ i = i
tm⊑ {q = V} {r = T} _ i = ` i
tm⊑ {q = T} {r = T} _ t = t

data _[_]T≔_ where
  U[]  : U [ δ ]T≔ U
  El[] : t [ δ ] U[] ≔ t[] → El t [ δ ]T≔ El t[]
  Π[]  : ∀ (A𝒢 : A [ δ ]T≔ A[]) → B [ δ ^ A𝒢 ]T≔ B[] → Π A B [ δ ]T≔ Π A[] B[]

-- Laws
wk<>T  : A [ wk ]T≔ A[] → A[] [ < t > ]T≔ A

wk^T   : A [ wk ]T≔ A[]₁ → A [ δ ]T≔ A[]₂
       → A[]₁ [ δ ^ B𝒢 ]T≔ A[][]
       → A[]₂ [ wk ]T≔ A[][]

wk^  : t [ wk ] A𝒢₁ ≔ t[]₁ → t [ δ ] A𝒢₂ ≔ t[]₂
     → t[]₁ [ δ ^ B𝒢 ] A𝒢₃ ≔ t[][]
     → t[]₂ [ wk ] wk^T A𝒢₁ A𝒢₂ A𝒢₃ ≔ t[][]

^<>T   : A [ < u > ]T≔ A[]₁
       → A [ δ ^ B𝒢 ]T≔ A[]₂
       → A[]₁ [ δ ]T≔ A[][]
       → u [ δ ] B𝒢 ≔ u[]
       → A[]₂ [ < u[] > ]T≔ A[][]

Ty≡ : Γ₁ ≡ᴾ Γ₂ → Ty Γ₁ ≡ᴾ Ty Γ₂
Ty≡ refl = refl

variable
  A≡ A≡₁ A≡₂ B≡ B≡₁ B≡₂ : A₁ ≡ᴾ A₂

-- We "Ford" with *inductively defined* dependent identity to ensure strict
-- positivity
data _≡[_]Tm_ (t : Tm[ q ] Γ A₁) : A₁ ≡ᴾ A₂ → Tm[ q ] Γ A₂ → Prop where
  refl : t ≡[ refl ]Tm t

Tm≡ : A₁ ≡ᴾ A₂ → Tm[ q ] Γ A₁ ≡ᴾ Tm[ q ] Γ A₂
Tm≡ A≡ = congᴾ (Tm[ _ ] _) A≡

↑Tm≡ : t₁ ≡[ A≡ ]Tm t₂ → t₁ ≡[ Tm≡ A≡ ]≡ᴾ t₂
↑Tm≡ refl = refl
↓Tm≡ : t₁ ≡[ Tm≡ A≡ ]≡ᴾ t₂ → t₁ ≡[ A≡ ]Tm t₂
↓Tm≡ {A≡ = refl} refl = refl

coe-≡[]Tm : t₁ ≡[ A≡ ]Tm t₂ → coeTm A≡ t₁ ≡ᴾ t₂
coe-≡[]Tm refl = refl

data _[_]_≔_ where
  i[wk] : i [ wk ] A𝒢 ≔ vs i A𝒢
  -- Much neater, but produces recursive unification equations
  -- vz<> : vz A𝒢 [ < u₁ > ] wk<> A𝒢 ≔ u₂
  vz<>  : ∀ {A𝒢 : A [ wk ]T≔ A[]} {u₁ : Tm Γ A} {A𝒢₂ : A[] [ < u₁ > ]T≔ A[][]}
        → u₁ ≡[ A≡ ]Tm u₂
        → vz A𝒢 [ < u₁ > ] A𝒢₂ ≔ u₂
  -- I think we could define the substitution relation without
  -- reference to the laws (we can just ask for the relevant equations
  -- when necessary).
  vs<>  : vs i A𝒢 [ < u > ] wk<>T A𝒢 ≔ (` i)
  vs^   : i [ δ ] A𝒢₂ ≔ i[] → i[] [ wk ] wk^T A𝒢₁ A𝒢₂ A𝒢₃ ≔ i[][]
        → vs i A𝒢₁ [ δ ^ B𝒢 ] A𝒢₃ ≔ i[][]
  vz^   : vz A𝒢₁ [ δ ^ A𝒢₂ ] A𝒢₃ ≔ tm⊑ V⊑ (vz (wk^T A𝒢₁ A𝒢₂ A𝒢₃))
  `[]   : i [ δ ] A𝒢 ≔ i[] → (` i) [ δ ] A𝒢 ≔ tm⊑ ⊑T i[]
  lam[] : t [ δ ^ A𝒢 ] B𝒢 ≔ t[] → lam t [ δ ] Π[] A𝒢 B𝒢 ≔ lam t[]
  app[] : t [ δ ] Π[] A𝒢 B𝒢₂ ≔ t[] → ∀ (u𝒢 : u [ δ ] A𝒢 ≔ u[])
        → app t u B𝒢₁ [ δ ] B𝒢₃
        ≔ app t[] u[] (^<>T B𝒢₁ B𝒢₂ B𝒢₃ u𝒢)

-- To prove the laws, we need to handle arbitrary context extensions 
-- (telescopes)
-- This enables us to recurse under binders properly
data Tel (Γ : Ctx) : Set

_▷▷_ : ∀ Γ → Tel Γ → Ctx

data Tel Γ where
  •   : Tel Γ
  _▷_ : ∀ (Ξ : Tel Γ) → Ty (Γ ▷▷ Ξ) → Tel Γ

Γ ▷▷ •       = Γ
Γ ▷▷ (Ξ ▷ A) = (Γ ▷▷ Ξ) ▷ A

variable
  Ξ Ξ[] Ξ[][] : Tel Γ

-- I am not being super principled with what I am putting in |Set| vs |Prop|.
-- Putting |_[_]Ts≔_| in |Set| is useful for implementing |_^^_|, but putting
-- the other relations in |Prop| is useful for not needing to prove uniqueness.
data _[_]Ts≔_ : Tel Γ → Sub[ q ] Δ Γ → Tel Δ → Set

_^^_ : ∀ (δ : Sub[ q ] Δ Γ) → Ξ [ δ ]Ts≔ Ξ[] → Sub[ q ] (Δ ▷▷ Ξ[]) (Γ ▷▷ Ξ) 
  
data _[_]Ts≔_ where
  •[] : • [ δ ]Ts≔ •
  ▷[] : ∀ (Ξ𝒢 : Ξ [ δ ]Ts≔ Ξ[]) → A [ δ ^^ Ξ𝒢 ]T≔ A[] 
      → (Ξ ▷ A) [ δ ]Ts≔ (Ξ[] ▷ A[])

δ ^^ •[]       = δ
δ ^^ ▷[] Ξ𝒢 A𝒢 = (δ ^^ Ξ𝒢) ^ A𝒢

variable
  Ξ𝒢 Ξ𝒢₁ Ξ𝒢₂ : Ξ [ δ ]Ts≔ Ξ[]
  t𝒢 u𝒢 : t [ δ ] _ ≔ t[] 

wk<>Ts  : Ξ [ wk ]Ts≔ Ξ[] → Ξ[] [ < u > ]Ts≔ Ξ
wk<>T^^ : ∀ {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]} {Ξ𝒢₂ : Ξ[] [ < u > ]Ts≔ Ξ}
        → A [ wk ^^ Ξ𝒢₁ ]T≔ A[] → A[] [ < u > ^^ Ξ𝒢₂ ]T≔ A
wk<>^^  : ∀ {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]} {Ξ𝒢₂ : Ξ[] [ < u > ]Ts≔ Ξ} {A𝒢}
        → t [ wk ^^ Ξ𝒢₁ ] A𝒢 ≔ t[] 
        → t[] [ < u > ^^ Ξ𝒢₂ ] wk<>T^^ A𝒢 ≔ tm⊑ ⊑T t

wk<>Ts •[]         = •[]
wk<>Ts (▷[] Ξ𝒢 A𝒢) = ▷[] (wk<>Ts Ξ𝒢) (wk<>T^^ A𝒢)

wk<>T^^ U[]         = U[]
wk<>T^^ (El[] t𝒢)   = El[] (wk<>^^ t𝒢)
wk<>T^^ (Π[] A𝒢 B𝒢) = Π[] (wk<>T^^ A𝒢) (wk<>T^^ B𝒢)

wk<>^^ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} i[wk] = vs<>
wk<>^^ (`[] i𝒢)             = `[] (wk<>^^ i𝒢)
wk<>^^ (lam[] {A𝒢 = A𝒢} t𝒢) = lam[] {A𝒢 = wk<>T^^ A𝒢} (wk<>^^ t𝒢)
wk<>^^ (app[] {B𝒢₂ = B𝒢₂} t𝒢 u𝒢) 
  = app[] {B𝒢₂ = wk<>T^^ B𝒢₂} (wk<>^^ t𝒢) (wk<>^^ u𝒢)
wk<>^^ {t = vs i A𝒢} {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} (vs^ i𝒢 i[wk]) 
  = vs^ (wk<>^^ i𝒢) (`[] i[wk])
wk<>^^ {t = vz A𝒢} {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} vz^ = vz^

wk<>T = wk<>T^^

-- TODO: Prove other laws similarly

π₁Π[] : Π A B [ δ ]T≔ Π A[] B[] → A [ δ ]T≔ A[]
π₁Π[] (Π[] A𝒢 B𝒢) = A𝒢

π₂Π[] : ∀ (AB𝒢 : Π A B [ δ ]T≔ Π A[] B[]) → B [ δ ^ π₁Π[] AB𝒢 ]T≔ B[] 
π₂Π[] (Π[] A𝒢 B𝒢) = B𝒢

-- Now we show that substitution is computable

_[_]T : Ty Γ → Sub[ q ] Δ Γ → Ty Δ
_[_]_ : Tm[ q ] Γ A → ∀ (δ : Sub[ r ] Δ Γ) → A [ δ ]T≔ A[] 
      → Tm[ q ⊔ r ] Δ A[]
[]T   : A [ δ ]T≔ (A [ δ ]T)
[]    : t [ δ ] A𝒢 ≔ (_[_]_ {r = r} {A[] = A[]} t δ A𝒢)

[]T≡ : A [ δ ]T≔ A[] → A [ δ ]T ≡ᴾ A[]
[]≡ : t [ δ ] A𝒢 ≔ t[] → _[_]_ {r = r} t δ A𝒢 ≡ᴾ t[]

U     [ δ ]T = U
El t  [ δ ]T = El (t [ δ ] U[])
Π A B [ δ ]T = Π (A [ δ ]T) (B [ δ ^ []T ]T)

-- Curiously, termination fails if we squish these cases together.
-- Exact splits for operations (like substitution) is probably a good idea
-- anyway...
vz A𝒢   [ wk ] B𝒢 = vs (vz A𝒢) B𝒢
vs i A𝒢 [ wk ] B𝒢 = vs (vs i A𝒢) B𝒢

vz A𝒢₁   [ δ ^ A𝒢₂ ] A𝒢₃ = tm⊑ V⊑ (vz (wk^T A𝒢₁ A𝒢₂ A𝒢₃))
vz A𝒢₁   [ < u > ]   A𝒢₂ = coeTm (symᴾ ([]T≡ (wk<>T A𝒢₁)) ∙ᴾ []T≡ A𝒢₂) u
vs i A𝒢₁ [ < u > ]   A𝒢₂ = coeTm (symᴾ ([]T≡ (wk<>T A𝒢₁)) ∙ᴾ []T≡ A𝒢₂) (` i)

_[_]_ {r = V} (vs i A𝒢₁) (δ ^ B𝒢) A𝒢₂ 
  = vs (i [ δ ] []T) (wk^T A𝒢₁ []T A𝒢₂)
_[_]_ {r = T} (vs i A𝒢₁) (δ ^ B𝒢) A𝒢₂ 
  = (i [ δ ] []T) [ wk ] (wk^T A𝒢₁ []T A𝒢₂)

(` i) [ δ ] A𝒢 = tm⊑ ⊑T (i [ δ ] A𝒢)
_[_]_ {A[] = Π A[] B[]} (lam t) δ AB𝒢 
  = lam (t [ δ ^ π₁Π[] AB𝒢 ] π₂Π[] AB𝒢)
app t u B𝒢₁ [ δ ] B𝒢₂ 
  = app (t [ δ ] (Π[] []T []T)) (u [ δ ] []T) (^<>T B𝒢₁ []T B𝒢₂ [])


coe[]T-rhs : A[]₁ ≡ᴾ A[]₂ → A [ δ ]T≔ A[]₁ → A [ δ ]T≔ A[]₂
coe[]T-rhs refl A𝒢 = A𝒢

[]coh : t [ δ ] coe[]T-rhs (symᴾ A≡) A𝒢 ≔ t[] → t [ δ ] A𝒢 ≔ coeTm A≡ t[]
[]coh {A≡ = refl} t𝒢 = t𝒢

[]T {A = U}     = U[]
[]T {A = El t}  = El[] []
[]T {A = Π A B} = Π[] []T []T

[] {t = vz A𝒢}    {δ = wk}      = i[wk]
[] {t = vs i A𝒢}  {δ = wk}      = i[wk]
[] {t = vz A𝒢}    {δ = < u >}   = []coh (vz<> refl)
[] {t = vs i A𝒢}  {δ = < u >}   = []coh vs<>
[] {t = vz A𝒢₁}   {δ = δ ^ A𝒢₂} = vz^
[] {t = vs i A𝒢₁} {r = V} {δ = δ ^ A𝒢₂} = vs^ [] i[wk]
[] {t = vs i A𝒢₁} {r = T} {δ = δ ^ A𝒢₂} = vs^ [] []

[] {t = ` i}        = `[] []
[] {t = lam t} {A[] = Π A[] B[]} = lam[] []
[] {t = app t u B𝒢} = app[] {B𝒢₂ = []T} [] []


[]Tℱ : (A [ δ ]T) ≡ᴾ A[] → A [ δ ]T≔ A[]
[]Tℱ refl = []T

Π[]≡ : ∀ (A≡ : A [ δ ]T ≡ᴾ A[]) → B [ δ ^ A𝒢 ]T ≡ᴾ B[] 
      → Π A B [ δ ]T ≡ᴾ Π A[] B[]
Π[]≡ refl refl = refl

lam[]≡ : t [ δ ^ A𝒢 ] B𝒢 ≡ᴾ t[] 
        → lam t [ δ ] (Π[] A𝒢 B𝒢) ≡ᴾ lam t[]
lam[]≡ refl = refl

app[]≡ : A [ δ ]T ≡ᴾ A[] → B [ δ ^ A𝒢 ]T ≡ᴾ B[]
        → t [ δ ] (Π[] A𝒢 B𝒢₂) ≡ᴾ t[] → u [ δ ] A𝒢 ≡ᴾ u[]
        → app {A = A} {B = B} t u B𝒢₁ [ δ ] B𝒢₃ 
        ≡ᴾ app {A = A[]} {B = B[]} t[] u[]  (^<>T B𝒢₁ B𝒢₂ B𝒢₃ u𝒢)
app[]≡ refl refl refl refl = refl

vs[]≡ : A [ δ ]T ≡ᴾ A[] → i [ δ ] A𝒢₂ ≡ᴾ i[] 
      → vs {A = A} i A𝒢₁ [ δ ^ B𝒢 ] A𝒢₃ ≡ᴾ vs {A = A[]} i[] (wk^T A𝒢₁ A𝒢₂ A𝒢₃)
vs[]≡ refl refl = refl

[][wk]≡ : A [ δ ]T ≡ᴾ A[] → _[_]_ {A = A} {A[] = A[]} t δ A𝒢₂ ≡ᴾ t[] 
        → t[] [ wk ] wk^T A𝒢₁ A𝒢₂ A𝒢₃ ≡ᴾ t[][]
        → (t [ δ ] []T) [ wk ] wk^T A𝒢₁ []T A𝒢₃ ≡ᴾ t[][]
[][wk]≡ refl refl refl = refl


[]T≡ U[]         = refl
[]T≡ (El[] t𝒢)   = congᴾ El ([]≡ t𝒢)
[]T≡ (Π[] A𝒢 B𝒢) = Π[]≡ ([]T≡ A𝒢) ([]T≡ B𝒢)

[]≡ {t = vz A𝒢} i[wk] = refl
[]≡ {t = vs i A𝒢} i[wk] = refl
[]≡ (vz<> refl) = refl
[]≡ vs<> = refl

[]≡ {r = V} (vs^ {i = i} {A𝒢₂ = A𝒢₂} {A𝒢₁ = A𝒢₁} {A𝒢₃ = A𝒢₃} i𝒢 i[wk]) 
  = vs[]≡ {i = i} {A𝒢₁ = A𝒢₁} {A𝒢₃ = A𝒢₃} ([]T≡ A𝒢₂) ([]≡ i𝒢)
[]≡ {r = T} (vs^ {i = i} {A𝒢₂ = A𝒢₂} {A𝒢₁ = A𝒢₁} {A𝒢₃ = A𝒢₃} i𝒢 i[]𝒢)
  = [][wk]≡ {t = i} {A𝒢₁ = A𝒢₁} {A𝒢₃ = A𝒢₃} ([]T≡ A𝒢₂) ([]≡ i𝒢) ([]≡ i[]𝒢)
[]≡ vz^ = refl
[]≡ (`[] i𝒢) = congᴾ (tm⊑ ⊑T) ([]≡ i𝒢)
[]≡ (lam[] {t = t} {B𝒢 = B𝒢} t𝒢) = lam[]≡ {t = t} ([]≡ t𝒢)
[]≡ (app[] {t = t} {A𝒢 = A𝒢} {B𝒢₂ = B𝒢₂}  {u = u} {B𝒢₁ = B𝒢₁} {B𝒢₃ = B𝒢₃} 
           t𝒢 u𝒢) 
  = app[]≡ {t = t} {B𝒢₂ = B𝒢₂} {B𝒢₁ = B𝒢₁} {B𝒢₃ = B𝒢₃} {u𝒢 = u𝒢} 
           ([]T≡ A𝒢) ([]T≡ B𝒢₂) ([]≡ t𝒢) ([]≡ u𝒢) 
