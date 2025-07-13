{-# OPTIONS --rewriting #-}

open import Utils
open import Common.Sort
open import Common.SortEq

open import RelSSub.Syntax
open import RelSSub.SubUniq
open import RelSSub.Laws1

-- The commuting laws are more painful, all mutually depending on each other.
--
-- The structural decrease is |Sort| also does not appear to be enough to
-- satisfy Agda's termination checking if we try to prove these laws for both
-- weakening and substitutions at once, so we deal with weakening and
-- substitution separately (sadly, copy-and-pasting a lot of code...)
module RelSSub.Laws2Wk where

record wk^TOut (δ : Sub[ r ] Δ Γ) A A[][]
               (Ξ𝒢₁ : Ξ [ δ ]Ts≔ Ξ[]) (Ξ𝒢₂ : Ξ[] [ wk ]Ts≔ Ξ[][]) : Set 
               where
  no-eta-equality
  pattern
  field
    πA[] : Ty (Δ ▷▷ Ξ[])
    πA𝒢₁ : A [ δ ^^ Ξ𝒢₁ ]T≔ πA[]
    πA𝒢₂ : πA[] [ wk ^^ Ξ𝒢₂ ]T≔ A[][]

record wk^Out (δ : Sub[ r ] Δ Γ) 
              (t : Tm[ q ] (Γ ▷▷ Ξ) A) t[][]
              (Ξ𝒢₁ : Ξ [ δ ]Ts≔ Ξ[]) (Ξ𝒢₂ : Ξ[] [ wk ]Ts≔ Ξ[][]) 
              (πA𝒢s : wk^TOut δ A A[][] Ξ𝒢₁ Ξ𝒢₂) : Set
              where
  no-eta-equality
  pattern
  open wk^TOut πA𝒢s
  field
    πt[] : Tm[ _ ] (Δ ▷▷ Ξ[]) πA[]
    πt𝒢₁ : t [ δ ^^ Ξ𝒢₁ ] πA𝒢₁ ≔ πt[]
    πt𝒢₂ : πt[] [ wk ^^ Ξ𝒢₂ ] πA𝒢₂ ≔ t[][]

record ^wkTOut (δ : Sub[ r ] Δ Γ) (B𝒢 : B [ δ ]T≔ B[]) A A[][]
               (Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]) (Ξ𝒢₂ : Ξ[] [ δ ^ B𝒢 ]Ts≔ Ξ[][])
               : Set where
  no-eta-equality
  pattern
  field
    πA[] : Ty ((Γ ▷ B) ▷▷ Ξ[])
    πA𝒢₁ : A [ wk ^^ Ξ𝒢₁ ]T≔ πA[]
    πA𝒢₂ : πA[] [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ]T≔ A[][]

record ^wkOut (δ : Sub[ r ] Δ Γ) (B𝒢 : B [ δ ]T≔ B[])
              (t : Tm[ q ] (Γ ▷▷ Ξ) A) t[][]
              (Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]) (Ξ𝒢₂ : Ξ[] [ δ ^ B𝒢 ]Ts≔ Ξ[][])
              (πA𝒢s : ^wkTOut δ B𝒢 A A[][] Ξ𝒢₁ Ξ𝒢₂) : Set
              where
  no-eta-equality
  pattern
  open ^wkTOut πA𝒢s
  field
    πt[] : Tm[ _ ] ((Γ ▷ B) ▷▷ Ξ[]) πA[]
    πt𝒢₁ : t [ wk ^^ Ξ𝒢₁ ] πA𝒢₁ ≔ πt[]
    πt𝒢₂ : πt[] [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ] πA𝒢₂ ≔ t[][]

open wk^TOut public
open wk^Out public

open ^wkTOut public
open ^wkOut public

wk^T^^ : ∀ (δ : Sub[ V ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]₁} 
           {Ξ𝒢₂ : Ξ[]₁ [  δ ^ B𝒢 ]Ts≔ Ξ[][]} 
           {Ξ𝒢₃ : Ξ [ δ ]Ts≔ Ξ[]₂} 
           {Ξ𝒢₄ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
       → A [ wk ^^ Ξ𝒢₁ ]T≔ A[] 
       → A[] [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ]T≔ A[][]
       → wk^TOut δ A A[][] Ξ𝒢₃ Ξ𝒢₄

wk^^^ : ∀ (δ : Sub[ V ] Δ Γ) {B𝒢}
          {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]₁} 
          {Ξ𝒢₂ : Ξ[]₁ [  δ ^ B𝒢 ]Ts≔ Ξ[][]} 
          {Ξ𝒢₃ : Ξ [ δ ]Ts≔ Ξ[]₂} 
          {Ξ𝒢₄ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
          {A𝒢₁ A𝒢₂ A[]′ A𝒢₃ A𝒢₄}
       → _[_]_≔_ {q = q} t (wk ^^ Ξ𝒢₁) A𝒢₁ t[] 
       → t[] [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ] A𝒢₂ ≔ t[][]
       → wk^Out δ t t[][] Ξ𝒢₃ Ξ𝒢₄ 
                (record {πA[] = A[]′ ; πA𝒢₁ = A𝒢₃ ; πA𝒢₂ = A𝒢₄})

^wkT^^ : ∀ (δ : Sub[ V ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ δ ]Ts≔ Ξ[]₂}
           {Ξ𝒢₂ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
           {Ξ𝒢₃ : Ξ [ wk ]Ts≔ Ξ[]₁} 
           {Ξ𝒢₄ : Ξ[]₁ [ δ ^ B𝒢 ]Ts≔ Ξ[][]} 
       → A [ δ ^^ Ξ𝒢₁ ]T≔ A[]
       → A[] [ wk ^^ Ξ𝒢₂ ]T≔ A[][]
       → ^wkTOut δ B𝒢 A A[][] Ξ𝒢₃ Ξ𝒢₄

^wk^^  : ∀ (δ : Sub[ V ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ δ ]Ts≔ Ξ[]₂}
           {Ξ𝒢₂ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
           {Ξ𝒢₃ : Ξ [ wk ]Ts≔ Ξ[]₁} 
           {Ξ𝒢₄ : Ξ[]₁ [ δ ^ B𝒢 ]Ts≔ Ξ[][]} 
           {A𝒢₁ A𝒢₂ A[]′ A𝒢₃ A𝒢₄}
       → _[_]_≔_ {q = q} t (δ ^^ Ξ𝒢₁) A𝒢₁ t[]
       → t[] [ wk ^^ Ξ𝒢₂ ] A𝒢₂ ≔ t[][]
       → ^wkOut δ B𝒢 t t[][] Ξ𝒢₃ Ξ𝒢₄ 
                (record {πA[] = A[]′ ; πA𝒢₁ = A𝒢₃ ; πA𝒢₂ = A𝒢₄})

^<>T^^ : ∀ (δ : Sub[ V ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ < u > ]Ts≔ Ξ[]₁}
           {Ξ𝒢₂ : Ξ [ δ ^ B𝒢 ]Ts≔ Ξ[]₂}
           {Ξ𝒢₃ : Ξ[]₁ [ δ ]Ts≔ Ξ[][]}
           {Ξ𝒢₄ : Ξ[]₂ [ < u[] > ]Ts≔ Ξ[][]}
       → A [ < u > ^^ Ξ𝒢₁ ]T≔ A[]₁
       → A [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ]T≔ A[]₂
       → A[]₁ [ δ ^^ Ξ𝒢₃ ]T≔ A[][] 
       → u [ δ ] B𝒢 ≔ u[]
       → A[]₂ [ < u[] > ^^ Ξ𝒢₄ ]T≔ A[][]

^<>^^  : ∀ (δ : Sub[ V ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ < u > ]Ts≔ Ξ[]₁}
           {Ξ𝒢₂ : Ξ [ δ ^ B𝒢 ]Ts≔ Ξ[]₂}
           {Ξ𝒢₃ : Ξ[]₁ [ δ ]Ts≔ Ξ[][]}
           {Ξ𝒢₄ : Ξ[]₂ [ < u[] > ]Ts≔ Ξ[][]}
           {A𝒢₁ A𝒢₂ A𝒢₃ A𝒢₄}
       → _[_]_≔_ {q = q} t (< u > ^^ Ξ𝒢₁) A𝒢₁ t[]₁
       → t [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ] A𝒢₂ ≔ t[]₂
       → t[]₁ [ δ ^^ Ξ𝒢₃ ] A𝒢₃ ≔ t[][] 
       → (u𝒢 : u [ δ ] B𝒢 ≔ u[])
       → t[]₂ [ < u[] > ^^ Ξ𝒢₄ ] A𝒢₄ ≔ t[][]

wk^T^^ δ U[] U[] 
  = record { πA𝒢₁ = U[] ; πA𝒢₂ = U[] }
wk^T^^ δ (El[] t𝒢₁) (El[] t𝒢₂) 
  using t𝒢s ← wk^^^ δ t𝒢₁ t𝒢₂
  = record { πA𝒢₁ = El[] (t𝒢s .πt𝒢₁) ; πA𝒢₂ = El[] (t𝒢s .πt𝒢₂) }
wk^T^^ δ (Π[] A𝒢₁ B𝒢₁) (Π[] A𝒢₂ B𝒢₂) 
  using A𝒢s ← wk^T^^ δ A𝒢₁ A𝒢₂
      | B𝒢s ← wk^T^^ δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                        {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _}
                        B𝒢₁ B𝒢₂
  = record { πA𝒢₁ = Π[] (A𝒢s .πA𝒢₁) (B𝒢s .πA𝒢₁)
           ; πA𝒢₂ = Π[] (A𝒢s .πA𝒢₂) (B𝒢s .πA𝒢₂)
           }

^wkT^^ δ U[] U[] 
  = record { πA𝒢₁ = U[] ; πA𝒢₂ = U[] }
^wkT^^ δ (El[] t𝒢₁) (El[] t𝒢₂) 
  using t𝒢s ← ^wk^^ δ t𝒢₁ t𝒢₂
  = record { πA𝒢₁ = El[] (t𝒢s .πt𝒢₁) ; πA𝒢₂ = El[] (t𝒢s .πt𝒢₂) }
^wkT^^ δ (Π[] A𝒢₁ B𝒢₁) (Π[] A𝒢₂ B𝒢₂) 
  using A𝒢s ← ^wkT^^ δ A𝒢₁ A𝒢₂
      | B𝒢s ← ^wkT^^ δ 
                     {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                     {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _}
                     B𝒢₁ B𝒢₂
  = record { πA𝒢₁ = Π[] (A𝒢s .πA𝒢₁) (B𝒢s .πA𝒢₁)
           ; πA𝒢₂ = Π[] (A𝒢s .πA𝒢₂) (B𝒢s .πA𝒢₂)
           }

^<>T^^ δ U[]        U[]        U[]        u𝒢 = U[]
^<>T^^ δ (El[] t𝒢₁) (El[] t𝒢₂) (El[] t𝒢₃) u𝒢 
  = El[] (^<>^^ δ t𝒢₁ t𝒢₂ t𝒢₃ u𝒢)
^<>T^^ δ (Π[] A𝒢₁ B𝒢₁) (Π[] A𝒢₂ B𝒢₂) (Π[] A𝒢₃ B𝒢₃) u𝒢 
  = Π[] (^<>T^^ δ A𝒢₁ A𝒢₂ A𝒢₃ u𝒢) 
        (^<>T^^ δ {Ξ𝒢₂ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _} B𝒢₁ B𝒢₂ B𝒢₃ u𝒢)

wk^^^ {q = T} δ (`[] i𝒢₁) (`[] i𝒢₂)
  using i𝒢s ← wk^^^ δ i𝒢₁ i𝒢₂
  = record { πt𝒢₁ = `[] (i𝒢s .πt𝒢₁)  ; πt𝒢₂ = `[] (i𝒢s .πt𝒢₂) }
wk^^^ {q = T} δ {A𝒢₃ = Π[] _ _} {A𝒢₄ = Π[] _ _} 
      (lam[] {A𝒢 = A𝒢₁} t𝒢₁) (lam[] {A𝒢 = A𝒢₂} t𝒢₂)
  using t𝒢s ← wk^^^ δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                      {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _} 
                    t𝒢₁ t𝒢₂
  = record { πt𝒢₁ = lam[] (t𝒢s .πt𝒢₁)  ; πt𝒢₂ = lam[] (t𝒢s .πt𝒢₂) }
wk^^^ {q = T} δ {A𝒢₃ = B𝒢₃}
      (app[] {A𝒢 = A𝒢₁} {B𝒢₂ = B𝒢₁} {B𝒢₁ = B[]𝒢₁} t𝒢₁ u𝒢₁) 
      (app[] {A𝒢 = A𝒢₂} {B𝒢₂ = B𝒢₂} t𝒢₂ u𝒢₂) 
  using A𝒢s ← wk^T^^ δ A𝒢₁ A𝒢₂
      | B𝒢s ← wk^T^^ δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                        {Ξ𝒢₃ = ▷[] _ (A𝒢s .πA𝒢₁)} {Ξ𝒢₄ = ▷[] _ (A𝒢s .πA𝒢₂)}
                        B𝒢₁ B𝒢₂
      | t𝒢s ← wk^^^ δ t𝒢₁ t𝒢₂
      | u𝒢s ← wk^^^ δ u𝒢₁ u𝒢₂
      | B𝒢′ ← ^<>T^^ (δ ^^ _)  
                     {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]}
                     B[]𝒢₁ (πA𝒢₁ B𝒢s) B𝒢₃ (u𝒢s .πt𝒢₁)
  = record { πt𝒢₁ = app[] {B𝒢₂ = B𝒢s .πA𝒢₁} {B𝒢₄ = B𝒢′} 
                          (t𝒢s .πt𝒢₁) (u𝒢s .πt𝒢₁)  
           ; πt𝒢₂ = app[] {B𝒢₂ = B𝒢s .πA𝒢₂} (t𝒢s .πt𝒢₂) (u𝒢s .πt𝒢₂)  }

wk^^^ {q = V} δ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]}
      {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
      i[wk] (vs^ {A𝒢₂ = A𝒢₃′} {A𝒢₄ = A𝒢₄′} i𝒢₂ i[]𝒢₂)
  with refl ← []T-uniq A𝒢₃ A𝒢₃′
  with refl ← u[]Tp A𝒢₃ A𝒢₃′
     | refl ← u[]Tp A𝒢₄ A𝒢₄′
  = record { πt𝒢₁ = i𝒢₂ ; πt𝒢₂ = i[]𝒢₂ }
wk^^^ {q = V} δ
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
      {Ξ𝒢₃ = ▷[] Ξ𝒢₃ A𝒢₂} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _} 
      {A𝒢₃ = A𝒢₃}
  (vz^ {A𝒢₁ = A𝒢₁}) vz^ 
  using A𝒢s ← wk^T^^ (δ ^^ Ξ𝒢₃) 
                     {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                     A𝒢₁ A𝒢₃
      | Acoh ← []T-uniq (πA𝒢₁ A𝒢s) A𝒢₂
  = record { πt𝒢₁ = vz^ {A𝒢₄ = coe[]T-lhs Acoh (πA𝒢₂ A𝒢s)} ; πt𝒢₂ = vz^ }
wk^^^ {q = V} {t = vs i A𝒢} {t[] = vs i[] A[]𝒢} δ 
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
      {Ξ𝒢₃ = ▷[] Ξ𝒢₃ _} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ B𝒢}
      {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
      (vs^ {A𝒢₂ = A𝒢₁} i𝒢₁ i[wk]) (vs^ {A𝒢₂ = A𝒢₂} i𝒢₂ i[wk]) 
  using A𝒢s ← wk^T^^ δ A𝒢₁ A𝒢₂
      | i𝒢s ← wk^^^ δ {A𝒢₃ = πA𝒢₁ A𝒢s} {A𝒢₄ = πA𝒢₂ A𝒢s} i𝒢₁ i𝒢₂
      | A𝒢s′ ← wk^T^^ (δ ^^ Ξ𝒢₃) 
                      {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]}
                      A𝒢 A𝒢₃
      | Acoh ← []T-uniq (πA𝒢₁ A𝒢s′) (πA𝒢₁ A𝒢s)
  = record { πt𝒢₁ = vs^ {A𝒢₄ = coe[]T-lhs Acoh (πA𝒢₂ A𝒢s′)} (i𝒢s .πt𝒢₁) i[wk] 
           ; πt𝒢₂ = vs^ (i𝒢s .πt𝒢₂) i[wk] } 

^wk^^ {q = T} δ (`[] i𝒢₁) (`[] i𝒢₂)
  using i𝒢s ← ^wk^^ δ i𝒢₁ i𝒢₂
  = record { πt𝒢₁ = `[] (i𝒢s .πt𝒢₁)  ; πt𝒢₂ = `[] (i𝒢s .πt𝒢₂) }
^wk^^ {q = T} δ {A𝒢₃ = Π[] _ _} {A𝒢₄ = Π[] _ _}
      (lam[] {A𝒢 = A𝒢₁} t𝒢₁) (lam[] {A𝒢 = A𝒢₂} t𝒢₂)
  using t𝒢s ← ^wk^^ δ
                    {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                    {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _} 
                    t𝒢₁ t𝒢₂
  = record { πt𝒢₁ = lam[] (t𝒢s .πt𝒢₁)  ; πt𝒢₂ = lam[] (t𝒢s .πt𝒢₂) }
  
^wk^^ {q = T} δ
      {A𝒢₃ = B𝒢₃}
      (app[] {A𝒢 = A𝒢₁} {B𝒢₂ = B𝒢₁} {B𝒢₁ = B[]𝒢₁} t𝒢₁ u𝒢₁) 
      (app[] {A𝒢 = A𝒢₂} {B𝒢₂ = B𝒢₂} t𝒢₂ u𝒢₂) 
  using A𝒢s ← ^wkT^^ δ A𝒢₁ A𝒢₂
      | B𝒢s ← ^wkT^^ δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                     {Ξ𝒢₃ = ▷[] _ (A𝒢s .πA𝒢₁)} {Ξ𝒢₄ = ▷[] _ (A𝒢s .πA𝒢₂)}
                     B𝒢₁ B𝒢₂
      | t𝒢s ← ^wk^^ δ t𝒢₁ t𝒢₂
      | u𝒢s ← ^wk^^ δ u𝒢₁ u𝒢₂
      | B𝒢′ ← ^<>T^^ (wk ^^ _) 
                     {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]}
                     B[]𝒢₁ (B𝒢s .πA𝒢₁) B𝒢₃ (u𝒢s .πt𝒢₁)
  = record { πt𝒢₁ = app[] {B𝒢₂ = B𝒢s .πA𝒢₁} 
                          {B𝒢₄ = B𝒢′} 
                          (t𝒢s .πt𝒢₁) (u𝒢s .πt𝒢₁)  
           ; πt𝒢₂ = app[] {B𝒢₂ = B𝒢s .πA𝒢₂} (t𝒢s .πt𝒢₂) (u𝒢s .πt𝒢₂)  }

^wk^^ {q = V} δ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} {A𝒢₂ = A𝒢₂}
      i𝒢₁ i𝒢₂
  = record { πt𝒢₁ = i[wk] ; πt𝒢₂ = vs^ i𝒢₁ i𝒢₂ }

^wk^^ {q = V} δ
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
      {Ξ𝒢₃ = ▷[] Ξ𝒢₃ A𝒢₂} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _} 
      {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
  (vz^ {A𝒢₁ = A𝒢₁} {A𝒢₂ = wah} {A𝒢₃ = bah}) vz^ 
  using A𝒢s ← wk^T^^ (wk ^^ _)
                     {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                     A𝒢₁ A𝒢₃
      | Acoh ← []T-uniq (πA𝒢₁ A𝒢s) A𝒢₂
  = record { πt𝒢₁ = vz^ {A𝒢₄ = coe[]T-lhs Acoh (πA𝒢₂ A𝒢s)} ; πt𝒢₂ = vz^ }

^wk^^ {q = V} {t = vs i A𝒢} {t[] = vs i[] A[]𝒢} δ
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
      {Ξ𝒢₃ = ▷[] Ξ𝒢₃ _} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _} 
      {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
      (vs^ {A𝒢₂ = A𝒢₁} i𝒢₁ i[wk]) 
      (vs^ {A𝒢₂ = A𝒢₂} i𝒢₂ i[wk])
  using A𝒢s ← ^wkT^^ δ A𝒢₁ A𝒢₂
      | i𝒢s ← ^wk^^ δ {A𝒢₃ = A𝒢s .πA𝒢₁} {A𝒢₄ = A𝒢s .πA𝒢₂} i𝒢₁ i𝒢₂
      | A[]𝒢s ← wk^T^^ (wk ^^ _) 
                       {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                       A𝒢 A𝒢₃
      | Acoh ← []T-uniq (πA𝒢₁ A[]𝒢s) (πA𝒢₁ A𝒢s)
  = record { πt𝒢₁ = vs^ {A𝒢₄ = coe[]T-lhs Acoh (πA𝒢₂ A[]𝒢s)} (i𝒢s .πt𝒢₁) i[wk] 
           ; πt𝒢₂ = vs^ (i𝒢s .πt𝒢₂) i[wk] }

^<>^^ {q = V} δ {B𝒢 = A𝒢′} 
      {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} {A𝒢₃ = A𝒢₃}
  vz<> vz^ i𝒢₃ u𝒢 
  with refl ← []T-uniq A𝒢₃ A𝒢′
  with refl ← u[]Tp A𝒢₃ A𝒢′
  with refl ← []-uniq  i𝒢₃ u𝒢
  = vz<>
^<>^^ {q = V} δ {B𝒢 = B𝒢} {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
  {A𝒢₄ = A𝒢₄}
  vs<> (vs^ {A𝒢₂ = A𝒢₂} {A𝒢₄ = A[]𝒢₂} i𝒢₂ i[]𝒢₂) (`[] {A𝒢 = A𝒢₃} i𝒢₃) u𝒢 
  with refl ← []T-uniq A𝒢₂ A𝒢₃
  with refl ← u[]Tp A𝒢₂ A𝒢₃
  with refl ← []-uniq i𝒢₂ i𝒢₃
  with refl ← u[]Tp A𝒢₄ (wk<>T^^ A[]𝒢₂)
  = wk<>^^ i[]𝒢₂

^<>^^ {q = T} δ (`[] i𝒢₁) (`[] i𝒢₂) i𝒢₃ u𝒢 
  = `[] (^<>^^ δ i𝒢₁ i𝒢₂ i𝒢₃ u𝒢)
^<>^^ {q = T} δ 
      {A𝒢₄ = Π[] _ _}
      (lam[] t𝒢₁) (lam[] t𝒢₂) (lam[] t𝒢₃) u𝒢 
  = lam[] (^<>^^ δ {Ξ𝒢₂ = ▷[] _ _} t𝒢₁ t𝒢₂ t𝒢₃ u𝒢)
^<>^^ {q = T} δ 
      (app[] {A𝒢 = A𝒢₁} {B𝒢₂ = B𝒢₁} t𝒢₁ u𝒢₁) 
      (app[] {A𝒢 = A𝒢₂} {B𝒢₂ = B𝒢₂} t𝒢₂ u𝒢₂) 
      (app[] {A𝒢 = A𝒢₃} {B𝒢₂ = B𝒢₃} t𝒢₃ u𝒢₃) 
      v𝒢 
  using A𝒢′ ← ^<>T^^ δ A𝒢₁ A𝒢₂ A𝒢₃ v𝒢
      | B𝒢′ ← ^<>T^^ δ {Ξ𝒢₂ = ▷[] _ _} B𝒢₁ B𝒢₂ B𝒢₃ v𝒢
      | t𝒢′ ← ^<>^^ δ t𝒢₁ t𝒢₂ t𝒢₃ v𝒢
      | u𝒢′ ← ^<>^^ δ {A𝒢₄ = A𝒢′} u𝒢₁ u𝒢₂ u𝒢₃ v𝒢
  = app[] {B𝒢₂ = B𝒢′} t𝒢′ u𝒢′ 
^<>^^ {q = V} δ 
      {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _} 
      vz^ vz^ (`[] vz^) u𝒢 
  = vz^
^<>^^ {q = V} δ
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} {Ξ𝒢₃ = ▷[] Ξ𝒢₃ _} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _}
      {A𝒢₃ = A𝒢₃}
      (vs^ {i = i} {A𝒢₂ = A𝒢₁} {i[] = i[]} {A𝒢₄ = A[]𝒢₁} i𝒢₁ i[]𝒢₁) 
      (vs^ {A𝒢₂ = A𝒢₂} i𝒢₂ i[wk]) i𝒢₃ u𝒢
  using A[]𝒢s₁ ← wk^T^^ (δ ^^ _)
                        {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]}
                        A[]𝒢₁ A𝒢₃
      | i[]𝒢s ← wk^^^ {t = i[]} (δ ^^ _)
                      {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                      {A𝒢₃ = πA𝒢₁ A[]𝒢s₁} {A𝒢₄ = πA𝒢₂ A[]𝒢s₁}
                      i[]𝒢₁ i𝒢₃
      | A𝒢′    ← ^<>T^^ δ {Ξ𝒢₁ = Ξ𝒢₁} {Ξ𝒢₂ = Ξ𝒢₂} {Ξ𝒢₃ = Ξ𝒢₃} {Ξ𝒢₄ = Ξ𝒢₄}  
                        A𝒢₁ A𝒢₂ (A[]𝒢s₁ .πA𝒢₁) u𝒢
      | i𝒢′    ← ^<>^^ {t = i} δ 
                       {Ξ𝒢₁ = Ξ𝒢₁} {Ξ𝒢₂ = Ξ𝒢₂} {Ξ𝒢₃ = Ξ𝒢₃} {Ξ𝒢₄ = Ξ𝒢₄}  
                       {A𝒢₄ = A𝒢′}
                       i𝒢₁ i𝒢₂ (i[]𝒢s .πt𝒢₁) u𝒢
  = vs^ i𝒢′ (i[]𝒢s .πt𝒢₂)
