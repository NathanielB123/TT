{-# OPTIONS --prop --show-irrelevant --rewriting #-}

open import Utils
open import Utils.IdExtras
open import Common.Sort
open import Common.SortEq

open import RelSSub.Syntax
open import RelSSub.SubUniq
open import RelSSub.Laws1

module RelSSub.Laws2 where

wk^T  : A [ wk ]T≔ A[]₁ → A [ δ ]T≔ A[]₂
      → A[]₁ [ δ ^ B𝒢 ]T≔ A[][]
      → A[]₂ [ wk ]T≔ A[][]

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

open wk^TOut
open wk^Out

open ^wkTOut
open ^wkOut

wk^T^^ : ∀ (δ : Sub[ r ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]₁} 
           {Ξ𝒢₂ : Ξ[]₁ [  δ ^ B𝒢 ]Ts≔ Ξ[][]} 
           {Ξ𝒢₃ : Ξ [ δ ]Ts≔ Ξ[]₂} 
           {Ξ𝒢₄ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
       → A [ wk ^^ Ξ𝒢₁ ]T≔ A[] 
       → A[] [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ]T≔ A[][]
       → wk^TOut δ A A[][] Ξ𝒢₃ Ξ𝒢₄

wk^^^ : ∀ (δ : Sub[ r ] Δ Γ) {B𝒢}
          {Ξ𝒢₁ : Ξ [ wk ]Ts≔ Ξ[]₁} 
          {Ξ𝒢₂ : Ξ[]₁ [  δ ^ B𝒢 ]Ts≔ Ξ[][]} 
          {Ξ𝒢₃ : Ξ [ δ ]Ts≔ Ξ[]₂} 
          {Ξ𝒢₄ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
          {A𝒢₁ A𝒢₂ A[]′ A𝒢₃ A𝒢₄}
       → _[_]_≔_ {q = q} t (wk ^^ Ξ𝒢₁) A𝒢₁ t[] 
       → t[] [ (δ ^ B𝒢) ^^ Ξ𝒢₂ ] A𝒢₂ ≔ t[][]
       → wk^Out δ t t[][] Ξ𝒢₃ Ξ𝒢₄ 
                (record {πA[] = A[]′ ; πA𝒢₁ = A𝒢₃ ; πA𝒢₂ = A𝒢₄})

^wkT^^ : r ≡ V 
       → ∀ (δ : Sub[ r ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ δ ]Ts≔ Ξ[]₂}
           {Ξ𝒢₂ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
           {Ξ𝒢₃ : Ξ [ wk ]Ts≔ Ξ[]₁} 
           {Ξ𝒢₄ : Ξ[]₁ [ δ ^ B𝒢 ]Ts≔ Ξ[][]} 
       → A [ δ ^^ Ξ𝒢₁ ]T≔ A[]
       → A[] [ wk ^^ Ξ𝒢₂ ]T≔ A[][]
       → ^wkTOut δ B𝒢 A A[][] Ξ𝒢₃ Ξ𝒢₄

^wk^^  : (p : r ≡ V)
       → ∀ (δ : Sub[ r ] Δ Γ) {B𝒢}
           {Ξ𝒢₁ : Ξ [ δ ]Ts≔ Ξ[]₂}
           {Ξ𝒢₂ : Ξ[]₂ [ wk ]Ts≔ Ξ[][]}
           {Ξ𝒢₃ : Ξ [ wk ]Ts≔ Ξ[]₁} 
           {Ξ𝒢₄ : Ξ[]₁ [ δ ^ B𝒢 ]Ts≔ Ξ[][]} 
           {A𝒢₁ A𝒢₂ A[]′ A𝒢₃ A𝒢₄}
       → _[_]_≔_ {q = q} t (δ ^^ Ξ𝒢₁) A𝒢₁ t[]
       → t[] [ wk ^^ Ξ𝒢₂ ] A𝒢₂ ≔ t[][]
       → ^wkOut δ B𝒢 t t[][] Ξ𝒢₃ Ξ𝒢₄ 
                (record {πA[] = A[]′ ; πA𝒢₁ = A𝒢₃ ; πA𝒢₂ = A𝒢₄})

wk^T^^ δ U[] U[] = record { πA𝒢₁ = U[] ; πA𝒢₂ = U[] }
wk^T^^ δ (El[] t𝒢₁) (El[] t𝒢₂) 
  = record { πA𝒢₁ = El[] (t𝒢s .πt𝒢₁) ; πA𝒢₂ = El[] (t𝒢s .πt𝒢₂) }
  where t𝒢s = wk^^^ δ t𝒢₁ t𝒢₂
wk^T^^ δ (Π[] A𝒢₁ B𝒢₁) (Π[] A𝒢₂ B𝒢₂) 
  = record { πA𝒢₁ = Π[] (A𝒢s .πA𝒢₁) (B𝒢s .πA𝒢₁)
           ; πA𝒢₂ = Π[] (A𝒢s .πA𝒢₂) (B𝒢s .πA𝒢₂)
           }
  where A𝒢s = wk^T^^ δ A𝒢₁ A𝒢₂
        B𝒢s = wk^T^^ δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                       {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _}
                       B𝒢₁ B𝒢₂

^wkT^^ p δ U[] U[] = record { πA𝒢₁ = U[] ; πA𝒢₂ = U[] }
^wkT^^ p δ (El[] t𝒢₁) (El[] t𝒢₂) 
  = record { πA𝒢₁ = El[] (t𝒢s .πt𝒢₁) ; πA𝒢₂ = El[] (t𝒢s .πt𝒢₂) }
  where t𝒢s = ^wk^^ p δ t𝒢₁ t𝒢₂
^wkT^^ p δ (Π[] A𝒢₁ B𝒢₁) (Π[] A𝒢₂ B𝒢₂) 
  = record { πA𝒢₁ = Π[] (A𝒢s .πA𝒢₁) (B𝒢s .πA𝒢₁)
           ; πA𝒢₂ = Π[] (A𝒢s .πA𝒢₂) (B𝒢s .πA𝒢₂)
           }
  where A𝒢s = ^wkT^^ p δ A𝒢₁ A𝒢₂
        B𝒢s = ^wkT^^ p δ 
                     {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                     {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _}
                     B𝒢₁ B𝒢₂

coh[]≔-lhs : ∀ (A≡ : A[]₁ ≡ᴾ A[]₂)
        → t [ δ ] A𝒢₁ ≔ t[]
        → t [ δ ] A𝒢₂ ≔ coeTm A≡ t[]
coh[]≔-lhs {A𝒢₁ = A𝒢₁} {A𝒢₂ = A𝒢₂} A≡ t𝒢
  with refl ← ≡↑ A≡
  with refl ← ≡↑ (u[]Tp A𝒢₁ A𝒢₂)
  = t𝒢

coh[]≔-rhs : ∀ (A≡ : A₁ ≡ᴾ A₂)
            → t [ δ ] A𝒢₁ ≔ t[]
            → coeTm A≡ t [ δ ] A𝒢₂ ≔ t[]
coh[]≔-rhs {A𝒢₁ = A𝒢₁} {A𝒢₂ = A𝒢₂} A≡ t𝒢
  with refl ← ≡↑ A≡
  with refl ← ≡↑ (u[]Tp A𝒢₁ A𝒢₂)
  = t𝒢

wk^^^ {q = T} δ (`[] i𝒢₁) (`[] i𝒢₂)
  = record { πt𝒢₁ = `[] (i𝒢s .πt𝒢₁)  ; πt𝒢₂ = tm⊑[] (i𝒢s .πt𝒢₂) }
  where i𝒢s = wk^^^ δ i𝒢₁ i𝒢₂
wk^^^ {q = T} δ {A𝒢₃ = Π[] _ _} {A𝒢₄ = Π[] _ _} 
      (lam[] {A𝒢 = A𝒢₁} t𝒢₁) (lam[] {A𝒢 = A𝒢₂} t𝒢₂)
  = record { πt𝒢₁ = lam[] (t𝒢s .πt𝒢₁)  ; πt𝒢₂ = lam[] (t𝒢s .πt𝒢₂) }
  where t𝒢s = wk^^^ δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                      {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _} 
                    t𝒢₁ t𝒢₂
wk^^^ {q = T} δ (app[] {A𝒢 = A𝒢₁} {B𝒢₂ = B𝒢₁} t𝒢₁ u𝒢₁) 
      (app[] {A𝒢 = A𝒢₂} {B𝒢₂ = B𝒢₂} t𝒢₂ u𝒢₂) 
  = record { πt𝒢₁ = app[] {B𝒢₂ = B𝒢s .πA𝒢₁} {B𝒢₄ = {!B𝒢s .πA𝒢₂!}} 
                          (t𝒢s .πt𝒢₁) (u𝒢s .πt𝒢₁)  
           ; πt𝒢₂ = app[] {B𝒢₂ = B𝒢s .πA𝒢₂} (t𝒢s .πt𝒢₂) (u𝒢s .πt𝒢₂)  }
    where A𝒢s = wk^T^^ δ A𝒢₁ A𝒢₂
          B𝒢s = wk^T^^ δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                         {Ξ𝒢₃ = ▷[] _ (A𝒢s .πA𝒢₁)} {Ξ𝒢₄ = ▷[] _ (A𝒢s .πA𝒢₂)}
                         B𝒢₁ B𝒢₂
          t𝒢s = wk^^^ δ t𝒢₁ t𝒢₂
          u𝒢s = wk^^^ δ u𝒢₁ u𝒢₂
wk^^^ {q = V} δ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]}
      {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
      i[wk] (vs^ {A𝒢₂ = A𝒢₃′} {A𝒢₄ = A𝒢₄′} i𝒢₂ i[]𝒢₂)
  with refl ← ≡↑ ([]T-uniq A𝒢₃ A𝒢₃′)
  with refl ← ≡↑ (u[]Tp A𝒢₃ A𝒢₃′)
     | refl ← ≡↑ (u[]Tp A𝒢₄ A𝒢₄′)
  = record { πt𝒢₁ = i𝒢₂ ; πt𝒢₂ = i[]𝒢₂ }
wk^^^ {q = V} δ
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
      {Ξ𝒢₃ = ▷[] Ξ𝒢₃ A𝒢₂} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _} 
      {A𝒢₃ = A𝒢₃}
  (vz^ {A𝒢₁ = A𝒢₁}) vz^ 
  = record { πt𝒢₁ = vz^ {A𝒢₄ = coe[]T-lhs Acoh (πA𝒢₂ A𝒢s)} ; πt𝒢₂ = tm⊑[] vz^ }
  where A𝒢s = wk^T^^ (δ ^^ Ξ𝒢₃) 
                     {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                     A𝒢₁ A𝒢₃
        Acoh = []T-uniq (πA𝒢₁ A𝒢s) A𝒢₂
wk^^^ {q = V}
  {t = vs i A𝒢} {t[] = vs i[] _} δ
  {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
  {Ξ𝒢₃ = ▷[] Ξ𝒢₃ _} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _}
  {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
  (vs^ {A𝒢₂ = A𝒢₁} i𝒢₁ i[wk]) (vs^ {A𝒢₂ = A𝒢₂} {A𝒢₄ = A[]𝒢₂} i𝒢₂ i[]𝒢₂) 
  = record { πt𝒢₁ = vs^ {A𝒢₄ = coe[]T-lhs A[]coh (πA𝒢₂ A[]𝒢s′)} 
                        (i[]𝒢s .πt𝒢₁) (coh[]≔-lhs Acoh (i𝒢s .πt𝒢₁)) 
           ; πt𝒢₂ = coh[]≔-rhs Acoh (i𝒢s .πt𝒢₂) }
  where A[]𝒢s = wk^T^^ δ {Ξ𝒢₁ = Ξ𝒢₁} {Ξ𝒢₂ = Ξ𝒢₂} {Ξ𝒢₃ = Ξ𝒢₃} {Ξ𝒢₄ = Ξ𝒢₄}
                       A𝒢₁ A𝒢₂
        i[]𝒢s = wk^^^ δ {Ξ𝒢₁ = Ξ𝒢₁} {Ξ𝒢₂ = Ξ𝒢₂} {Ξ𝒢₃ = Ξ𝒢₃} {Ξ𝒢₄ = Ξ𝒢₄} 
                      {A𝒢₃ = A[]𝒢s .πA𝒢₁} {A𝒢₄ = A[]𝒢s .πA𝒢₂}
                      i𝒢₁ i𝒢₂
        A𝒢s   = ^wkT^^ refl (wk ^^ Ξ𝒢₄)
                       {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                       (A[]𝒢s .πA𝒢₂) A[]𝒢₂
        i𝒢s   = ^wk^^ {t = i[]𝒢s .πt[]} refl (wk ^^ Ξ𝒢₄)
                      {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                      {A𝒢₃ = πA𝒢₁ A𝒢s} {A𝒢₄ = πA𝒢₂ A𝒢s}
                      (i[]𝒢s .πt𝒢₂) i[]𝒢₂
        A[]𝒢s′ = wk^T^^ (δ ^^ Ξ𝒢₃)
                        {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                        A𝒢 A𝒢₃
        A[]coh = []T-uniq (πA𝒢₁ A[]𝒢s′) (πA𝒢₁ A[]𝒢s)
        Acoh = []T-uniq (A𝒢s .πA𝒢₁) (coe[]T-lhs A[]coh (πA𝒢₂ A[]𝒢s′))

^wk^^ {q = T} refl δ (`[] i𝒢₁) (`[] i𝒢₂) 
  = record { πt𝒢₁ = `[] (i𝒢s .πt𝒢₁)  ; πt𝒢₂ = `[] (i𝒢s .πt𝒢₂) }
  where i𝒢s = ^wk^^ refl δ i𝒢₁ i𝒢₂
^wk^^ {q = T} p δ {A𝒢₃ = Π[] _ _} {A𝒢₄ = Π[] _ _}
      (lam[] {A𝒢 = A𝒢₁} t𝒢₁) (lam[] {A𝒢 = A𝒢₂} t𝒢₂)
  = record { πt𝒢₁ = lam[] (t𝒢s .πt𝒢₁)  ; πt𝒢₂ = lam[] (t𝒢s .πt𝒢₂) }
  where t𝒢s = ^wk^^ p δ
                    {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                    {Ξ𝒢₃ = ▷[] _ _} {Ξ𝒢₄ = ▷[] _ _} 
                    t𝒢₁ t𝒢₂
^wk^^ {q = T} p δ
      (app[] {A𝒢 = A𝒢₁} {B𝒢₂ = B𝒢₁} t𝒢₁ u𝒢₁) 
      (app[] {A𝒢 = A𝒢₂} {B𝒢₂ = B𝒢₂} t𝒢₂ u𝒢₂) 
  = record { πt𝒢₁ = app[] {B𝒢₂ = B𝒢s .πA𝒢₁} {B𝒢₄ = {!!}} 
                          (t𝒢s .πt𝒢₁) (u𝒢s .πt𝒢₁)  
           ; πt𝒢₂ = app[] {B𝒢₂ = B𝒢s .πA𝒢₂} (t𝒢s .πt𝒢₂) (u𝒢s .πt𝒢₂)  }
  where A𝒢s = ^wkT^^ p δ A𝒢₁ A𝒢₂
        B𝒢s = ^wkT^^ p δ {Ξ𝒢₁ = ▷[] _ _} {Ξ𝒢₂ = ▷[] _ _} 
                     {Ξ𝒢₃ = ▷[] _ (A𝒢s .πA𝒢₁)} {Ξ𝒢₄ = ▷[] _ (A𝒢s .πA𝒢₂)}
                     B𝒢₁ B𝒢₂
        t𝒢s = ^wk^^ p δ t𝒢₁ t𝒢₂
        u𝒢s = ^wk^^ p δ u𝒢₁ u𝒢₂
^wk^^ {q = V} p δ {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} {A𝒢₂ = A𝒢₂}
      i𝒢₁ i𝒢₂
  = record { πt𝒢₁ = i[wk] ; πt𝒢₂ = vs^ i𝒢₁ i𝒢₂ }

^wk^^ {q = V} p δ
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
      {Ξ𝒢₃ = ▷[] Ξ𝒢₃ A𝒢₂} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _} 
      {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
  (vz^ {A𝒢₁ = A𝒢₁} {A𝒢₂ = wah} {A𝒢₃ = bah}) vz^ 
  = record { πt𝒢₁ = vz^ {A𝒢₄ = coe[]T-lhs Acoh (πA𝒢₂ A𝒢s)} ; πt𝒢₂ = vz^ }
  where A𝒢s = wk^T^^ (wk ^^ _)
                     {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                     A𝒢₁ A𝒢₃
        Acoh = []T-uniq (πA𝒢₁ A𝒢s) A𝒢₂
^wk^^ {q = V} {t = vs i A𝒢} {t[] = vs i[] A[]𝒢} p δ
      {Ξ𝒢₁ = ▷[] Ξ𝒢₁ _} {Ξ𝒢₂ = ▷[] Ξ𝒢₂ _} 
      {Ξ𝒢₃ = ▷[] Ξ𝒢₃ _} {Ξ𝒢₄ = ▷[] Ξ𝒢₄ _} 
      {A𝒢₃ = A𝒢₃} {A𝒢₄ = A𝒢₄}
      (vs^ {A𝒢₂ = A𝒢₁} i𝒢₁ i[wk]) 
      (vs^ {A𝒢₂ = A𝒢₂} i𝒢₂ i[wk])
  = record { πt𝒢₁ = vs^ {A𝒢₄ = coe[]T-lhs Acoh (πA𝒢₂ A[]𝒢s)} (i𝒢s .πt𝒢₁) i[wk] 
           ; πt𝒢₂ = vs^ (i𝒢s .πt𝒢₂) i[wk] }
    where A𝒢s = ^wkT^^ p δ A𝒢₁ A𝒢₂
          i𝒢s = ^wk^^ p δ {A𝒢₃ = A𝒢s .πA𝒢₁} {A𝒢₄ = A𝒢s .πA𝒢₂} i𝒢₁ i𝒢₂
          A[]𝒢s = wk^T^^ (wk ^^ _) 
                         {Ξ𝒢₁ = •[]} {Ξ𝒢₂ = •[]} {Ξ𝒢₃ = •[]} {Ξ𝒢₄ = •[]} 
                         A𝒢 A𝒢₃
          Acoh = []T-uniq (πA𝒢₁ A[]𝒢s) (πA𝒢₁ A𝒢s)

wk^T {δ = δ} A𝒢₁ A𝒢₂ A𝒢₃ 
  using A𝒢s ← wk^T^^ δ {Ξ𝒢₂ = •[]} {Ξ𝒢₄ = •[]} A𝒢₁ A𝒢₃
  with refl ← ≡↑ ([]T-uniq A𝒢₂ (A𝒢s .πA𝒢₁))
  with refl ← ≡↑ (u[]Tp A𝒢₂ (A𝒢s .πA𝒢₁))
  = A𝒢s .πA𝒢₂
