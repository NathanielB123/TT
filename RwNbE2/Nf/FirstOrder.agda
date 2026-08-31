{-# OPTIONS --prop --rewriting #-}

open import RwNbE2.Nf.Raw

module RwNbE2.Nf.FirstOrder where

data FirstOrder {l} {n} : Nfᴿ l n → Set where
  ttFO : FirstOrder ttᴿ
  ffFO : FirstOrder ffᴿ

  zeFO : FirstOrder zeᴿ
  suFO : FirstOrder tᴿ → FirstOrder (suᴿ tᴿ)
  
  pairFO : FirstOrder tᴿ → FirstOrder uᴿ
         → FirstOrder (pairᴿ Bᴿ tᴿ uᴿ)
  
  rflFO : FirstOrder tᴿ → FirstOrder (rflᴿ tᴿ)

  ne𝔹FO  : FirstOrder (ne𝔹ᴿ tᴿ)
  neℕFO  : FirstOrder (neℕᴿ tᴿ)
  neIdFO : FirstOrder (neIFᴿ tᴿ Aᴿ Bᴿ uᴿ)
  neIFFO : FirstOrder (neIdᴿ t₁ᴿ t₂ᴿ uᴿ)
