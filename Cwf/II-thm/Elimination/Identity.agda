{-
Paper: section 6

Identity type structure part of the eliminator construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S

open import StrictLib hiding (_∘_;id)

import InitialAlg.Eliminators as IA
open import InitialAlg.Eliminators using (Conᶜ; Tmᶜ; Subᶜ; Tyᶜ)

import ADS as ADS
open import ADS using (Conʳ; Tyʳ ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ)

module Elimination.Identity (Ω : S.Con)(ω : Conʳ Ω .ᴰ (Conᶜ Ω Ω S.id)) where

open import Elimination.CwF Ω ω
open import Elimination.ElU Ω ω

-- Identity
--------------------------------------------------------------------------------

Id : {Γ : S.Con} {Γᴹ : Con Γ} {a : S.Tm Γ (S.U {Γ})} (aᴹ : Tm {Γ} Γᴹ
     {S.U {Γ}} (U {Γ} {Γᴹ}) a) {t : S.Tm Γ (S.El {Γ} a)} → Tm {Γ} Γᴹ
     {S.El {Γ} a} (El {Γ} {Γᴹ} {a} aᴹ) t → {u : S.Tm Γ (S.El {Γ} a)}
     → Tm {Γ} Γᴹ {S.El {Γ} a} (El {Γ} {Γᴹ} {a} aᴹ) u → Ty {Γ} Γᴹ
     (S.Id {Γ} a t u)
Id {Γ}{Γᴹ}{a} aᴹ {t} tᴹ {u} uᴹ ν _ = tt

-- Agda can't really typecheck the following (but they are trivial)

-- Id[] : holds by ⊤ propositionality
-- Reflect : holds by UIP
