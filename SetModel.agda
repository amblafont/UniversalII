-- first part of the set model

open import Level 
open import monlib
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import ModelRecord
-- open import SetModelComponents


module SetModel {ℓ : Level}   where

-- inspired by DeepCME.agda

import SetModelComponents {ℓ} as S




set1 : ModelRecord.Model1 {lsucc (lsucc ℓ)}
set1 = record
         { Con =  S.Con 
         ; Telescope = S.Tel 
         ; Ty = S.Ty
         ; Tm = S.Tm
         ; ∙ = S.∙
         ; _▶_ = S._,_
         ; _^^_ = S._^^_
         ; ∙t = S.∙t
         ; _▶t_ = S._▶t_
         ; ^^∙t =  refl
         ; ^^▶t = refl
         ; U = λ Γ → S.U
         ; El = λ Γ → S.El
         ; ΠΠ = λ Γ → S.Π
         ; wkC = S.wkC
         ; wk∙t = refl
         ; liftT = S.liftT
         ; liftt = S.liftt
         ; wk▶t = refl
         ; V0 = S.V0
         ; subTel = S.subTel
         ; sub∙t = refl
         ; l-subT = S.l-subT
         ; sub▶t = refl
         ; l-subt = S.l-subt
         ; app = S.app'
         }
