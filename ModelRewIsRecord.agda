{-# OPTIONS --rewriting #-}
-- The model with rewrite rules is a model in the sense of ModelRecord

open import Level 
open import monlib
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import Model
open import ModelRecord


module ModelRewIsRecord {l}  where

-- the model with rew rules
module M = Model {l}


m1 : ModelRecord.Model1 {_}
m1 =  record
       { Con = M.Con
       ; Telescope = M.Telescope
       ; Ty = M.Ty
       ; Tm = M.Tm
       ; ∙ = M.∙
       ; _▶_ = M._▶_
       ; _^^_ = M._^^_
       ; ∙t = M.∙t
       ; _▶t_ = M._▶t_
       ; ^^∙t = refl
       ; ^^▶t = refl
       ; U = M.U
       ; El = M.El
       ; ΠΠ = M.ΠΠ
       ; wkC = M.wkC
       ; wk∙t = refl
       ; liftT = M.liftT
       ; liftt = M.liftt
       ; wk▶t = refl
       ; V0 = M.V0
       ; subTel = M.subTel
       ; sub∙t = refl
       ; l-subT = M.l-subT
       ; sub▶t = refl
       ; l-subt = M.l-subt
       ; app = M.app
       }
      

