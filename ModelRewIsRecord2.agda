{-# OPTIONS  --rewriting #-}
-- The model with rewrite rules is a model in the sense of ModelRecord

open import Level 
open import monlib
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import Model
open import ModelRecord
open import ModelRewIsRecord


module ModelRewIsRecord2 {l}  where

-- the model with rew rules
module M1 = Model1 (m1 {l})


m2 : ModelRecord.Model2 {l} m1
m2 =  record
        { lift-wkT = M.lift-wkT
        ; liftU = λ _ _ → refl
        ; liftEl = λ Δ E a → refl
        ; liftΠ = λ Δ E A B → refl
        ; liftV0 = M.liftV0 
        ; lift-wkt = M.lift-wkt
        ; l-subU = λ Ex Δ t → refl
        ; l-subEl = λ Ex Δ t u → refl
        ; l-subΠ = λ Ex Δ t A B → refl
        ; lift-subT = M.lift-subT
        ; lift-app = M.lift-app
        ; l-subT-subT = M.l-subT-subT
        ; sub-app = M.sub-app
        ; l-subT-wkT = M.l-subT-wkT
        ; l-subt-wkt = M.l-subt-wkt
        ; subT-wkT = M.subT-wkT
        ; subt-wkt = M.subt-wkt
        ; subt-v0 = M.subt-v0
        ; Sn-subt-v0 = M.Sn-subt-v0
        }
