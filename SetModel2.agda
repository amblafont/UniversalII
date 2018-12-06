-- amazing!!

open import Level 
open import monlib
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import ModelRecord
-- open import SetModelComponents


module SetModel2 {ℓ : Level}   where

-- inspired by DeepCME.agda

import SetModelComponents {ℓ} as S
open import SetModel {ℓ}




set2 : ModelRecord.Model2 set1
set2 = record
         { lift-wkT = λ A B Ex → refl

         ; liftU = λ Δ E → refl
         ; liftEl = λ Δ E a → refl
         ; liftΠ = λ Δ E A B → refl

         ; liftV0 = λ Γ Δ A Ex → refl
         ; lift-wkt = λ Δ A B Ex t → refl

         ; l-subU = λ Ex Δ t → refl
         ; l-subEl = λ Ex Δ t u → refl
         ; l-subΠ = λ Ex Δ t A B → refl

         ; lift-subT = λ Δ Ex A B t → refl
         ; lift-app = λ Δ Ex A B t u → refl
         ; l-subT-subT = λ E Δ z A a B → refl
         ; sub-app = λ E Δ z A B t u → refl
         ; l-subT-wkT = λ z A C → refl
         ; l-subt-wkt = λ z t C → refl
         ; subT-wkT = λ z A → refl
         ; subt-wkt = λ z t → refl
         ; subt-v0 = λ z → refl
         ; Sn-subt-v0 = λ z A → refl
         }
