
open import Level 
open import monlib
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import Syntax
open import ModelRecord
open import SyntaxIsRecord


module SyntaxIsRecord2   where

module S1 = Model1 syntax1


syntax2 : ModelRecord.Model2  syntax1
syntax2 = record
       { lift-wkT = λ A B Ex → Subtype=-out (_ , (λ a → it)) ( comm-liftT _ _)
       ; liftU = λ Δ E → refl
       ; liftEl = λ Δ E a → refl
       ; liftΠ = λ Δ E A B → refl
       ; liftV0 = λ Γ Δ A Ex →
        ↓-Subtype-in (λ a → _ , (λ b → it))
          (↓-cst-in refl)
        ; lift-wkt = λ Δ A B Ex t →
          ↓-Subtype-in (λ a → _ , (λ b → it))
          (↓-cst-in (comm-liftt _ _))
       ; l-subU = λ Ex Δ t → refl
       ; l-subEl = λ Ex Δ t u → refl
       ; l-subΠ = λ Ex Δ t A B → refl
       ; lift-subT = λ Δ Ex A B t → Subtype=-out (_ , (λ a → it))
         (lift-subT _ _ _)
        ; lift-app = λ Δ Ex A B t u →
          ↓-Subtype-in (λ a → _ , (λ b → it)) (↓-cst-in refl)
       ; l-subT-subT = λ E Δ z A a B →
          Subtype=-out (_ , (λ a₁ → it))
          (l-subT-subT  _ _ _ _)
       ; sub-app = λ E Δ z A B t u → 
          ↓-Subtype-in (λ a → _ , (λ b → it)) (↓-cst-in refl)
       
       ; l-subT-wkT = λ z A C → Subtype=-out (_ , (λ a → it))
          (l-subT-wkT _ _ _)
      ; l-subt-wkt = λ z t C →
          ↓-Subtype-in (λ a → _ , (λ b → it)) (↓-cst-in ( l-subt-wkt _ (₁ z) (₁ t) ))
       ; subT-wkT = λ z A → Subtype=-out (_ , (λ a → it))
         (subT-wkT _ _)
        ; subt-wkt = λ z t → ↓-Subtype-in (λ a → _ , (λ b → it)) (↓-cst-in (n-subt-wkt _ _ _))
       ; subt-v0 =
        λ z → ↓-Subtype-in (λ a → _ , (λ b → it)) (↓-cst-in refl)
        ; Sn-subt-v0 = λ z A → ↓-Subtype-in (λ a → _ , (λ b → it)) (↓-cst-in refl)
       }
