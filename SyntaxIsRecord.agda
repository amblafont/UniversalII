{-# OPTIONS --rewriting #-}
-- a definition of model, without rewrite rules. It exactly follows the rewrite rule version.

open import Level 
open import monlib
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import Syntax
open import ModelRecord


module SyntaxIsRecord   where



syntax1 : ModelRecord.Model1 
syntax1 =  record
             { Con = Subtype (Conw , λ Γ → it )
             ; Telescope = λ Γ →  Subtype ((λ Δ → Conw ((₁ Γ) ^^ Δ)) , λ x → it)
             ; Ty = λ Γ →  Subtype (Tyw (₁ Γ) , λ x → it)
             ; Tm = λ Γ A → Subtype (Tmw (₁ Γ) (₁ A) , λ x → it )
             ; ∙ = _ , ∙w
             ; _▶_ = λ Γ A  → _ , ▶w (₂ Γ) (₂ A)
             ; _^^_ = λ Γ Δ  → (₁ Γ ^^ ₁ Δ) , ₂ Δ
             ; ∙t = λ Γ → Syntax.∙p , ₂ Γ
             ; _▶t_ = λ Δ A  → _ , ▶w (₂ Δ) (₂ A)
             ; ^^∙t = refl
             ; ^^▶t = refl
             ; U = λ Γ → _ , Uw _ (₂ Γ)
             ; El = λ Γ x → _ , Elw (₂ Γ)(₂ x)
             ; ΠΠ = λ Γ A B → _ , Πw (₂ Γ)(₂ A)(₂ B)
             ; wkC = λ Γ Ex Δ → _ , wkCw' (₂ Ex) _ (₂ Δ)
             ; wk∙t = refl
             ; liftT = λ Γ Δ Ex A → _ , liftTw (₂ Ex) (₁ Δ) (₂ A)
             ; liftt = λ Γ Δ Ex A t → _ , lifttw (₂ Ex) (₁ Δ) (₂ t)
             ; wk▶t = refl
             ; V0 = λ Γ A → _ , vw (V0w _ (₂ Γ) _ (₂ A))
             ; subTel = λ Ex Δ z → _ , subTelw (₂ z) (₂ Δ)
             ; sub∙t = refl
             ; l-subT = λ E Δ z A → _ , subTw (₂ z)(₂ A)
             ; sub▶t = refl
             ; l-subt = λ Ex Δ t A u → _ , subtw (₂ t)(₂ u)
             ; app = λ Γ A B t u → _ , appw _ (₂ Γ) _ (₂ A) _ (₂ B) _ (₂ t) _ (₂ u)
             }
