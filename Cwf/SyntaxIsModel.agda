


open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )

  hiding (_∘_ ; _⁻¹ ; Π ; _$_)



open import monlib hiding (tr2)



module SyntaxIsModel   where

open import ModelRecord
open import Syntax

-- Con = ∃ Conw

-- I defined it as a record rather than using Σ because otherwise
-- inferences may fail
record Con : Set  where
  constructor _,_
  field
    ₁ : Conp
    ₂ : Conw ₁
open Con public

record Ty (Γ : Con) : Set  where
  constructor _,_
  field
    ₁ : Typ
    ₂ : Tyw (Con.₁ Γ ) ₁

open Ty public

Ty= : ∀ {Γ}{A B : Ty Γ}(e : ₁ A ≡ ₁ B) → A ≡ B
Ty= {Γ} {A , Aw} {B} e rewrite e | prop-has-all-paths Aw (₂ B) = refl

record Tm (Γ : Con)(A : Ty Γ) : Set  where
  constructor _,_
  field
    ₁ : Tmp
    ₂ : Tmw (Con.₁ Γ ) (Ty.₁ A) ₁

open Tm public

Tm= : ∀ {Γ}{A}{t u : Tm Γ A}(e : ₁ t ≡ ₁ u) → t ≡ u
Tm= {Γ} {A}{t , tw} {u} e rewrite e | prop-has-all-paths tw (₂ u) = refl

Tm=↓ : ∀ {Γ}{A}{t : Tm Γ A}{B}{u : Tm Γ B}(eT : A ≡ B)(e : ₁ t ≡ ₁ u) →
   t == u [ Tm Γ ↓ eT ]

Tm=↓ {Γ} {A} {t}{.A}{u} refl = Tm= {u = u} 

record Sub (Γ : Con)(Δ : Con) : Set  where
  constructor _,_
  field
    ₁ : Subp
    ₂ : Subw (Con.₁ Γ )(Con.₁ Δ ) ₁

open Sub public

Sub= : ∀ {Γ}{Δ}{σ δ : Sub Γ Δ}(e : ₁ σ ≡ ₁ δ) → σ ≡ δ
Sub= {Γ}{Δ} {σ , σw} {δ} e rewrite e | prop-has-all-paths σw (₂ δ) = refl

open Sub public

syntaxCwF : CwF
syntaxCwF = record
              { Con = Con
              ; Ty = Ty
              ; Tm = Tm
              ; Sub = Sub
              ; ∙ = ∙p , ∙w
              ; _▶_ = λ Γ A → ((₁ Γ ▶p ₁ A ) , ▶w (₂ Γ) (₂ A))
              ; _[_]T = λ {Γ}{Δ}A σ → (_ , Tyw[] (₂ A)(₂ Γ)(₂ σ))
              ; id = λ {Γ} → _ , idpw (₂ Γ)
              ; _∘_ = λ {Γ}{Δ}{Y}σ δ → _ , ∘w (₂ σ)(₂ Γ)(₂ δ)
              ; ε = λ {Γ} → _ , nilw
              ; _,s_ = λ {Γ}{Δ}σ{A}t → (₁ t :: ₁ σ) , ,sw (₂ Δ) ((₂ σ)) (₂ A) (₂ t)
              ; π₁ = λ {Γ}{Δ}{A} →  λ { (_ , ,sw Δw σw Aw tw) → _ , σw }
              ; _[_]t = λ {Γ}{Δ}{A}t σ → _ , Tmw[](₂ t)(₂ Γ)(₂ σ)
              ; π₂ = λ {Γ}{Δ}{A} →  λ { (_ , ,sw Δw σw Aw tw) → _ , tw }

              ; [id]T = λ {Γ}{A}→ Ty= ([idp]T (₂ A))
              ; [][]T = λ {Γ}{Δ}{Y}{A}{σ}{δ} → Ty= (! ([∘]T _ _ _))
              ; idl = λ {Γ}{Δ}{σ} → Sub= (idl (₂ σ))
              ; idr = λ {Γ}{Δ}{σ} → Sub= {!!}
              ; ass = λ {Γ}{Δ}{Y}{O}{σ}{δ}{ν} → Sub= {!!}
              ; π₁,∘ = refl
              ; π₂,∘ = λ {Γ}{Δ}{Y}{δ}{σ}{A}{t} → Tm=↓ _ refl 
              ; π₁β = refl
              ; πη = λ {Γ}{Δ}{A} → λ { {_ , ,sw Δw σw Aw tw} → Sub= refl } 
              ; εη = λ {Γ} → (λ { {(_ , nilw)} → refl })
              ; π₂β = refl
              }


-- -}
