{-
Paper: section 6

CwF part of the eliminator construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S

open import StrictLib hiding (_∘_;id)

import InitialAlg.Eliminators as IA
open import InitialAlg.Eliminators using (Conᶜ; Tmᶜ; Subᶜ; Tyᶜ)

import ADS as ADS
open import ADS using (Conʳ; Tyʳ ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ)

module Elimination.CwF (Ω : S.Con)(ω : Conʳ Ω .ᴰ (Conᶜ Ω Ω S.id)) where

con : Conʳ Ω .ᴬ
con = Conᶜ Ω Ω S.id

--------------------------------------------------------------------------------

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 4 _▶_

i : Level
i = zero
j : Level
j = zero

Con : S.Con → Set i
Con Γ = (ν : S.Sub Ω Γ) → ˢ (Conʳ Γ) _ (ᴰ (Subʳ ν) _ ω)

Ty  : ∀ {Γ} → Con Γ → S.Ty Γ → Set j
Ty {Γ} Γᴱ A = (ν : S.Sub Ω Γ)(t : S.Tm Ω (A S.[ ν ]T))
              → ˢ (Tyʳ A) _ _ (Γᴱ ν) _ (ᴰ (Tmʳ t) _ ω)

Tm  : ∀ {Γ}(Γᴱ : Con Γ){A}(Aᴱ : Ty {Γ} Γᴱ A) → S.Tm Γ A → Set j
Tm {Γ} Γᴱ {A} Aᴱ t = (ν : S.Sub Ω Γ) → Aᴱ ν (t S.[ ν ]t) ≡ ˢ (Tmʳ t) _ _ (Γᴱ ν)

Sub : ∀ {Γ} → Con Γ → ∀ {Δ} → Con Δ → S.Sub Γ Δ → Set j
Sub {Γ} Γᴱ {Δ} Δᴱ σ = (ν : S.Sub Ω Γ) → Δᴱ (σ S.∘ ν) ≡ ˢ (Subʳ σ) _ _ (Γᴱ ν)

∙  : Con S.∙
∙ ν = lift tt

_▶_   : ∀ {Γ}(Γᴱ : Con Γ){A} → Ty {Γ} Γᴱ A → Con (Γ S.▶ A)
_▶_ {Γ} Γᴱ {A} Aᴱ ν = Γᴱ (S.π₁ ν) , Aᴱ (S.π₁ ν) (S.π₂ ν)

_[_]T : ∀ {Γ}{Γᴱ : Con Γ}{Δ}{Δᴱ : Con Δ}{A}(Aᴱ : Ty Δᴱ A)
          {σ}(σᴱ : Sub Γᴱ Δᴱ σ) → Ty Γᴱ (A S.[ σ ]T)
_[_]T {Γ}{Γᴱ}{Δ}{Δᴱ}{A} Aᴱ {σ} σᴱ ν t =
  coe ((λ x → ˢ (Tyʳ A) _ _ x _ (ᴰ (Tmʳ t) (Conᶜ Ω Ω S.id) ω)) & σᴱ ν)
      (Aᴱ (σ S.∘ ν) t)

id : ∀{Γ}{Γᴱ : Con Γ} → Sub Γᴱ Γᴱ S.id
id {Γ}{Γᴱ} ν = refl

_∘_   : ∀ {Γ}{Γᴱ : Con Γ}{Δ}{Δᴱ : Con Δ}{Σ}{Σᴱ : Con Σ}
          {σ}(σᴱ : Sub Δᴱ Σᴱ σ){δ}(δᴱ : Sub Γᴱ Δᴱ δ ) → Sub Γᴱ Σᴱ (σ S.∘ δ)
_∘_ {Γ}{Γᴱ}{Δ}{Δᴱ}{Σ}{Σᴱ}{σ} σᴱ {δ} δᴱ ν =
  σᴱ (δ S.∘ ν) ◾ (ˢ (Subʳ σ) _ _) & δᴱ ν

ε : ∀{Γ}{Γᴱ : Con Γ} → Sub Γᴱ ∙ S.ε
ε {Γ}{Γᴱ} _ = refl

_,s_ : {Γ : S.Con} {Γᴹ : Con Γ} {Δ : S.Con} {Δᴹ : Con Δ} {σ : S.Sub Γ Δ}
       (σᴹ : Sub {Γ} Γᴹ {Δ} Δᴹ σ) {A : S.Ty Δ} {Aᴹ : Ty {Δ} Δᴹ A}
       {t : S.Tm Γ (S._[_]T {Γ} {Δ} A σ)} →
       Tm {Γ} Γᴹ {S._[_]T {Γ} {Δ} A σ}
       (_[_]T {Γ} {Γᴹ} {Δ} {Δᴹ} {A} Aᴹ {σ} σᴹ) t →
       Sub {Γ} Γᴹ {Δ S.▶ A} (_▶_ {Δ} Δᴹ {A} Aᴹ) (S._,s_ {Γ} {Δ} σ {A} t)
_,s_ {Γ}{Γᴱ}{Δ}{Δᴱ} {σ} σᴱ {A}{Aᴱ} {t} tᴱ ν = ,≡ (σᴱ ν) (tᴱ ν)

π₁ : {Γ : S.Con} {Γᴱ : Con Γ} {Δ : S.Con} {Δᴱ : Con Δ} {A : S.Ty Δ}
     {Aᴱ : Ty {Δ} Δᴱ A} {σ : S.Sub Γ (Δ S.▶ A)} →
     Sub {Γ} Γᴱ {Δ S.▶ A} (_▶_ {Δ} Δᴱ {A} Aᴱ) σ →
     Sub {Γ} Γᴱ {Δ} Δᴱ (S.π₁ {Γ} {Δ} {A} σ)
π₁ {Γ}{Γᴱ}{Δ}{Δᴱ} {A}{Aᴱ}{σ} σᴱ ν = ₁ & σᴱ ν

_[_]t :
        {Γ : S.Con} {Γᴱ : Con Γ} {Δ : S.Con} {Δᴱ : Con Δ} {A : S.Ty Δ}
        {Aᴱ : Ty {Δ} Δᴱ A} {t : S.Tm Δ A} →
        Tm {Δ} Δᴱ {A} Aᴱ t →
        {σ : S.Sub Γ Δ} (σᴱ : Sub {Γ} Γᴱ {Δ} Δᴱ σ) →
        Tm {Γ} Γᴱ {S._[_]T {Γ} {Δ} A σ}
        (_[_]T {Γ} {Γᴱ} {Δ} {Δᴱ} {A} Aᴱ {σ} σᴱ) (S._[_]t {Γ} {Δ} {A} t σ)
_[_]t {Γ}{Γᴱ}{Δ}{Δᴱ} {A}{Aᴱ} {t} tᴱ {σ} σᴱ ν =
    (coe
      ((λ x →
          ˢ (Tyʳ A) _ _
          x _
          (ᴰ (Tmʳ t) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)))
           (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id))
            (ᴰ (Subʳ ν) (Conᶜ Ω Ω S.id) ω))))
       & σᴱ ν)) & tᴱ (σ S.∘ ν)
  ◾ apd (ˢ (Tmʳ t) _ _) (σᴱ ν)

π₂ :
        {Γ : S.Con} {Γᴱ : Con Γ} {Δ : S.Con} {Δᴱ : Con Δ} {A : S.Ty Δ}
        {Aᴱ : Ty {Δ} Δᴱ A} {σ : S.Sub Γ (Δ S.▶ A)}
        (σᴱ : Sub {Γ} Γᴱ {Δ S.▶ A} (_▶_ {Δ} Δᴱ {A} Aᴱ) σ) →
        Tm {Γ} Γᴱ {S._[_]T {Γ} {Δ} A (S.π₁ {Γ} {Δ} {A} σ)}
        (_[_]T {Γ} {Γᴱ} {Δ} {Δᴱ} {A} Aᴱ {S.π₁ {Γ} {Δ} {A} σ}
         (π₁ {Γ} {Γᴱ} {Δ} {Δᴱ} {A} {Aᴱ} {σ} σᴱ))
        (S.π₂ {Γ} {Δ} {A} σ)
π₂ {Γ}{Γᴱ}{Δ}{Δᴱ} {A}{Aᴱ}{σ} σᴱ ν =
  coe-coe _ _ (Aᴱ (S.π₁ (σ S.∘ ν)) (S.π₂ (σ S.∘ ν))) ◾ apd ₂ (σᴱ ν)

[id]T : {Γ : S.Con} {Γᴱ : Con Γ} {A : S.Ty Γ} {Aᴱ : Ty {Γ} Γᴱ A} →
        _≡_ {j} {Ty {Γ} Γᴱ A}
        (_[_]T {Γ} {Γᴱ} {Γ} {Γᴱ} {A} Aᴱ {S.id {Γ}} (id {Γ} {Γᴱ})) Aᴱ
[id]T {Γ}{Γᴱ}{A}{Aᴱ} = refl

[][]T : {Γ : S.Con} {Γᴱ : Con Γ} {Δ : S.Con} {Δᴱ : Con Δ} {Σ₁ : S.Con}
        {Σᴱ : Con Σ₁} {A : S.Ty Σ₁} {Aᴱ : Ty {Σ₁} Σᴱ A} {σ : S.Sub Γ Δ}
        {σᴱ : Sub {Γ} Γᴱ {Δ} Δᴱ σ} {δ : S.Sub Δ Σ₁}
        {δᴱ : Sub {Δ} Δᴱ {Σ₁} Σᴱ δ} →
        _≡_ {j} {Ty {Γ} Γᴱ (S._[_]T {Γ} {Σ₁} A (S._∘_ {Γ} {Δ} {Σ₁} δ σ))}
        (_[_]T {Γ} {Γᴱ} {Δ} {Δᴱ} {S._[_]T {Δ} {Σ₁} A δ}
         (_[_]T {Δ} {Δᴱ} {Σ₁} {Σᴱ} {A} Aᴱ {δ} δᴱ) {σ} σᴱ)
        (_[_]T {Γ} {Γᴱ} {Σ₁} {Σᴱ} {A} Aᴱ {S._∘_ {Γ} {Δ} {Σ₁} δ σ}
         (_∘_ {Γ} {Γᴱ} {Δ} {Δᴱ} {Σ₁} {Σᴱ} {δ} δᴱ {σ} σᴱ))
[][]T {Γ}{Γᴱ}{Δ}{Δᴱ}{Σ}{Σᴱ}{A}{Aᴱ}{σ}{σᴱ}{δ}{δᴱ} =
  ext λ ν → ext λ t → uñ
    (uncoe
      ((λ x → ˢ (Tyʳ A) (ᴬ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id)))) (ᴰ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id))) (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν)
          (Conᶜ Ω Ω S.id) ω))) (ˢ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν)
          (Conᶜ Ω Ω S.id))) (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id))
          (ᴰ (Subʳ ν) (Conᶜ Ω Ω S.id) ω)) x) (ᴬ (Tmʳ t) (Conᶜ Ω Ω
          S.id)) (ᴰ (Tmʳ t) (Conᶜ Ω Ω S.id) ω)) & σᴱ ν) (coe ((λ x → ˢ
          (Tyʳ A) (ᴬ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id)))) (ᴰ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id))) (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν)
          (Conᶜ Ω Ω S.id) ω))) x (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id)) (ᴰ (Tmʳ
          t) (Conᶜ Ω Ω S.id) ω)) & δᴱ (σ S.∘ ν)) (Aᴱ (δ S.∘ (σ S.∘ ν))
          t))
   ◾̃ uncoe
      ((λ x → ˢ (Tyʳ A) (ᴬ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id)))) (ᴰ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id))) (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν)
          (Conᶜ Ω Ω S.id) ω))) x (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id)) (ᴰ (Tmʳ
          t) (Conᶜ Ω Ω S.id) ω)) & δᴱ (σ S.∘ ν)) (Aᴱ (δ S.∘ (σ S.∘ ν))
          t)
   ◾̃ uncoe
      ((λ x → ˢ (Tyʳ A) (ᴬ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id)))) (ᴰ (Subʳ δ) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id))) (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν)
          (Conᶜ Ω Ω S.id) ω))) x (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id)) (ᴰ (Tmʳ
          t) (Conᶜ Ω Ω S.id) ω)) & (δᴱ (σ S.∘ ν) ◾ ˢ (Subʳ δ) (ᴬ
          (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id))) (ᴰ (Subʳ σ) (ᴬ (Subʳ
          ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν) (Conᶜ Ω Ω S.id) ω)) & σᴱ ν))
          (Aᴱ (δ S.∘ (σ S.∘ ν)) t) ⁻¹̃
     )

-- Tm, Sub equalities all given by UIP
