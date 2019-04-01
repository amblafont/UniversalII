{-
Paper: section 4

CwF part of the initial algebra construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S
open import StrictLib hiding (id; _∘_)
import ADS as ADS
open import ADS using (Conʳ; Tyʳ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ; mkCon; mkTy; mkTm; mkSub)

module InitialAlg.CwF (Ω : S.Con) where

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 4 _▶_

i : Level
i = suc zero
j : Level
j = suc zero

Con : S.Con → Set i
Con Γ = (ν : S.Sub Ω Γ) → Conʳ Γ .ᴬ

Ty  : ∀ {Γ} → Con Γ → S.Ty Γ → Set j
Ty {Γ} Γᶜ A = (ν : S.Sub Ω Γ)(t : S.Tm Ω (A S.[ ν ]T)) → Tyʳ A .ᴬ (Γᶜ ν)

Tm  : ∀ {Γ}(Γᶜ : Con Γ){A}(Aᶜ : Ty {Γ} Γᶜ A) → S.Tm Γ A → Set j
Tm {Γ} Γᶜ {A} Aᶜ t = (ν : S.Sub Ω Γ) → Aᶜ ν (t S.[ ν ]t) ≡ Tmʳ t .ᴬ (Γᶜ ν)

Sub : ∀ {Γ} → Con Γ → ∀ {Δ} → Con Δ → S.Sub Γ Δ → Set j
Sub {Γ} Γᶜ {Δ} Δᶜ σ = (ν : S.Sub Ω Γ) → Δᶜ (σ S.∘ ν) ≡ Subʳ σ .ᴬ (Γᶜ ν)

∙ : Con S.∙
∙ = λ _ → lift tt

_▶_   : ∀ {Γ}(Γᶜ : Con Γ){A} → Ty {Γ} Γᶜ A → Con (Γ S.▶ A)
_▶_ {Γ} Γᶜ {A} Aᶜ = λ ν → (Γᶜ (S.π₁ ν)) , (Aᶜ (S.π₁ ν) (S.π₂ ν))

_[_]T : ∀ {Γ}{Γᶜ : Con Γ}{Δ}{Δᶜ : Con Δ}{A}(Aᶜ : Ty Δᶜ A)
          {σ}(σᶜ : Sub Γᶜ Δᶜ σ) → Ty Γᶜ (A S.[ σ ]T)
_[_]T {Γ}{Γᶜ}{Δ}{Δᶜ}{A} Aᶜ {σ} σᶜ ν t = tr (Tyʳ A .ᴬ) (σᶜ ν) (Aᶜ (σ S.∘ ν) t)

id : ∀{Γ}{Γᶜ : Con Γ} → Sub Γᶜ Γᶜ S.id
id {Γ} Γᶜ = refl

_∘_ : ∀ {Γ}{Γᶜ : Con Γ}{Δ}{Δᶜ : Con Δ}{Σ}{Σᶜ : Con Σ}
        {σ}(σᶜ : Sub Δᶜ Σᶜ σ){δ}(δᶜ : Sub Γᶜ Δᶜ δ ) → Sub Γᶜ Σᶜ (σ S.∘ δ)
_∘_ {Γ}{Γᶜ}{Δ}{Δᶜ}{Σ}{Σᶜ}{σ} σᶜ {δ} δᶜ ν = σᶜ (δ S.∘ ν) ◾ Subʳ σ .ᴬ & δᶜ ν

ε : ∀{Γ}{Γᶜ : Con Γ} → Sub Γᶜ ∙ S.ε
ε {Γ}{Γᶜ} ν = refl

_,s_ : {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {σ : S.Sub Γ Δ}
       (σᶜ : Sub {Γ} Γᶜ {Δ} Δᶜ σ) {A : S.Ty Δ} {Aᶜ : Ty {Δ} Δᶜ A}
       {t : S.Tm Γ (S._[_]T {Γ} {Δ} A σ)} →
       Tm {Γ} Γᶜ {S._[_]T {Γ} {Δ} A σ}
       (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {A} Aᶜ {σ} σᶜ) t →
       Sub {Γ} Γᶜ {Δ S.▶ A} (_▶_ {Δ} Δᶜ {A} Aᶜ) (S._,s_ {Γ} {Δ} σ {A} t)
_,s_ {Γ}{Γᶜ}{Δ}{Δᶜ}{σ} σᶜ {A}{Aᶜ}{t} tᶜ ν =
  ,≡ (σᶜ ν) (coe-coe _ _ (Aᶜ (σ S.∘ ν) (t S.[ ν ]t)) ◾ tᶜ ν)

π₁    : {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {A : S.Ty Δ}
        {Aᶜ : Ty {Δ} Δᶜ A} {σ : S.Sub Γ (Δ S.▶ A)} →
        Sub {Γ} Γᶜ {Δ S.▶ A} (_▶_ {Δ} Δᶜ {A} Aᶜ) σ →
        Sub {Γ} Γᶜ {Δ} Δᶜ (S.π₁ {Γ} {Δ} {A} σ)
π₁ {Γ}{Γᶜ}{Δ}{Δᶜ}{A}{Aᶜ}{σ} σᶜ ν = ₁ & σᶜ ν

_[_]t :
        {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {A : S.Ty Δ}
        {Aᶜ : Ty {Δ} Δᶜ A} {t : S.Tm Δ A} →
        Tm {Δ} Δᶜ {A} Aᶜ t →
        {σ : S.Sub Γ Δ} (σᶜ : Sub {Γ} Γᶜ {Δ} Δᶜ σ) →
        Tm {Γ} Γᶜ {S._[_]T {Γ} {Δ} A σ}
        (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {A} Aᶜ {σ} σᶜ) (S._[_]t {Γ} {Δ} {A} t σ)
_[_]t {Γ}{Γᶜ}{Δ}{Δᶜ}{A}{Aᶜ} {t} tᶜ {σ} σᶜ ν =
  (coe (Tyʳ A .ᴬ & σᶜ ν)) & tᶜ (σ S.∘ ν) ◾ apd (Tmʳ t .ᴬ) (σᶜ ν)

π₂    :
        {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {A : S.Ty Δ}
        {Aᶜ : Ty {Δ} Δᶜ A} {σ : S.Sub Γ (Δ S.▶ A)}
        (σᶜ : Sub {Γ} Γᶜ {Δ S.▶ A} (_▶_ {Δ} Δᶜ {A} Aᶜ) σ) →
        Tm {Γ} Γᶜ {S._[_]T {Γ} {Δ} A (S.π₁ {Γ} {Δ} {A} σ)}
        (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {A} Aᶜ {S.π₁ {Γ} {Δ} {A} σ}
         (π₁ {Γ} {Γᶜ} {Δ} {Δᶜ} {A} {Aᶜ} {σ} σᶜ))
        (S.π₂ {Γ} {Δ} {A} σ)
π₂ {Γ}{Γᶜ}{Δ}{Δᶜ}{A}{Aᶜ}{σ} σᶜ ν =
  coe-coe _ _ (Aᶜ (S.π₁ (σ S.∘ ν)) (S.π₂ (σ S.∘ ν))) ◾ apd ₂ (σᶜ ν)

[id]T : {Γ : S.Con} {Γᶜ : Con Γ} {A : S.Ty Γ} {Aᶜ : Ty {Γ} Γᶜ A} →
        _≡_ {j} {Ty {Γ} Γᶜ A}
        (_[_]T {Γ} {Γᶜ} {Γ} {Γᶜ} {A} Aᶜ {S.id {Γ}} (id {Γ} {Γᶜ})) Aᶜ
[id]T = refl

[][]T : {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {Σ₁ : S.Con}
        {Σᶜ : Con Σ₁} {A : S.Ty Σ₁} {Aᶜ : Ty {Σ₁} Σᶜ A} {σ : S.Sub Γ Δ}
        {σᶜ : Sub {Γ} Γᶜ {Δ} Δᶜ σ} {δ : S.Sub Δ Σ₁}
        {δᶜ : Sub {Δ} Δᶜ {Σ₁} Σᶜ δ} →
        _≡_ {j} {Ty {Γ} Γᶜ (S._[_]T {Γ} {Σ₁} A (S._∘_ {Γ} {Δ} {Σ₁} δ σ))}
        (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S._[_]T {Δ} {Σ₁} A δ}
         (_[_]T {Δ} {Δᶜ} {Σ₁} {Σᶜ} {A} Aᶜ {δ} δᶜ) {σ} σᶜ)
        (_[_]T {Γ} {Γᶜ} {Σ₁} {Σᶜ} {A} Aᶜ {S._∘_ {Γ} {Δ} {Σ₁} δ σ}
         (_∘_ {Γ} {Γᶜ} {Δ} {Δᶜ} {Σ₁} {Σᶜ} {δ} δᶜ {σ} σᶜ))
[][]T {Γ}{Γᶜ}{Δ}{Δᶜ}{Σ}{Σᶜ}{A}{Aᶜ}{σ}{σᶜ}{δ}{δᶜ} =
  ext λ ν → ext λ t → uñ (
      (uncoe ((λ γ → ᴬ (Tyʳ A) (ᴬ (Subʳ δ) γ)) & σᶜ ν)
             (coe (Tyʳ A .ᴬ & δᶜ (σ S.∘ ν)) (Aᶜ (δ S.∘ (σ S.∘ ν)) t))
    ◾̃ uncoe (Tyʳ A .ᴬ & δᶜ (σ S.∘ ν)) (Aᶜ (δ S.∘ (σ S.∘ ν)) t))
    ◾̃ uncoe (Tyʳ A .ᴬ & (δᶜ (σ S.∘ ν) ◾ Subʳ δ .ᴬ & σᶜ ν))
          (Aᶜ (δ S.∘ (σ S.∘ ν)) t) ⁻¹̃)

-- Tm and Sub equations are all trivial by UIP
