{-
Paper: section 4

Non-inductive (metatheoretic) function space part of the initial algebra construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S
open import StrictLib hiding (id; _∘_)
import ADS as ADS
open import ADS using (Conʳ; Tyʳ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ; mkCon; mkTy; mkTm; mkSub)

module InitialAlg.PiNI (Ω : S.Con) where

open import InitialAlg.CwF Ω

-- Non-inductive functions
--------------------------------------------------------------------------------

ΠNI : {Γ : S.Con} {Γᶜ : Con Γ} (A : Set) {B : A → S.Ty Γ} →
      ((a : A) → Ty {Γ} Γᶜ (B a)) → Ty {Γ} Γᶜ (S.ΠNI {Γ} A B)
ΠNI {Γ}{Γᶜ} A {B} Bᶜ ν t α = Bᶜ α ν (S.appNI t α)

ΠNI[] : {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {σ : S.Sub
        Γ Δ} {σᶜ : Sub {Γ} Γᶜ {Δ} Δᶜ σ} {A : Set} {B : A → S.Ty Δ}
        {Bᶜ : (a : A) → Ty {Δ} Δᶜ (B a)} → _≡_ {j} {Ty {Γ} Γᶜ (S.ΠNI
        {Γ} A (λ α → S._[_]T {Γ} {Δ} (B α) σ))} (_[_]T {Γ} {Γᶜ} {Δ}
        {Δᶜ} {S.ΠNI {Δ} A B} (ΠNI {Δ} {Δᶜ} A {B} Bᶜ) {σ} σᶜ) (ΠNI
        {Γ} {Γᶜ} A {λ α → S._[_]T {Γ} {Δ} (B α) σ} (λ a → _[_]T {Γ}
        {Γᶜ} {Δ} {Δᶜ} {B a} (Bᶜ a) {σ} σᶜ))
ΠNI[] {Γ}{Γᶜ}{Δ}{Δᶜ}{σ}{σᶜ} {A}{B} {Bᶜ} =
  ext λ ν → ext λ t → uñ (
      uncoe ((λ γ → (α : A) → Tyʳ (B α) .ᴬ γ) & σᶜ ν)
            (λ α → Bᶜ α (σ S.∘ ν) (S.appNI t α))
    ◾̃ ext̃ (λ α → uncoe (Tyʳ (B α) .ᴬ & σᶜ ν) (Bᶜ α (σ S.∘ ν)
                       (S.appNI t α)) ⁻¹̃))

appNI :
  {Γ : S.Con} {Γᶜ : Con Γ} {A : Set} {B : A → S.Ty Γ}
  {Bᶜ : (a : A) → Ty {Γ} Γᶜ (B a)} {t : S.Tm Γ (S.ΠNI {Γ} A B)} →
  Tm {Γ} Γᶜ {S.ΠNI {Γ} A B} (ΠNI {Γ} {Γᶜ} A {B} Bᶜ) t →
  (α : A) → Tm {Γ} Γᶜ {B α} (Bᶜ α) (S.appNI {Γ} {A} {B} t α)
appNI {Γ}{Γᶜ}{A}{B}{Bᶜ}{t} tᶜ α ν = (λ f → f α) & (tᶜ ν)

-- appNI[] : UIP
