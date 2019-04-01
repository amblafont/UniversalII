{-
Paper: section 6

Metatheoretic function space part of the eliminator construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S

open import StrictLib hiding (_∘_;id)

import InitialAlg.Eliminators as IA
open import InitialAlg.Eliminators using (Conᶜ; Tmᶜ; Subᶜ; Tyᶜ)

import ADS as ADS
open import ADS using (Conʳ; Tyʳ ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ)

module Elimination.PiNI (Ω : S.Con)(ω : Conʳ Ω .ᴰ (Conᶜ Ω Ω S.id)) where

open import Elimination.CwF Ω ω

ΠNI : {Γ : S.Con} {Γᴱ : Con Γ} (A : Set) {B : A → S.Ty Γ} →
      ((a : A) → Ty {Γ} Γᴱ (B a)) → Ty {Γ} Γᴱ (S.ΠNI {Γ} A B)
ΠNI {Γ}{Γᴱ} A {B} Bᴱ ν t α = Bᴱ α ν (S.appNI t α)

ΠNI[] : {Γ : S.Con} {Γᴱ : Con Γ} {Δ : S.Con} {Δᴱ : Con Δ} {σ : S.Sub
        Γ Δ} {σᴱ : Sub {Γ} Γᴱ {Δ} Δᴱ σ} {A : Set} {B : A → S.Ty Δ}
        {Bᴱ : (a : A) → Ty {Δ} Δᴱ (B a)} → _≡_ {j} {Ty {Γ} Γᴱ (S.ΠNI
        {Γ} A (λ α → S._[_]T {Γ} {Δ} (B α) σ))} (_[_]T {Γ} {Γᴱ} {Δ}
        {Δᴱ} {S.ΠNI {Δ} A B} (ΠNI {Δ} {Δᴱ} A {B} Bᴱ) {σ} σᴱ) (ΠNI
        {Γ} {Γᴱ} A {λ α → S._[_]T {Γ} {Δ} (B α) σ} (λ a → _[_]T {Γ}
        {Γᴱ} {Δ} {Δᴱ} {B a} (Bᴱ a) {σ} σᴱ))
ΠNI[] {Γ}{Γᴱ}{Δ}{Δᴱ}{σ}{σᴱ}{A}{B}{Bᴱ} =
  ext λ ν → ext λ t → uñ (uncoe
      ((λ x → (α : A) → Tyʳ (B α) .ˢ (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω
          S.id))) (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν)
          (Conᶜ Ω Ω S.id) ω)) x (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id) α) (ᴰ (Tmʳ
          t) (Conᶜ Ω Ω S.id) ω α)) & σᴱ ν) (λ α → Bᴱ α (σ S.∘ ν)
          (S.appNI t α))
     ◾̃ ext̃ (λ α → uncoe
      ((λ x → ˢ (Tyʳ (B α)) (ᴬ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)))
          (ᴰ (Subʳ σ) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν) (Conᶜ Ω
          Ω S.id) ω)) x (Tmʳ t .ᴬ (Conᶜ Ω Ω S.id) α) (Tmʳ t .ᴰ (Conᶜ Ω
          Ω S.id) ω α)) & σᴱ ν) (Bᴱ α (σ S.∘ ν) (S.appNI t α)) ⁻¹̃))

appNI :
  {Γ : S.Con} {Γᴱ : Con Γ} {A : Set} {B : A → S.Ty Γ}
  {Bᴱ : (a : A) → Ty {Γ} Γᴱ (B a)} {t : S.Tm Γ (S.ΠNI {Γ} A B)} →
  Tm {Γ} Γᴱ {S.ΠNI {Γ} A B} (ΠNI {Γ} {Γᴱ} A {B} Bᴱ) t →
  (α : A) → Tm {Γ} Γᴱ {B α} (Bᴱ α) (S.appNI {Γ} {A} {B} t α)
appNI {Γ}{Γᴱ}{A}{B}{Bᴱ}{t} tᴱ α ν = ((λ f → f α) & tᴱ ν)

-- appNI[] : UIP
