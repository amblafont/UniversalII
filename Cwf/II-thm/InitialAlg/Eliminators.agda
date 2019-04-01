{-
Postulated eliminators of the initial algebra construction (section 4 in paper).
Eliminators were copied from DependentModelTemplate (see README for usage).
-}

{-# OPTIONS --rewriting #-}

import Syntax as S
open import StrictLib hiding (id; _∘_)
module InitialAlg.Eliminators (Ω : S.Con) where

open import InitialAlg.CwF      Ω public
open import InitialAlg.ElU      Ω public
open import InitialAlg.Pi       Ω public
open import InitialAlg.Identity Ω public
open import InitialAlg.PiNI     Ω public

-- Eliminators
--------------------------------------------------------------------------------

postulate
  Conᶜ : (Γ : S.Con) → Con Γ
  Tyᶜ  : ∀ {Γ} → (A : S.Ty Γ) → Ty (Conᶜ Γ) A
  Tmᶜ  : ∀ {Γ A} → (t : S.Tm Γ A) → Tm (Conᶜ Γ) (Tyᶜ A) t
  Subᶜ : ∀ {Γ Δ} → (σ : S.Sub Γ Δ) → Sub (Conᶜ Γ) (Conᶜ Δ) σ

postulate
  ∙ᶜ   : _≡_ {i} {Con S.∙} (Conᶜ S.∙) ∙

  ,ᶜ   : (Γ : S.Con) (A : S.Ty Γ) →
          _≡_ {i} {Con (Γ S.▶ A)} (Conᶜ (Γ S.▶ A))
          (_▶_ {Γ} (Conᶜ Γ) {A} (Tyᶜ {Γ} A))

  []Tᶜ : (Γ Δ : S.Con) (A : S.Ty Δ) (σ : S.Sub Γ Δ) →
          _≡_ {j} {Ty {Γ} (Conᶜ Γ) (S._[_]T {Γ} {Δ} A σ)}
          (Tyᶜ {Γ} (S._[_]T {Γ} {Δ} A σ))
          (_[_]T {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {A} (Tyᶜ {Δ} A) {σ}
           (Subᶜ {Γ} {Δ} σ))
{-# REWRITE ∙ᶜ ,ᶜ []Tᶜ #-}

postulate
  []tᶜ : {Γ Δ : S.Con} {A : S.Ty Δ} (t : S.Tm Δ A) (σ : S.Sub Γ Δ) →
         _≡_ {j}
         {Tm {Γ} (Conᶜ Γ) {S._[_]T {Γ} {Δ} A σ}
          (_[_]T {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {A} (Tyᶜ {Δ} A) {σ}
           (Subᶜ {Γ} {Δ} σ))
          (S._[_]t {Γ} {Δ} {A} t σ)}
         (Tmᶜ {Γ} {S._[_]T {Γ} {Δ} A σ} (S._[_]t {Γ} {Δ} {A} t σ))
         (_[_]t {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {A} {Tyᶜ {Δ} A} {t}
          (Tmᶜ {Δ} {A} t) {σ} (Subᶜ {Γ} {Δ} σ))

  idᶜ  : {Γ : S.Con} →
          _≡_ {j} {Sub {Γ} (Conᶜ Γ) {Γ} (Conᶜ Γ) (S.id {Γ})}
          (Subᶜ {Γ} {Γ} (S.id {Γ})) (id {Γ} {Conᶜ Γ})

  ∘ᶜ   : {Γ Δ : S.Con} {Σ₁ : S.Con} {σ : S.Sub Δ Σ₁} {δ : S.Sub Γ Δ} →
          _≡_ {j} {Sub {Γ} (Conᶜ Γ) {Σ₁} (Conᶜ Σ₁) (S._∘_ {Γ} {Δ} {Σ₁} σ δ)}
          (Subᶜ {Γ} {Σ₁} (S._∘_ {Γ} {Δ} {Σ₁} σ δ))
          (_∘_ {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {Σ₁} {Conᶜ Σ₁} {σ} (Subᶜ {Δ} {Σ₁} σ)
           {δ} (Subᶜ {Γ} {Δ} δ))

  εᶜ   : {Γ : S.Con} →
          _≡_ {j} {Sub {Γ} (Conᶜ Γ) {S.∙} ∙ (S.ε {Γ})}
          (Subᶜ {Γ} {S.∙} (S.ε {Γ})) (ε {Γ} {Conᶜ Γ})

  ,sᶜ  : {Γ Δ : S.Con} (σ : S.Sub Γ Δ) {A : S.Ty Δ}
          (t : S.Tm Γ (S._[_]T {Γ} {Δ} A σ)) →
          _≡_ {j}
          {Sub {Γ} (Conᶜ Γ) {Δ S.▶ A} (_▶_ {Δ} (Conᶜ Δ) {A} (Tyᶜ {Δ} A))
           (S._,s_ {Γ} {Δ} σ {A} t)}
          (Subᶜ {Γ} {Δ S.▶ A} (S._,s_ {Γ} {Δ} σ {A} t))
          (_,s_ {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {σ} (Subᶜ {Γ} {Δ} σ) {A}
           {Tyᶜ {Δ} A} {t} (Tmᶜ {Γ} {S._[_]T {Γ} {Δ} A σ} t))

  π₁ᶜ  : {Γ Δ : S.Con} {A : S.Ty Δ} (σ : S.Sub Γ (Δ S.▶ A)) →
          _≡_ {j} {Sub {Γ} (Conᶜ Γ) {Δ} (Conᶜ Δ) (S.π₁ {Γ} {Δ} {A} σ)}
          (Subᶜ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))
          (π₁ {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {A} {Tyᶜ {Δ} A} {σ}
           (Subᶜ {Γ} {Δ S.▶ A} σ))

{-# REWRITE []tᶜ idᶜ ∘ᶜ εᶜ ,sᶜ π₁ᶜ #-}

postulate
  π₂ᶜ : {Γ Δ : S.Con} {A : S.Ty Δ} (σ : S.Sub Γ (Δ S.▶ A)) →
         _≡_ {j}
         {Tm {Γ} (Conᶜ Γ) {S._[_]T {Γ} {Δ} A (S.π₁ {Γ} {Δ} {A} σ)}
          (_[_]T {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {A} (Tyᶜ {Δ} A)
           {S.π₁ {Γ} {Δ} {A} σ}
           (π₁ {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {A} {Tyᶜ {Δ} A} {σ}
            (Subᶜ {Γ} {Δ S.▶ A} σ)))
          (S.π₂ {Γ} {Δ} {A} σ)}
         (Tmᶜ {Γ} {S._[_]T {Γ} {Δ} A (S.π₁ {Γ} {Δ} {A} σ)}
          (S.π₂ {Γ} {Δ} {A} σ))
         (π₂ {Γ} {Conᶜ Γ} {Δ} {Conᶜ Δ} {A} {Tyᶜ {Δ} A} {σ}
          (Subᶜ {Γ} {Δ S.▶ A} σ))

  Uᶜ  : {Γ : S.Con} →
         _≡_ {j} {Ty {Γ} (Conᶜ Γ) (S.U {Γ})} (Tyᶜ {Γ} (S.U {Γ}))
         (U {Γ} {Conᶜ Γ})
{-# REWRITE π₂ᶜ Uᶜ #-}

postulate
  Elᶜ : {Γ : S.Con} {a : S.Tm Γ (S.U {Γ})} →
        _≡_ {j} {Ty {Γ} (Conᶜ Γ) (S.El {Γ} a)} (Tyᶜ {Γ} (S.El {Γ} a))
        (El {Γ} {Conᶜ Γ} {a} (Tmᶜ {Γ} {S.U {Γ}} a))
{-# REWRITE Elᶜ #-}

postulate
  Πᶜ : {Γ : S.Con} (a : S.Tm Γ (S.U {Γ})) (B : S.Ty (Γ S.▶ S.El {Γ} a)) →
        _≡_ {j} {Ty {Γ} (Conᶜ Γ) (S.Π {Γ} a B)} (Tyᶜ {Γ} (S.Π {Γ} a B))
        (Π {Γ} {Conᶜ Γ} {a} (Tmᶜ {Γ} {S.U {Γ}} a) {B}
         (Tyᶜ {Γ S.▶ S.El {Γ} a} B))
{-# REWRITE Πᶜ #-}

postulate
  appᶜ : {Γ : S.Con} {a : S.Tm Γ (S.U {Γ})} {B : S.Ty (Γ S.▶ S.El {Γ} a)}
          (t : S.Tm Γ (S.Π {Γ} a B)) →
          _≡_ {j}
          {Tm {Γ S.▶ S.El {Γ} a}
           (_▶_ {Γ} (Conᶜ Γ) {S.El {Γ} a}
            (El {Γ} {Conᶜ Γ} {a} (Tmᶜ {Γ} {S.U {Γ}} a)))
           {B} (Tyᶜ {Γ S.▶ S.El {Γ} a} B) (S.app {Γ} {a} {B} t)}
          (Tmᶜ {Γ S.▶ S.El {Γ} a} {B} (S.app {Γ} {a} {B} t))
          (app {Γ} {Conᶜ Γ} {a} {Tmᶜ {Γ} {S.U {Γ}} a} {B}
           {Tyᶜ {Γ S.▶ S.El {Γ} a} B} {t} (Tmᶜ {Γ} {S.Π {Γ} a B} t))
{-# REWRITE appᶜ #-}

postulate
  Idᶜ : {Γ : S.Con} (a : S.Tm Γ (S.U {Γ})) (t u : S.Tm Γ (S.El {Γ} a)) →
        _≡_ {j} {Ty {Γ} (Conᶜ Γ) (S.Id {Γ} a t u)}
        (Tyᶜ {Γ} (S.Id {Γ} a t u))
        (Id {Γ} {Conᶜ Γ} {a} (Tmᶜ {Γ} {S.U {Γ}} a) {t}
         (Tmᶜ {Γ} {S.El {Γ} a} t) {u} (Tmᶜ {Γ} {S.El {Γ} a} u))
{-# REWRITE Idᶜ #-}

postulate
  ΠNIᶜ : {Γ : S.Con} (A : Set) (B : A → S.Ty Γ) →
         _≡_ {j} {Ty {Γ} (Conᶜ Γ) (S.ΠNI {Γ} A B)} (Tyᶜ {Γ} (S.ΠNI {Γ} A B))
         (ΠNI {Γ} {Conᶜ Γ} A {B} (λ α → Tyᶜ {Γ} (B α)))
{-# REWRITE ΠNIᶜ #-}

postulate
  appNIᶜ :
      {Γ : S.Con} (A : Set) (B : A → S.Ty Γ) (t : S.Tm Γ (S.ΠNI {Γ} A B))
      (α : A) →
      _≡_ {j}
      {Tm {Γ} (Conᶜ Γ) {B α} (Tyᶜ {Γ} (B α)) (S.appNI {Γ} {A} {B} t α)}
      (Tmᶜ {Γ} {B α} (S.appNI {Γ} {A} {B} t α))
      (appNI {Γ} {Conᶜ Γ} {A} {B} {λ α₁ → Tyᶜ {Γ} (B α₁)} {t}
       (Tmᶜ {Γ} {S.ΠNI {Γ} A B} t) α)
{-# REWRITE appNIᶜ #-}
