{-
Paper: section 4

Universe part of the initial algebra construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S
open import StrictLib hiding (id; _∘_)
import ADS as ADS
open import ADS using (Conʳ; Tyʳ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ; mkCon; mkTy; mkTm; mkSub)

module InitialAlg.ElU (Ω : S.Con) where

open import InitialAlg.CwF Ω

U  : {Γ : S.Con} {Γᶜ : Con Γ} → Ty {Γ} Γᶜ (S.U {Γ})
U {Γ}{Γᶜ} ν t = S.Tm Ω (S.El t)

U[]  : {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {σ : S.Sub
       Γ Δ} {σᶜ : Sub {Γ} Γᶜ {Δ} Δᶜ σ} → _≡_ {j} {Ty {Γ} Γᶜ (S.U
       {Γ})} (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ)
       (U {Γ} {Γᶜ})
U[] {Γ}{Γᶜ}{Δ}{Δᶜ}{σ}{σᶜ} = refl

El   : {Γ : S.Con} {Γᶜ : Con Γ} {a : S.Tm Γ (S.U {Γ})} →
       Tm {Γ} Γᶜ {S.U {Γ}} (U {Γ} {Γᶜ}) a → Ty {Γ} Γᶜ (S.El {Γ} a)
El {Γ}{Γᶜ}{a} aᶜ ν t = lift (coe (aᶜ ν) t)

El[] : {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {σ : S.Sub
       Γ Δ} {σᶜ : Sub {Γ} Γᶜ {Δ} Δᶜ σ} {a : S.Tm Δ (S.U {Δ})} {aᶜ :
       Tm {Δ} Δᶜ {S.U {Δ}} (U {Δ} {Δᶜ}) a} → _≡_ {j} {Ty {Γ} Γᶜ
       (S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ))} (_[_]T {Γ} {Γᶜ}
       {Δ} {Δᶜ} {S.El {Δ} a} (El {Δ} {Δᶜ} {a} aᶜ) {σ} σᶜ) (El {Γ}
       {Γᶜ} {S._[_]t {Γ} {Δ} {S.U {Δ}} a σ} (coe {j} {Tm {Γ} Γᶜ {S.U
       {Γ}} (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ)
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} {Tm {Γ} Γᶜ {S.U {Γ}} (U {Γ}
       {Γᶜ}) (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (_&_ {j} {suc j} {Ty
       {Γ} Γᶜ (S.U {Γ})} {Set j} (λ x → Tm {Γ} Γᶜ {S.U {Γ}} x
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)) {_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ}
       {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ} {U {Γ} {Γᶜ}} (U[] {Γ} {Γᶜ} {Δ}
       {Δᶜ} {σ} {σᶜ})) (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} {U {Δ}
       {Δᶜ}} {a} aᶜ {σ} σᶜ)))
El[] {Γ}{Γᶜ}{Δ}{Δᶜ}{σ}{σᶜ}{a}{aᶜ} =
  ext λ ν → ext λ t → uñ (
      uncoe ((λ γ → Lift (ᴬ (Tmʳ a) γ)) & σᶜ ν)
            (lift (coe (aᶜ (σ S.∘ ν)) t))
    ◾̃ ap2̃̃ (λ A → lift {A = A})
        (Tmʳ a .ᴬ & σᶜ ν)
        (  uncoe (aᶜ (σ S.∘ ν)) t
         ◾̃ uncoe (aᶜ (σ S.∘ ν) ◾ apd (Tmʳ a .ᴬ) (σᶜ ν)) t ⁻¹̃))
