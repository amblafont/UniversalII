{-
Paper: section 6

Universe part of the eliminator construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S

open import StrictLib hiding (_∘_;id)

import InitialAlg.Eliminators as IA
open import InitialAlg.Eliminators using (Conᶜ; Tmᶜ; Subᶜ; Tyᶜ)

import ADS as ADS
open import ADS using (Conʳ; Tyʳ ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ)

module Elimination.ElU (Ω : S.Con)(ω : Conʳ Ω .ᴰ (Conᶜ Ω Ω S.id)) where

open import Elimination.CwF Ω ω

U : {Γ : S.Con} {Γᴹ : Con Γ} → Ty {Γ} Γᴹ (S.U {Γ})
U {Γ}{Γᴹ} ν a α =
   let α' = coe (Tmᶜ Ω a S.id ⁻¹) α
   in coe (ᴰ (Tmʳ a) (Conᶜ Ω Ω S.id) ω &
             (lower & Tmᶜ Ω α' S.id ⁻¹ ◾ coecoe⁻¹ (Tmᶜ Ω a S.id) α))
          (lower (Tmʳ α' .ᴰ _ ω))

U[]  : {Γ : S.Con} {Γᴹ : Con Γ} {Δ : S.Con} {Δᴹ : Con Δ} {σ : S.Sub
       Γ Δ} {σᴹ : Sub {Γ} Γᴹ {Δ} Δᴹ σ} → _≡_ {j} {Ty {Γ} Γᴹ (S.U
       {Γ})} (_[_]T {Γ} {Γᴹ} {Δ} {Δᴹ} {S.U {Δ}} (U {Δ} {Δᴹ}) {σ} σᴹ)
       (U {Γ} {Γᴹ})
U[] {Γ}{Γᴹ}{Δ}{Δᴹ}{σ}{σᴹ} =
  ext λ ν → ext λ t → ext λ α →
    coe-coe _ _ (lower (Tmʳ (coe (Tmᶜ Ω t S.id ⁻¹) α) .ᴰ (Conᶜ Ω Ω S.id) ω))

El : {Γ : S.Con} {Γᴱ : Con Γ} {a : S.Tm Γ (S.U {Γ})} →
       Tm {Γ} Γᴱ {S.U {Γ}} (U {Γ} {Γᴱ}) a → Ty {Γ} Γᴱ (S.El {Γ} a)

El {Γ}{Γᴱ}{a} aᴱ ν t =
    (λ f → f (lower (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id)))) & aᴱ ν ⁻¹
  ◾ uñ (uncoe
          (ᴰ (Tmʳ a) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id)) (ᴰ (Subʳ ν) (Conᶜ Ω Ω
           S.id) ω) & (lower & Tmᶜ Ω (coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹)
           (lower (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id)))) S.id ⁻¹ ◾ coecoe⁻¹ (Tmᶜ Ω
           (a S.[ ν ]t) S.id) (lower (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id))))) (lower
           (Tmʳ (coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹) (lower (ᴬ (Tmʳ t) (Conᶜ
           Ω Ω S.id)))) .ᴰ (Conᶜ Ω Ω S.id) ω))
       ◾̃ ap2̃̃ (λ A → lower {zero}{suc zero}{A = A})
           (ᴰ (Tmʳ a) (ᴬ (Subʳ ν) (Conᶜ Ω Ω S.id))(ᴰ (Subʳ ν) (Conᶜ Ω Ω S.id) ω) &
               let p :  coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹)
                        (lower (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id))) ≡ t
                   p = uñ (uncoe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹)
                          (lower (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id)))
                        ◾̃ (lower & Tmᶜ Ω t S.id ⁻¹ ~) ◾̃ uncoe (Tmᶜ Ω (a S.[ ν ]t) S.id) t)
               in tr (λ t' → lower
                       (Tmʳ
                        (coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹)
                         (lower (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id))))
                        .ᴬ (Conᶜ Ω Ω S.id))
                       ≡ lower (ᴬ (Tmʳ t') (Conᶜ Ω Ω S.id)))
                     p refl)
           (((Tmʳ
                (coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹)
                (lower (ᴬ (Tmʳ t) (Conᶜ Ω Ω S.id))))
                .ᴰ (Conᶜ Ω Ω S.id) ω) ≃ ᴰ (Tmʳ t) (Conᶜ Ω Ω S.id) ω)
            ∋ ap̃̃ (λ x → Tmʳ (coe (Tmᶜ Ω (a S.[ ν ]t) S.id ⁻¹)
                         (lower x)) .ᴰ (Conᶜ Ω Ω S.id) ω)
                  (Tmᶜ Ω t S.id ⁻¹)
               ◾̃ ap̃̃ (λ x → Tmʳ x .ᴰ con ω)
                    (coecoe⁻¹' (Tmᶜ Ω (a S.[ ν ]t) S.id) t)
              )
     )

El[] : {Γ : S.Con} {Γᴱ : Con Γ} {Δ : S.Con} {Δᴱ : Con Δ} {σ : S.Sub
       Γ Δ} {σᴱ : Sub {Γ} Γᴱ {Δ} Δᴱ σ} {a : S.Tm Δ (S.U {Δ})} {aᴱ :
       Tm {Δ} Δᴱ {S.U {Δ}} (U {Δ} {Δᴱ}) a} → _≡_ {j} {Ty {Γ} Γᴱ
       (S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ))} (_[_]T {Γ} {Γᴱ}
       {Δ} {Δᴱ} {S.El {Δ} a} (El {Δ} {Δᴱ} {a} aᴱ) {σ} σᴱ) (El {Γ}
       {Γᴱ} {S._[_]t {Γ} {Δ} {S.U {Δ}} a σ} (coe {j} {Tm {Γ} Γᴱ {S.U
       {Γ}} (_[_]T {Γ} {Γᴱ} {Δ} {Δᴱ} {S.U {Δ}} (U {Δ} {Δᴱ}) {σ} σᴱ)
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} {Tm {Γ} Γᴱ {S.U {Γ}} (U {Γ}
       {Γᴱ}) (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (_&_ {j} {suc j} {Ty
       {Γ} Γᴱ (S.U {Γ})} {Set j} (λ x → Tm {Γ} Γᴱ {S.U {Γ}} x
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)) {_[_]T {Γ} {Γᴱ} {Δ} {Δᴱ}
       {S.U {Δ}} (U {Δ} {Δᴱ}) {σ} σᴱ} {U {Γ} {Γᴱ}} (U[] {Γ} {Γᴱ} {Δ}
       {Δᴱ} {σ} {σᴱ})) (_[_]t {Γ} {Γᴱ} {Δ} {Δᴱ} {S.U {Δ}} {U {Δ}
       {Δᴱ}} {a} aᴱ {σ} σᴱ)))
El[] = ext λ ν → ext λ t → UIP _ _
