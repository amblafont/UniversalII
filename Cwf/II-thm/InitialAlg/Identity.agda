-- now useless for II
{-
Paper: section 4

Identity type structure part of the initial algebra construction.
-}

{-# OPTIONS --rewriting #-}

import Syntax as S
open import StrictLib hiding (id; _∘_)
import ADS as ADS
open import ADS using (Conʳ; Tyʳ; Tmʳ; Subʳ; ᴬ; ᴰ; ˢ; mkCon; mkTy; mkTm; mkSub)

module InitialAlg.Identity (Ω : S.Con) where

open import InitialAlg.CwF Ω
open import InitialAlg.ElU Ω

-- Identity
--------------------------------------------------------------------------------

Id : {Γ : S.Con} {Γᶜ : Con Γ} {a : S.Tm Γ (S.U {Γ})} (aᶜ : Tm {Γ} Γᶜ
     {S.U {Γ}} (U {Γ} {Γᶜ}) a) {t : S.Tm Γ (S.El {Γ} a)} → Tm {Γ} Γᶜ
     {S.El {Γ} a} (El {Γ} {Γᶜ} {a} aᶜ) t → {u : S.Tm Γ (S.El {Γ} a)}
     → Tm {Γ} Γᶜ {S.El {Γ} a} (El {Γ} {Γᶜ} {a} aᶜ) u → Ty {Γ} Γᶜ
     (S.Id {Γ} a t u)
Id {Γ}{Γᶜ}{a} aᶜ {t} tᶜ {u} uᶜ ν e =
    tᶜ ν ⁻¹
  ◾ ((λ x → lift (coe (aᶜ ν) x)) & S.Reflect e)
  ◾ uᶜ ν

Id[] : {Γ : S.Con} {Γᶜ : Con Γ} {Δ : S.Con} {Δᶜ : Con Δ} {σ : S.Sub
       Γ Δ} {σᶜ : Sub {Γ} Γᶜ {Δ} Δᶜ σ} {a : S.Tm Δ (S.U {Δ})} {aᶜ :
       Tm {Δ} Δᶜ {S.U {Δ}} (U {Δ} {Δᶜ}) a} {t : S.Tm Δ (S.El {Δ} a)}
       (tᶜ : Tm {Δ} Δᶜ {S.El {Δ} a} (El {Δ} {Δᶜ} {a} aᶜ) t) {u :
       S.Tm Δ (S.El {Δ} a)} (uᶜ : Tm {Δ} Δᶜ {S.El {Δ} a} (El {Δ}
       {Δᶜ} {a} aᶜ) u) → _≡_ {j} {Ty {Γ} Γᶜ (S.Id {Γ} (S._[_]t {Γ}
       {Δ} {S.U {Δ}} a σ) (S._[_]t {Γ} {Δ} {S.El {Δ} a} t σ)
       (S._[_]t {Γ} {Δ} {S.El {Δ} a} u σ))} (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ}
       {S.Id {Δ} a t u} (Id {Δ} {Δᶜ} {a} aᶜ {t} tᶜ {u} uᶜ) {σ} σᶜ)
       (Id {Γ} {Γᶜ} {S._[_]t {Γ} {Δ} {S.U {Δ}} a σ} (coe {j} {Tm {Γ}
       Γᶜ {S.U {Γ}} (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ} {Δᶜ})
       {σ} σᶜ) (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} {Tm {Γ} Γᶜ {S.U {Γ}}
       (U {Γ} {Γᶜ}) (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (_&_ {j} {suc
       j} {Ty {Γ} Γᶜ (S.U {Γ})} {Set j} (λ x → Tm {Γ} Γᶜ {S.U {Γ}} x
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)) {_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ}
       {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ} {U {Γ} {Γᶜ}} (U[] {Γ} {Γᶜ} {Δ}
       {Δᶜ} {σ} {σᶜ})) (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} {U {Δ}
       {Δᶜ}} {a} aᶜ {σ} σᶜ)) {S._[_]t {Γ} {Δ} {S.El {Δ} a} t σ} (coe
       {j} {Tm {Γ} Γᶜ {S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)}
       (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.El {Δ} a} (El {Δ} {Δᶜ} {a} aᶜ)
       {σ} σᶜ) (S._[_]t {Γ} {Δ} {S.El {Δ} a} t σ)} {Tm {Γ} Γᶜ {S.El
       {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (El {Γ} {Γᶜ} {S._[_]t
       {Γ} {Δ} {S.U {Δ}} a σ} (coe {j} {Tm {Γ} Γᶜ {S.U {Γ}} (_[_]T
       {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ) (S._[_]t {Γ}
       {Δ} {S.U {Δ}} a σ)} {Tm {Γ} Γᶜ {S.U {Γ}} (U {Γ} {Γᶜ})
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (_&_ {j} {suc j} {Ty {Γ} Γᶜ
       (S.U {Γ})} {Set j} (λ x → Tm {Γ} Γᶜ {S.U {Γ}} x (S._[_]t {Γ}
       {Δ} {S.U {Δ}} a σ)) {_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ}
       {Δᶜ}) {σ} σᶜ} {U {Γ} {Γᶜ}} (U[] {Γ} {Γᶜ} {Δ} {Δᶜ} {σ} {σᶜ}))
       (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} {U {Δ} {Δᶜ}} {a} aᶜ {σ}
       σᶜ))) (S._[_]t {Γ} {Δ} {S.El {Δ} a} t σ)} (_&_ {j} {suc j}
       {Ty {Γ} Γᶜ (S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ))} {Set
       j} (λ x → Tm {Γ} Γᶜ {S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a
       σ)} x (S._[_]t {Γ} {Δ} {S.El {Δ} a} t σ)) {_[_]T {Γ} {Γᶜ} {Δ}
       {Δᶜ} {S.El {Δ} a} (El {Δ} {Δᶜ} {a} aᶜ) {σ} σᶜ} {El {Γ} {Γᶜ}
       {S._[_]t {Γ} {Δ} {S.U {Δ}} a σ} (coe {j} {Tm {Γ} Γᶜ {S.U {Γ}}
       (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ)
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} {Tm {Γ} Γᶜ {S.U {Γ}} (U {Γ}
       {Γᶜ}) (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (_&_ {j} {suc j} {Ty
       {Γ} Γᶜ (S.U {Γ})} {Set j} (λ x → Tm {Γ} Γᶜ {S.U {Γ}} x
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)) {_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ}
       {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ} {U {Γ} {Γᶜ}} (U[] {Γ} {Γᶜ} {Δ}
       {Δᶜ} {σ} {σᶜ})) (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} {U {Δ}
       {Δᶜ}} {a} aᶜ {σ} σᶜ))} (El[] {Γ} {Γᶜ} {Δ} {Δᶜ} {σ} {σᶜ} {a}
       {aᶜ})) (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.El {Δ} a} {El {Δ} {Δᶜ} {a}
       aᶜ} {t} tᶜ {σ} σᶜ)) {S._[_]t {Γ} {Δ} {S.El {Δ} a} u σ} (coe
       {j} {Tm {Γ} Γᶜ {S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)}
       (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.El {Δ} a} (El {Δ} {Δᶜ} {a} aᶜ)
       {σ} σᶜ) (S._[_]t {Γ} {Δ} {S.El {Δ} a} u σ)} {Tm {Γ} Γᶜ {S.El
       {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (El {Γ} {Γᶜ} {S._[_]t
       {Γ} {Δ} {S.U {Δ}} a σ} (coe {j} {Tm {Γ} Γᶜ {S.U {Γ}} (_[_]T
       {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ) (S._[_]t {Γ}
       {Δ} {S.U {Δ}} a σ)} {Tm {Γ} Γᶜ {S.U {Γ}} (U {Γ} {Γᶜ})
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (_&_ {j} {suc j} {Ty {Γ} Γᶜ
       (S.U {Γ})} {Set j} (λ x → Tm {Γ} Γᶜ {S.U {Γ}} x (S._[_]t {Γ}
       {Δ} {S.U {Δ}} a σ)) {_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ}
       {Δᶜ}) {σ} σᶜ} {U {Γ} {Γᶜ}} (U[] {Γ} {Γᶜ} {Δ} {Δᶜ} {σ} {σᶜ}))
       (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} {U {Δ} {Δᶜ}} {a} aᶜ {σ}
       σᶜ))) (S._[_]t {Γ} {Δ} {S.El {Δ} a} u σ)} (_&_ {j} {suc j}
       {Ty {Γ} Γᶜ (S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ))} {Set
       j} (λ x → Tm {Γ} Γᶜ {S.El {Γ} (S._[_]t {Γ} {Δ} {S.U {Δ}} a
       σ)} x (S._[_]t {Γ} {Δ} {S.El {Δ} a} u σ)) {_[_]T {Γ} {Γᶜ} {Δ}
       {Δᶜ} {S.El {Δ} a} (El {Δ} {Δᶜ} {a} aᶜ) {σ} σᶜ} {El {Γ} {Γᶜ}
       {S._[_]t {Γ} {Δ} {S.U {Δ}} a σ} (coe {j} {Tm {Γ} Γᶜ {S.U {Γ}}
       (_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ)
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} {Tm {Γ} Γᶜ {S.U {Γ}} (U {Γ}
       {Γᶜ}) (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)} (_&_ {j} {suc j} {Ty
       {Γ} Γᶜ (S.U {Γ})} {Set j} (λ x → Tm {Γ} Γᶜ {S.U {Γ}} x
       (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)) {_[_]T {Γ} {Γᶜ} {Δ} {Δᶜ}
       {S.U {Δ}} (U {Δ} {Δᶜ}) {σ} σᶜ} {U {Γ} {Γᶜ}} (U[] {Γ} {Γᶜ} {Δ}
       {Δᶜ} {σ} {σᶜ})) (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.U {Δ}} {U {Δ}
       {Δᶜ}} {a} aᶜ {σ} σᶜ))} (El[] {Γ} {Γᶜ} {Δ} {Δᶜ} {σ} {σᶜ} {a}
       {aᶜ})) (_[_]t {Γ} {Γᶜ} {Δ} {Δᶜ} {S.El {Δ} a} {El {Δ} {Δᶜ} {a}
       aᶜ} {u} uᶜ {σ} σᶜ)))
Id[] {Γ}{Γᶜ}{Δ}{Δᶜ}{σ}{σᶜ}{a}{aᶜ}{t} tᶜ {u} uᶜ =
  ext λ ν → ext λ t → UIP _ _

Reflect : {Γ : S.Con} {Γᶜ : Con Γ} {a : S.Tm Γ (S.U {Γ})} (aᶜ : Tm
          {Γ} Γᶜ {S.U {Γ}} (U {Γ} {Γᶜ}) a) {t : S.Tm Γ (S.El {Γ} a)}
          (tᶜ : Tm {Γ} Γᶜ {S.El {Γ} a} (El {Γ} {Γᶜ} {a} aᶜ) t) {u :
          S.Tm Γ (S.El {Γ} a)} (uᶜ : Tm {Γ} Γᶜ {S.El {Γ} a} (El {Γ}
          {Γᶜ} {a} aᶜ) u) {e : S.Tm Γ (S.Id {Γ} a t u)} → Tm {Γ} Γᶜ
          {S.Id {Γ} a t u} (Id {Γ} {Γᶜ} {a} aᶜ {t} tᶜ {u} uᶜ) e →
          _≡_ {j} {Tm {Γ} Γᶜ {S.El {Γ} a} (El {Γ} {Γᶜ} {a} aᶜ) u}
          (tr {zero} {j} {S.Tm Γ (S.El {Γ} a)} (Tm {Γ} Γᶜ {S.El {Γ}
          a} (El {Γ} {Γᶜ} {a} aᶜ)) {t} {u} (S.Reflect {Γ} {a} {t}
          {u} e) tᶜ) uᶜ
Reflect {Γ}{Γᶜ}{a} aᶜ {t} tᶜ {u} uᶜ {e} eᶜ =
  ext λ ν → UIP _ _
