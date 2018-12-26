{-# OPTIONS  --rewriting  #-}

-- proof #~el
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
import ModelCwf as M
open import Syntax as S
open import Composition as C

module RelationCwfSubstitution  where

-- j'ai pas trouvé dans la libraire HoTT..
-- transport sur PathOver
tr!-over : ∀ {i j k} {A : Type i} {B : A → Type j}(C : ∀ a → B a → Type k)
  {x y : A} {p : x ≡ y} {u : B x} {v : B y} (q : u == v [ B ↓ p ]) → C y v → C x u
tr!-over C {p = refl} refl c = c

open import RelationCwf

Ty[]~ : ∀ 
  {Γ}{Γw : Conw Γ} (Γm : ∃ (Con~ Γw))
  {Δ}{Δw : Conw Γ} (Δm : ∃ (Con~ Δw))
  {σ}{σw : Subw Γ Δ σ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
  {A}{Aw : Tyw Δ A} (Am : ∃ (Ty~ Aw {₁ Δm}))
  → Ty~ (Tywₛ Aw Γw σw) {₁ Γm} (₁ Am M.[ ₁ σm ]T)

Var[]~ : ∀ 
   Γm
  Δm
  {Γ}{Δ}{σ}{σw : Subw Γ Δ σ}(σm : ∃ (Sub~ σw {Γm}{Δm}))
  {A}{Aw : Tyw Δ A} (Am : ∃ (Ty~ Aw {Δm}))
  {x}{xw : Varw Δ A x} (xm : ∃ (Var~ xw {Δm}{₁ Am}))
  → Tm~ (Varwₛ xw σw) {Γm} {₁ Am M.[ ₁ σm ]T} (₁ xm M.[ ₁ σm ]t)

  -- Ty[]~ Γm Δm σm Am = {!!}
Ty[]~ Γm Δm σm Am = {!!}

Var[]~ Γm (.(₁ Δm M.▶ ₁ Am')) {σw = ,sw  Γw' {σp = σ} σw Aw' {tp = t} tw}
  -- σm
  (sm , Δm' , σm' , Am'' , tm' , eC , eS)
  (.(₁ Am' M.[ M.π₁ M.id ]T) , Ar) {xw = V0w Γp Γw Ap Aw} (xm , Δm , Am' , refl , refl , refl)
  rewrite wkₛT Ap t σ
  | prop-has-all-paths Γw' Γw
  | prop-has-all-paths Δm' Δm

  | prop-has-all-paths Aw' Aw
  | prop-has-all-paths Am'' Am'

  | prop-has-all-paths eC refl
  | eS
    =
      tr!-over (λ Em → Tm~ tw {Am = Em}) (M.vz[,s] (₁ σm') (₁ Am') (₁ tm')) (₂ tm')

Var[]~ Γm _ {σw = ,sw Δw' {σp = σ} σw Aw' {tp = t} tw}
  (sm , Δm' , σm , Am'' , tm , eC , eS)
  (Am , Ar) {xw = VSw Δp Δw Ap Aw Bp Bw xp xw}
  (_ , Δm , Am' , Bm , xm , refl , refl , refl  )
  rewrite wkₛT Bp t σ
  | prop-has-all-paths Δw' Δw
  | prop-has-all-paths Δm' Δm

  | prop-has-all-paths Aw' Aw
  | prop-has-all-paths Am'' Am'

  | prop-has-all-paths eC refl
  | eS
  =
    tr!-over (λ Em → Tm~ (Varwₛ xw σw) {Am = Em}) {p = M.wk[]T}M.wk[]t
      ( ( (Var[]~ Γm (₁ Δm) σm Bm xm  ) ) )
