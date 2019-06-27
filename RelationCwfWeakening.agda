{-# OPTIONS  --rewriting  #-}

-- proof #~el
open import Level
open import Hott renaming ( _∙_ to _◾_ ;  transport to tr ; fst to ₁ ; snd to ₂)
open import monlib

open import Data.Nat renaming (suc to S)

module RelationCwfWeakening {k : Level} where


open import Syntax {k} as S
import ModelCwf {k = k} as M
open import RelationCwf


Telw' : Conp  → Conp → Set (lsucc k)
Telw' Γ ∙p = Lift (0 ≡ 0)
Telw' Γ (Δ ▶p A) = Σ (Γ ⊢ A) (λ _ → (Telw' (Γ ▶p A) Δ))

Tel~' : ∀ {Γ}{Δ}(Δw : Telw' Γ Δ){Γm}(Δm : M.Tel' Γm) → Set (lmax (lmax k M.i) M.j) 
-- Tel~' {Γ}{Δ}Δw {Γm}Δm = {!Δ!}
Tel~' {Γ} {∙p} Δw {Γm} Δm = Lift (Δm ≡ M.∙t')
Tel~' {Γ} {Δ ▶p A} (Aw , Δw) {Γm} Em =
  Σ (Σ _ (Ty~ Aw)) λ Am →
  Σ (Σ _ (Tel~'  Δw )) λ Δm →
  Em ≡ (₁ Am M.◀t ₁ Δm)

Telrec-concat' : ∀{i}(Γ : Conp)(P : ∀ (Δ : Conp) → Set i)
    (P∙ :  P Γ )
    (P▶ : ∀  (Δ : Conp)(A : Typ) → P Δ → P (((∙p ▶p A) ^^ Δ )))
    → ∀ (Δ : Conp) → P (Δ ^^ Γ)

Telrec-concat' Γ P P∙ P▶ ∙p = {!!}
Telrec-concat' Γ P P∙ P▶ (Δ ▶p A) = {! transport P ? (P▶ (Δ ^^ Γ) A ?) !}
-- (Telrec-concat Γ P P∙ P▶ Δ)

-- ^^'▶p : ∀ Γ Δ A → (Γ ^^' (Δ ▶))



   -- → (wkw : Γ ^^' Δ ⊢ iter ∣ Δ ∣ wkS (idp ∣ Γ ∣) ⇒ Γ )
   -- → (should be equal to iter ∣ Δ ∣ wkS (idp ∣ Γ ∣) ⇒ Γ )

-- NTI: could be avoided. We want to state that it is equal to
-- iter ∣ Δ ∣ wkS (idp ∣ Γ ∣) 
verylongWk : Conp → Conp → Subp
verylongWk ∙p Δ = nil
verylongWk (Γ ▶p A) Δ = V ∣ Δ ∣ ∷ verylongWk Γ (Δ ▶p A)

verlong▶pT : ∀ {Γ Δ A
(A [ verylongWk Γ (( Δ) ▶p A) ]T)

-- wkTel' : ℕ → Conp → Conp
-- wkTel' n ∙p = ∙p
-- wkTel' n (Δ ▶p A) = wkTel' (S n) Δ ▶p iter n wkT A

{-
Varn~ : ∀  {Γ} {Γw : Γ ⊢}{Γm}(Γr : Con~ Γw Γm)
     {A}{Aw : Γ ⊢ A}{Am}(A~ : Ty~ Aw Am)
     Δ'
     {Δ}{Δw : Telw' (Γ ▶p A) (Δ ^^ Δ')} →
    ∀ {Δm : M.Tel' (Γm M.▶ Am)}(Δ~ : Tel~' Δw Δm)
    -- 
    -- it should be equal to (A [ verylongWk Γ ((Δ ^^ Δ') ▶p A) ]T)
     A'
  (xw : ((Γ ▶p A) ^^' (Δ ^^ Δ')) ⊢ ∣ Δ ^^ Δ' ∣ ∈v
        A') →
        -- (A [ verylongWk Γ ((Δ' ^^ Δ) ▶p A) ]T)) →
   Var~ xw
      (tr (λ s → M.Tm (( Γm M.▶  Am) M.^^' Δm) ( Am M.[ s ]T))
       (! M.wk∘) (M.π₂ (M.verylongWk Δm)))
       -}



Varnstat  =  λ Δ →
   ∀  {Γ} {Γw : Γ ⊢}{Γm}(Γr : Con~ Γw Γm)
     {A}{Aw : Γ ⊢ A}{Am}(A~ : Ty~ Aw Am)
     {Δw : Telw' (Γ ▶p A) Δ} →
    ∀ {Δm : M.Tel' (Γm M.▶ Am)}(Δ~ : Tel~' Δw Δm)
    -- 
    -- it should be equal to (A [ verylongWk Γ ((Δ ^^ Δ') ▶p A) ]T)
     -- A'
  (xw : ((Γ ▶p A) ^^' Δ) ⊢ ∣ Δ  ∣ ∈v
        -- A'
        (A [ verylongWk Γ (( Δ) ▶p A) ]T)
        ) →
   Var~ xw
      (tr (λ s → M.Tm (( Γm M.▶  Am) M.^^' Δm) ( Am M.[ s ]T))
       (! M.wk∘) (M.π₂ (M.verylongWk Δm)))

Varn~ : ∀ {Δ} {Γ} {Γw : Γ ⊢}{Γm}(Γr : Con~ Γw Γm)
     {A}{Aw : Γ ⊢ A}{Am}(A~ : Ty~ Aw Am)
     {Δw : Telw' (Γ ▶p A) Δ} →
    ∀ {Δm : M.Tel' (Γm M.▶ Am)}(Δ~ : Tel~' Δw Δm)
    -- 
    -- it should be equal to (A [ verylongWk Γ ((Δ ^^ Δ') ▶p A) ]T)
     -- A'
  (xw : ((Γ ▶p A) ^^' Δ) ⊢ ∣ Δ  ∣ ∈v
        (A [ verylongWk Γ (( Δ) ▶p A) ]T)) →
        -- (A [ verylongWk Γ ((Δ' ^^ Δ) ▶p A) ]T)) →
   Var~ xw
      (tr (λ s → M.Tm (( Γm M.▶  Am) M.^^' Δm) ( Am M.[ s ]T))
       (! M.wk∘) (M.π₂ (M.verylongWk Δm)))

Varn~ {Δ} = Tel-last-ind Varnstat {!Varnstat!} {!!} Δ


Varn-succ~ : (Δ : Conp) (A : Typ) →
      Varnstat Δ → Varnstat (∙p ▶p A ^^ Δ)
Varn-succ~ Δ B vΔ {Γ}{Γw}{Γm}Γ~ {A}{Aw}{Am} A~ {Δw}{Δm}Δ~ xw rewrite ^^'-^^ (Γ ▶p A) (∙p ▶p B) Δ | ∣^^∣ Δ B
  | Varw= _ _ _ xw {!VSw!}
  = {!!}
-- =
--    λ { _ (VSw Γw' Aw' Bw xw ) →
--      {!!}
--      }
-- Varn-succ~ Δ B vΔ {Γ} {Γw} {Γm} Γ~ {A} {Aw} {Am} A~ {Δw} {Δm} Δ~ _ (VSw Γw₁ Aw₁ Bw xw) | _ | refl | _ | refl = ?

-- Varn~ {Γ}{Γw}{Γm}Γ~{A}{Aw}{Am}A~ {Δ}{Δw}{Δm}Δ~ A' xw = {!Δ!}

-- Varn~ {Γ}{Γw}{Γm}Γ~{A}{Aw}{Am}A~{Δ}{Δw}{Δm}Δ~ xw = {!Δ!}
-- Varn~ {Γ}{Γw}{Γm}Γ~{A}{Aw}{Am}A~ {Δ}{Δw}{Δm}Δ~ xw = {!Δ!}
-- Varn~ {Γ} {Γw} {Γm} Γ~ {A} {Aw} {Am} A~ Δ' {_} {Δw} {Δm} Δ~ xw = {!!}
-- -- Varn~ {Γ} {Γw} {Γm} Γ~ {A} {Aw} {Am} A~ Δ' {Δ ▶p B} {Δw} {Δm} Δ~ xw = {!!}
-- Varn~ {Γ} {Γw} {Γm} Γ~ {A} {Aw} {Am} A~ Δ' {Δ ▶p B} {Δw} {Δm} Δ~ A' xw = {!xw!}


wk^n~ : ∀ {Γ} {Γw : Γ ⊢}{Γm}(Γr : Con~ Γw Γm){Δ}{Δw : Telw' Γ Δ}
   → ∀ {Δm : M.Tel' Γm}(Δ~ : Tel~' Δw Δm)
-- {A}(Aw : Γ ⊢ A)
   -- → (wkw : (Γ ▶p A) ^^' wkTel' 0 Δ ⊢ iter ∣ Δ ∣ wkS (idp ∣ Γ ∣) ⇒ Γ ^^' Δ)
   -- → (wkw : Γ ^^' Δ ⊢ iter ∣ Δ ∣ wkS (idp ∣ Γ ∣) ⇒ Γ )
   → (wkw : Γ ^^' Δ ⊢ verylongWk Γ Δ ⇒ Γ )
   -- {Am : M.Ty Γm}
   -- → ∀ {Γm}{Δm}(ΓΔm : M.isTel Γm Δm){Am : M.Ty Γm}
   → Sub~ wkw (M.verylongWk  Δm)

-- wk^n~ {Γ}{Γw}{Γm}Γr{Δ}Δw{A}Aw wkw Δm = {!!}
-- wk^n~ {Γ}{Γw}{Γm}Γ~{Δ}{Δw}{Δm}Δ~ wkw  = {!!}
wk^n~ {.∙p} {∙w} {Γm} Γ~ {Δ} {Δw} {Δm} Δ~ wkw = {!!}
wk^n~ {.(_ ▶p _)} {▶w Γw Aw} (Γm , Am , refl) {Δ} {Δw} {Δm} Δ~ (,sw Γw' wkw {Ap = Ap}Aw' (vw xw))  
  rewrite prop-has-all-paths Γw Γw' 
    | prop-has-all-paths Aw' Aw =
    Γm ,
    (((M.verylongWk (₁ Am M.◀t Δm) ,
       wk^n~ (₂ Γm) {Δ = Δ ▶p Ap } {Aw , Δw }
        ((Am , (Δm , Δ~) , refl))
        wkw
        )) ,
    Am ,
    -- V ∣ Δ ∣ must be related to this guy
      (
      (
      -- tr (M.Tm _) ( M.[][]T {A = ₁ Am} {M.verylongWk Δm}{M.wk}) (M.vz M.[  M.verylongWk Δm ]t)
      tr (λ s → M.Tm _ (₁ Am M.[ s ]T)) (! M.wk∘) ( M.π₂  (M.verylongWk Δm) )
      ,
      {!!})
      , refl , ! M.πη ◾ M.,s= (! M.wk∘) (from-transp _ (! M.wk∘) refl)))

{-


-- σar : (Sub~ (keepw Γw σw (Elw Δw aw)) (₁ σm M.^ M.El (₁ am)))


wkTel~ :
  ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
    {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Tel~ {Γp = Γ} Δw {₁ Γm}))
    →
    Tel~ {Γp = Γ ▶p E}{Δp = wkTel Δ}(wkTelw {Γp = Γ} Ew Δ Δw) (M.wkTel (₁ Em) (₁ Δm))

liftT~ :
    ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
    {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Tel~ {Γp = Γ} Δw {₁ Γm}))
    {A}{Aw : (Γ ^^ Δ) ⊢ A}(Am : ∃ (Ty~ Aw {(₁ Γm) M.^^ (₁ Δm)})) →
    Ty~ (liftTw Ew Δ Aw) (M.liftT (₁ Δm) (₁ Em) (₁ Am))

liftt~ :
  ∀ {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw) )
  {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
  {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Tel~ {Γp = Γ} Δw {₁ Γm}))
  {t}{A}{tw : (Γ ^^ Δ) ⊢ t ∈ A}
  {Am : M.Ty  ((₁ Γm) M.^^ (₁ Δm))}(tm : ∃ (Tm~ tw {₁ Γm M.^^ (₁ Δm)}{Am} )) →
  Tm~ (lifttw Ew Δ tw) (M.liftt (₁ Δm) (₁ Em) (₁ tm))

liftV~ :
  -- j'ai besoin que Γm soit relié pour le cas 0 des variables
  ∀ {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw) )
  {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
  {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Tel~ {Γp = Γ} Δw {₁ Γm}))
  -- j'ai besoin que Am soit relié pour le cas 0 des variables
  -- ah bah non en fait !!TDODO

  -- TDOO enelever cete condition
  -- {A}{Aw : Tyw (Γ ^^ Δ) A}(Am : ∃ (Ty~ Aw {(₁ Γm) M.^^ (₁ Δm)}))
  -- {x}{xw : Varw (Γ ^^ Δ) A x}(xm : ∃ (Var~ xw {₁ Γm M.^^ (₁ Δm)}{₁ Am} )) →
  {x}{A}{xw : (Γ ^^ Δ) ⊢ x ∈v A}{Am :  M.Ty  ((₁ Γm) M.^^ (₁ Δm))}(xm : ∃ (Var~ xw {₁ Γm M.^^ (₁ Δm)}{Am} )) →
  Var~ (liftVw Ew Δ xw) (M.liftt (₁ Δm) (₁ Em) (₁ xm))

-- wkTel~ {Γ}{Γw}Γm{E}{Ew}Em{Δ}{Δw}Δm = ?
wkTel~ {Γ} {Γw} Γm {E} {Ew} Em {∙p} {Δw} (_ , Level.lift refl) = Level.lift refl

wkTel~ {Γ} {Γw} Γm {E} {Ew} Em {Δ ▶p A} {▶w Δw Aw} (_ , Δm , Am , refl) =
   (_ , (wkTel~ Γm Em Δm)) ,
   (_ , liftT~ Γm Em Δm Am) ,
   refl



-- liftT~ {Γ}{Γw}Γm{E}{Ew}Em{Δ}{Δw}Δm{T}{Tw}Tm = {!!}
liftT~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.Up} {Uw  Γw₁} (_ , Level.lift refl) = Level.lift refl
liftT~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(ΠΠp ( _) _)} {Πw Γw Aw Bw} (_ , am , Bm , refl)
  rewrite prop-has-all-paths Δw Γw
  =
  (_ , (liftt~ Γm Em Δm {tw = Aw} am)) ,
  (_ ,
     (liftT~ Γm Em {Δw = ▶w Γw (Elw Γw Aw)}
      (_ , Δm , (_ , am , refl) , refl)
      Bm)) ,
  refl

liftT~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm  {_} {ΠNIw Γw {T}{Bp} Bw} (_ , Bm , refl) =
  (λ a →  _ , liftT~ Γm Em Δm (Bm a)) ,
   refl

liftT~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(Elp _)} {Elw Γw aw} (_ , am , refl) =
  (_ , (liftt~ Γm Em Δm {tw = aw} am)) ,
  refl


-- liftt~ {Γ}{Γw}Γm{E}{Ew}Em{Δ}{Δw}Δm{z}{T}{zw}{Tm}zm = {!!}
liftt~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(V _)} {T} {vw xw} {Tm} zm = liftV~ Γm Em Δm zm
liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {_}{_}  {appw Γw aw {Bp} Bw tw {u} uw} {_} (_ , am , Bm , tm , um , refl , refl)
  rewrite (lift+[↦]T 0 ∣ Δ ∣ u Bp)
    |  prop-has-all-paths Δw Γw
 =
  (_ , liftt~ Γm Em Δm {tw = aw} am) ,
  (_ , liftT~ Γm Em {Δw = ▶w Γw (Elw Γw aw)}
        (_ , Δm , (_ , am , refl) , refl)
          Bm) ,
  (_ , liftt~ Γm Em Δm {tw = tw} tm) ,
  (_ , liftt~ Γm Em Δm {tw = uw} um) ,
   eB  ,
   ≅↓ eapp
  where
    -- eB : (((₁ Bm) M.[ M.< ₁ um > ]T M.[ M.longWk {E = ₁ Em}(₁ Δm) ]T)) ≡
    eB : (
        M.liftT (₁ Δm) (₁ Em) ((₁ Bm) M.[ M.< ₁ um > ]T)
       ) ≡
      ((M.liftT (₁ Δm M.▶t M.El (₁ am)) (₁ Em) (₁ Bm) ) M.[ M.< M.liftt (₁ Δm) (₁ Em) (₁ um)  > ]T)

    eB = M.lift-subT (₁ Δm) {B = ₁ Bm}{t = ₁ um}

    eapp : (((₁ tm) M.$ (₁ um)) M.[ M.longWk {E = ₁ Em}(₁ Δm) ]t ) ≅
      ((₁ tm) M.[ M.longWk {E = ₁ Em} (₁ Δm) ]t) M.$ (₁ um M.[ M.longWk (₁ Δm) ]t)
    -- eapp : {!(((₁ tm) M.$ (₁ um)) M.[ M.longWk (₁ Δm) ]t ) ≅ ?!}
    eapp =  ↓≅ ( M.$[] {σ =  M.longWk (₁ Δm) }{t = ₁ tm}{u = ₁ um})

liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {appNI t _} {_} {appNIw Γw {T} {Bp} Bw tw u} {_}
  (_ , Bm , tm , refl , refl)
 = (λ a → _ , liftT~ Γm Em Δm (Bm a)) ,
 (_ , liftt~ Γm Em Δm {tw = tw} tm) ,
 refl , refl

liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {appNI t _} {_} {appInfw Γw {T} {Bp} Bw tw u} {_}
  (_ , Bm , tm , refl , refl)
 =
 (λ a → _ , liftt~ Γm Em Δm {tw = Bw a} (Bm a)) ,
    (_ , liftt~ Γm Em Δm {tw = tw} tm) ,
      (refl , refl)

liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {ΠInf B} {_} {ΠInfw Γw {T}{Bp} Bw} {_}
  (_ , Bm , refl , refl)
  = (λ a →  _ , liftt~ Γm Em Δm {tw = Bw a}(Bm a)) , refl , refl
-- liftV~ {.(Γp ▶p Ap)} {Γw} Γm {E} {Ew} Em {∙p} {Δw} Δm {.(liftT 0 Ap)} Am {.0} {V0w Γp Γw₁ Ap Aw} xm = {!!}

-- liftV~ {.(Γp ▶p Ap)} {▶w Γw' Aw'} (_ , Γm , Am'' , refl) {E} {Ew} Em {∙p} {Δw} ((Δm , ΔT) , Δr) {_} Am  {.0} {V0w Γp Γw Ap Aw}  (xm , Γm' , Am' , eC , eE , ex)
liftV~ {_} {▶w Γw' Aw'} (_ , Γm , Am'' , refl) {E} {Ew} Em {∙p} {Δw} (_ , Level.lift refl) {_}
    {xw = V0w Γw Aw} {Am = Am} (xm , Γm' , Am' , eC , eE , ex)
   rewrite
       prop-has-all-paths Γw' Γw
     | prop-path (ConP Γw) Γm' Γm

     | prop-has-all-paths Aw' Aw
     | prop-path (TyP Aw (₁ Γm)) Am'' Am'
     -- | eC | eE | ex

     | uip eC refl
     | eE | ex
   =
    (_ , Γm , Am' , refl) ,
     Em ,
    (wAm ,
    (_ , Γm , Am' , refl , (refl , refl)) ,
    (refl , refl , refl))
    -- ({!!} , {!!} , {!!}))
    where
     wAm = (₁ Am' M.[ M.wk ]T) , liftT~ Γm Am' {∙p} {Γw} (_ , Level.lift refl) Am'

-- liftV~ {.(Γp ▶p Ap)} {Γw} (Γm , Γr) {E} {Ew} Em {∙p} {Δw} Δm {.(liftT 0 Bp)} Am {.(S xp)} {VSw Γp Γw' Ap Aw Bp Bw xp xw} (zm , Γm' , Am' , Bm , xm , eC , eE , ezm) =
-- here I can't destruct eC for a reason I don't know (agda bug ?)
liftV~ {_} {Γw} (Γm , Γr) {E} {Ew} Em {∙p} {Δw} (_ , Level.lift refl)
   {xw = VSw Γw' Aw Bw xw} {Am = Am} (zm , Γm' , Am' , Bm , xm , eC , eE , ezm) =
     helper Γm Γr Em Am zm Γm' Am' Bm xm eC eE ezm
  where
    helper : ∀ Γm (Γr : Con~ Γw Γm) (Em : Σ (M.Ty Γm) (Ty~ Ew))
      (Am : M.Ty Γm)  (zm : M.Tm Γm Am) (Γm' : ∃ (Con~ Γw'))
      (Am' : Σ (M.Ty (₁ Γm')) (Ty~ Aw))
      (Bm : Σ (M.Ty (₁ Γm')) (Ty~ Bw))
      (xm : Σ (M.Tm (₁ Γm') (₁ Bm)) (Var~ xw))
      (eC : Γm ≡ (₁ Γm' M.▶ ₁ Am'))
      (eE : PathOver M.Ty eC Am (₁ Bm M.[ M.π₁ M.id ]T))
      (ezm : PathOver (λ CE → M.Tm (₁ CE) (₂ CE)) (pair= eC eE) zm (M.vs (₁ xm)))
      →
        -- Var~ (liftVw Ew Δw (VSw Γp Γw' Ap Aw Bp Bw xp xw)) (M.liftt (M.∙t _) (₁ Em) zm)
        Var~ (liftVw Ew ∙p (VSw Γw' Aw Bw xw)) (M.liftt (M.∙t _) (₁ Em) zm)
    helper .(₁ Γm' M.▶ ₁ Am') Γr Em .(₁ Bm M.[ M.π₁ M.id ]T) .(₁ xm M.[ M.π₁ M.id ]t) Γm' Am' Bm xm refl refl refl =
      (_ , Γm' , Am' , refl) ,
      (Em ,
      -- ((M.liftT (M.∙t (₁ Γm')) (₁ Am') (₁ Bm)) , liftT~ Γm' Am' {∙p} {Γw'} (M.∙t _ , lift refl) Bm  ) ,
      ((₁ Bm M.[ M.wk ]T) , liftT~ Γm' Am' {∙p} {Γw'} (M.∙t _ , lift refl) Bm  ) ,
      (_ , Γm' , Am' , Bm , xm , refl , refl , refl) ,
      refl , refl , refl)

-- liftV~ {Γ} {Γw} Γm {E} {Ew} Em {Δ ▶p C} {▶w Δw Cw} ((_ , ΔT) , (Δm , Am , eΔ)) {.(liftT 0 C)} _ {.0} {V0w .(Γ ^^ Δ) Γw₁ .C Aw} (_ , Γm' , Am' , refl , refl , refl)
liftV~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ ▶p C} {▶w Δw Cw} (_ , (Δm , Am , refl))
  {xw = V0w  Γw  Aw}
  {Am = Cm}
  (zm , Γm' , Am' , eC , eT , ez)
-- liftV~ {Γ} {Γw} Γm {E} {Ew} Em {Δ ▶p C} {▶w Δw Cw} Δm {.(liftT 0 C)} Cm {.0} {V0w .(Γ ^^ Δ) Γw' .C Aw} (zm , Γm' , Am' , eC , eT , ez)
  rewrite (lift-liftT 0 ∣ Δ ∣ C)
  | prop-has-all-paths Δw Γw
  | prop-path (ConP Γw) Γm' (((₁ Γm) M.^^ (₁ Δm)) , ^^~ Γm (₂ Δm))

  | prop-has-all-paths Cw Aw
  | prop-path (TyP Aw _) Am' Am

  | uip eC refl
  | eT | ez
  =
  -- needed : weakening of telescopes
  (((₁ Γm M.▶ ₁ Em) M.^^ (M.wkTel (₁ Em) (₁ Δm))) ,
       ^^~ {Γw = ▶w Γw' Ew}
      (_ , Γm , Em , refl)
        (wkTel~ Γm Em Δm)) ,
  ( _ , (liftT~ Γm Em Δm Am)) ,
  refl ,
  (eA ,
   ≅↓ ex)
  where
   eA = M.lift-wkT (₁ Δm)(₁ Am)
   -- {₁ Am}{₁ Em}
   ex : M.vz M.[ M.longWk (₁ Δm M.▶t ₁ Am) ]t ≅ M.vz
   ex = ↓≅ (M.liftV0 (₁ Δm)(₁ Am)(₁ Em))



liftV~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ ▶p C} {▶w Δw Cw} (_ , Δm , Cm , refl)
   {xw = VSw Γw Aw {Bp} Bw xw}
   {Am = Am}
   (zm , Γm' , Am' , Bm , xm , eC , eE , ez )
  rewrite
    prop-has-all-paths Δw Γw
  | prop-path (ConP Γw) Γm' (((₁ Γm) M.^^ (₁ Δm)) , ^^~ Γm (₂ Δm))

  | prop-has-all-paths Cw Aw
  | prop-path (TyP Aw _) Cm Am'

  | uip eC refl
  | eE | ez
  | (lift-liftT 0 ∣ Δ ∣ Bp)
  =
  -- needed : weakening of telescopes
    (((₁ Γm M.▶ ₁ Em) M.^^ (M.wkTel (₁ Em) (₁ Δm))) ,
         ^^~ {Γw = ▶w Γw' Ew}
           (_ , Γm , Em , refl)
           (wkTel~ Γm Em Δm)) ,
    ( _ , (liftT~ Γm Em Δm Am')) ,
    (_ , liftT~ Γm Em Δm Bm) ,
    (_ , (liftV~ Γm Em Δm xm)) ,
    refl ,
    eB ,
    ex
    where
      eB = M.lift-wkT (₁ Δm)(₁ Bm)
      ex = ≅↓ (↓≅ (M.lift-wkt (₁ Δm) (₁ xm)))



wkSub~ : ∀
  {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
  { Δ σ} {σw : Γ ⊢ σ ⇒ Δ}
  { Δm}(σm : ∃ (Sub~ σw {(₁ Γm)}{Δm}))
  {A }{Aw : Γ ⊢ A} (Am : Σ (M.Ty (₁ Γm)) (Ty~ Aw)) →
  Sub~ (wkSw σw Aw)(₁ σm M.∘ M.wk {A = ₁ Am})


wkSub~ {Γ} {Γw} Γm {.∙p} {.nil} {nilw} {_} (_ , refl , Level.lift refl) {E} {Ew} Em = refl ,  Level.lift M.εη
wkSub~ {Γ} {Γw} Γm {.(_ ▶p _)} {_} {,sw Δw {σp = σp} σw {Ap = Ap} Aw {tp = tp} tw}  {_}
  (_ , Δm , σm , Am , tm , refl , refl)
    {E} {Ew} Em
  = Δm ,
    (_ , wkSub~ Γm σm Em) ,
    (Am ,
    tm' ,
    refl ,
    M.,∘ etm)
    where
      tm'₁ : (M.Tm ((₁ Γm) M.▶ (₁ Em)) (₁ Am M.[ ₁ σm M.∘ M.wk ]T))
      tm'₁ = tr (M.Tm _) (M.[][]T {A = ₁ Am}) ((₁ tm) M.[ M.wk ]t)
      tm'₂ :  Tm~
              (transport! (λ A → (Γ ▶p E) ⊢ (liftt 0 tp) ∈ A ) ([wkS]T σp Ap)
                (wktw Ew tw))
              tm'₁
      tm' = tm'₁ , tm'₂
      etm = from-transp _ _ refl
      tm'₂ rewrite [wkS]T σp Ap =
        tr-over (λ A t → Tm~ (lifttw Ew ∙p tw) {Am = A} t)
           etm
        (liftt~ Γm {Ew = Ew}Em {Δw = Γw} (M.∙t _ , Level.lift refl) {tw = tw} tm)

-- -}
