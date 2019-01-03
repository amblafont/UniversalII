{-# OPTIONS  --rewriting  #-}
-- {-# OPTIONS  --rewriting --no-termination-check #-}

-- proof #~el
open import Level 
open import HoTT renaming (_∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
-- open import Lib2 using (_&_)
-- import Lib2 using (_⁻¹)
import ModelCwf as M
open import Syntax as S

module RelationCwfSubstitution  where



open import RelationCwf
open import RelationCwfWeakening


Var[]~ : ∀ 
   {Γm Δm : M.Con}
   {Γ}{Δ}{σ}{σw : Subw Γ Δ σ}(σm : ∃ (Sub~ σw {Γm}{Δm}))
   {Am : M.Ty Δm}
    {A}{x}{xw : Varw Δ A x} (xm : ∃ (Var~ xw {Δm}{ Am}))
  → Tm~ (Varw[] xw σw) {Γm} { Am M.[ ₁ σm ]T} (₁ xm M.[ ₁ σm ]t)

  -- Ty[]~ Γm Δm σm Am = {!!}

Var[]~ {Γm} {σw = ,sw  Γw' {σp = σ} σw Aw' {tp = t} tw}
  -- σm
  (sm , Δm' , σm' , Am'' , tm' , eC , eS)
   {xw = V0w Γp Γw Ap Aw} (xm , Δm , Am' , refl , refl , refl)
  rewrite wk[,]T Ap t σ
  | prop-has-all-paths Γw' Γw
  | prop-has-all-paths Δm' Δm

  | prop-has-all-paths Aw' Aw
  | prop-has-all-paths Am'' Am'

  | prop-has-all-paths eC refl
  | eS
    =
      tr!-over (λ Em → Tm~ tw {Am = Em}) (M.vz[,s] (₁ σm') (₁ Am') (₁ tm')) (₂ tm')

Var[]~ {Γm} {σw = ,sw Δw' {σp = σ} σw Aw' {tp = t} tw}
  (sm , Δm' , σm , Am'' , tm , eC , eS)
  {Am} {xw = VSw Δp Δw Ap Aw Bp Bw xp xw}
  (_ , Δm , Am' , Bm , xm , refl , refl , refl  )
  rewrite wk[,]T Bp t σ
  | prop-has-all-paths Δw' Δw
  | prop-has-all-paths Δm' Δm

  | prop-has-all-paths Aw' Aw
  | prop-has-all-paths Am'' Am'

  | prop-has-all-paths eC refl
  | eS
  =
    tr!-over (λ Em → Tm~ (Varw[] xw σw) {Am = Em}) {p = M.wk[]T}M.wk[]t
      (Var[]~ σm xm)

Tm[]~ : ∀ 
      {Γ}{Γw : Conw Γ}(Γm : ∃ (Con~ Γw))
      {Δ}{Δw : Conw Δ}(Δm : ∃ (Con~ Δw))
      {σ}{σw : Subw Γ Δ σ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
      {Am : M.Ty (₁ Δm)}
      {A}{t}{tw : Tmw Δ A t} (tm : ∃ (Tm~ tw {₁ Δm}{ Am}))
      → Tm~ (Tmw[] tw Γw σw) {₁ Γm} { Am M.[ ₁ σm ]T} (₁ tm M.[ ₁ σm ]t)

Ty[]~ : ∀ 
   {Γ}{Γw : Conw Γ}(Γm : ∃ (Con~ Γw))
   {Δ}{Δw : Conw Δ}(Δm : ∃ (Con~ Δw))
  {σ}{σw : Subw Γ Δ σ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
  {A}{Aw : Tyw Δ A} (Am : ∃ (Ty~ Aw {₁ Δm}))
  → Ty~ (Tyw[] Aw Γw σw) {₁ Γm} (₁ Am M.[ ₁ σm ]T)
  -- Ty[]~ {Γm}{Δm}{Γ}Γw{Δ}{σ}{σw}  σm{T}{Tw}Tm  = {!!}

keepEl~ : ∀ {Γp}{Γw : Conw Γp}(Γm : ∃ (Con~ Γw))
  {Δp}{Δw : Conw Δp}(Δm : ∃ (Con~ Δw))
  {σp}{σw : Subw Γp Δp σp} (σm : Σ (M.Sub (₁ Γm) (₁ Δm)) (Sub~ σw))
  {Ap}{Aw : Tmw Δp Up Ap}(Am : Σ (M.Tm (₁ Δm) M.U) (Tm~ Aw)) →
  Sub~ (keepw Γw σw (Elw Δw Aw))(₁ σm M.^ M.El (₁ Am))

keepEl~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ}{σw}σm{A}{Aw}Am
  rewrite prop-has-all-paths (Sub-Con2w σw) Δw
  =
    Δm ,
    ((₁ σm M.∘ M.wk) , wkSub~ Γm σm (M.El (₁ Am M.[ ₁ σm ]t) ,
       (_ , Tm[]~ Γm Δm σm {tw = Aw} Am) , refl) 
      -- (Tyw[] Aw Γw σw) (₁ Am M.[ ₁ σm ]T)
      ) ,
    (M.El (₁ Am) , Am , refl) ,
    (tr (M.Tm ((₁ Γm) M.▶ M.El (₁ Am) M.[ ₁ σm ]T)) (M.[][]T {A = M.El (₁ Am)}) M.vz , vz~) ,
    refl ,
    refl
  where
    vz~ : Var~
      (transport! (λ x → Varw (Γ ▶p Elp (A [ σ ]t)) x 0) (liftT=wkS 0 σ (Elp A))
      (V0w Γ Γw ((Elp A) [ σ ]T) (Tyw[] (Elw Δw Aw) Γw σw)))
      (tr (M.Tm ((₁ Γm) M.▶ M.El (₁ Am M.[ ₁ σm ]t))) (M.[][]T {A = M.El (₁ Am)}) M.vz)

    vz~ rewrite (liftT=wkS 0 σ (Elp A)) =
      Γm ,
      (M.El (₁ Am M.[ ₁ σm ]t) , (_ , Tm[]~ Γm Δm σm {tw = Aw} Am) , refl) ,
      -- Ty[]~ Γm Δm σm Am) ,
      refl ,
       ! (M.[][]T {A = M.El (₁ Am)})  ,
      ≅↓ (↓≅  (from-transp (M.Tm (₁ Γm M.▶ M.El (₁ Am M.[ ₁ σm ]t))) (M.[][]T {A = M.El (₁ Am)}) refl)  !≅)


-- helper for Π[] and app[] cases
Π-B[]~ :
  ∀ {Γ}{Γw : Conw Γ}(Γm : ∃ (Con~ Γw))
  {Δ}{Δw : Conw Δ}(Δm : ∃ (Con~ Δw)) (Δw' : Conw Δ)
  {σ}{σw : Subw Γ Δ σ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
  {A}{Aw : Tmw Δ Up A} (am : ∃ (Tm~ Aw {₁ Δm}{M.U}))
  {B}{Bw : Tyw (Δ ▶p Elp A) B} (Bm : ∃ (Ty~ Bw {₁ Δm M.▶ M.El (₁ am) }))
  →
  -- Σ (M.Ty (₁ Γm M.▶ M.El (₁ am M.[ ₁ σm ]t)))
    (Ty~ (Tyw[] Bw (▶w Γw (Elw Γw (Tmw[] Aw Γw σw))) (keepw Γw σw (Elw Δw' Aw))))
    (₁ Bm M.[ ₁ σm M.^ (M.El (₁ am)) ]T)

Π-B[]~
   {Γ}{Γw}Γm
   {Δ}{Δw}Δm Δw'
   {σ}{σw}σm
   {A}{Aw}am
   {B}{Bw}Bm
   =
   let Γaw = (▶w Γw (Elw Γw (Tmw[] Aw Γw σw))) in
   let Δaw = (▶w Δw (Elw Δw' Aw)) in
   let Elam : ∃ (Ty~ (Elw Δw' Aw) {₁ Δm})
       Elam = (M.El (₁ am) , am , refl)
   in
   let σam : ∃ (Sub~ (keepw Γw σw (Elw Δw' Aw))) 
       σam =  (₁ σm M.^ (M.El (₁ am)))  , keepEl~ Γm Δm σm {Aw = Aw} am
   in
   let am[] : Σ (M.Tm (₁ Γm) M.U) (Tm~ (Tmw[] Aw Γw σw)) 
       am[] = _ , Tm[]~ Γm Δm σm {tw = Aw} am
   in
   let Δa~ : Con~ Δaw (₁ Δm M.▶ M.El (₁ am))
       Δa~ = Δm , Elam , refl
   in
    Ty[]~ (_ , Γm , (_ , am[] , refl) , refl) {Δw = Δaw} (_ , Δa~) σam Bm 
   -- let Bm[]~ = Ty[]~ (_ , Γm , (_ , am[] , refl) , refl) {Δw = Δaw} (_ , Δa~) σam Bm in
   --  (₁ Bm M.[ ₁ σm M.^ (M.El (₁ am)) ]T) , Bm[]~


-- -}


  -- TODO factoriser avec app
   -- σar = keep~ Γm Δm σm (M.El (₁ am) , am , refl)

Ty[]~ {Γ}{Γw}Γm {_}{Δw'}Δm  {σ} {σw} σm {.Up} {Uw Δ Δw} (_ , HoTT.lift refl) = HoTT.lift refl

Ty[]~ {Γ}{Γw}Γm {Δ}{Δw}Δm {σ} {σw} σm {.(ΠΠp (Elp _) _)} {Πw Δw' Aw Bw} (_ , am , Bm , refl) =
   -- this was factorized by Π-B[]~
   -- let Bm[]~ = Ty[]~ (_ , Γm , (_ , am[] , refl) , refl) {Δw = Δaw} (_ , Δa~) σam Bm in
   am[] ,
   -- Π-B[]~ Γm Δm Δw' σm am Bm
   -- ((₁ Bm M.[ ₁ σm M.^ (M.El (₁ am)) ]T) , Bm[]~)
   ((₁ Bm M.[ ₁ σm M.^ (M.El (₁ am)) ]T) , Π-B[]~ Γm Δm Δw' σm am Bm)
   ,
   refl
  where


    am[] : Σ (M.Tm (₁ Γm) M.U) (Tm~ (Tmw[] Aw Γw σw)) 
    am[] = _ , Tm[]~ Γm Δm σm {tw = Aw} am



Ty[]~ {Γ}{Γw}Γm {Δ}{Δw'}Δm  {σ} {σw} σm {.(Elp _)} {Elw Δw aw} (_ , am , refl) =
  (_ , ( Tm[]~ Γm Δm σm {tw = aw} am)) ,
  refl


-- Tm[]~ = {!!}
-- Tm[]~ {Γm}{Δm}{Γ}Γw{Δ}{σ}{σw}σm {Am}{A}{t}{tw} tm = {!!}

Tm[]~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ} {σw} σm {Am} {A} {.(V _)} {vw xw} tm = Var[]~ σm tm
Tm[]~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ} {σw} σm {_} {.(l-subT 0 u Bp)} {.(app t u)}
   {appw Δp Δw' Ap Aw Bp Bw t tw u uw}
   (_ , am , Bm , tm , um , refl , refl)
   rewrite l-sub[]T 0 Bp u σ
   =
    -- let Bm[]~ = Ty[]~ (_ , Γm , (_ , am[] , refl) , refl) {Δw = Δaw} (_ , Δa~) σam Bm in
    let tm[] = (₁ tm M.[ ₁ σm ]t) , Tm[]~ Γm Δm σm {tw = tw} tm in
    let um[] = (₁ um M.[ ₁ σm ]t) , Tm[]~ Γm Δm σm {tw = uw} um in
    am[] ,
    -- (_ , Bm[]~) ,
    (_ , Π-B[]~ Γm Δm Δw' σm am Bm) ,
    tm[] ,
    um[] ,
    M.app~eq₁ {Γ = ₁ Δm}{M.El (₁ am)}{₁ um} {₁ Bm},
    M.app~eq₂ {Γ = ₁ Δm}{₁ am} {₁ Bm}{₁ tm}
   
   where
    am[] : Σ (M.Tm (₁ Γm) M.U) (Tm~ (Tmw[] Aw Γw σw)) 
    am[] = _ , Tm[]~ Γm Δm σm {tw = Aw} am




-- keep~ {Γ}Γw{Δ}{σ}{σw}{Γm}{Δm}σm{A}{Aw}Am =
-- note that this keep~ is not defined by induction
keep~ : ∀ {Γp}{Γw : Conw Γp}(Γm : ∃ (Con~ Γw))
  {Δp}{Δw : Conw Δp}(Δm : ∃ (Con~ Δw))
  {σp}{σw : Subw Γp Δp σp} (σm : Σ (M.Sub (₁ Γm) (₁ Δm)) (Sub~ σw))
  {Ap}{Aw : Tyw Δp Ap}(Am : Σ (M.Ty (₁ Δm)) (Ty~ Aw)) →
  Sub~ (keepw Γw σw Aw)(₁ σm M.^ ₁ Am)

keep~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ}{σw}σm{A}{Aw}Am
  rewrite prop-has-all-paths (Sub-Con2w σw) Δw
  =
    Δm ,
    ((₁ σm M.∘ M.wk) , wkSub~ Γm σm ((₁ Am M.[ ₁ σm ]T) , Ty[]~ Γm Δm σm Am )
      -- (Tyw[] Aw Γw σw) (₁ Am M.[ ₁ σm ]T)
      ) ,
    Am ,
    (tr (M.Tm ((₁ Γm) M.▶ ₁ Am M.[ ₁ σm ]T)) (M.[][]T {A = ₁ Am}) M.vz , vz~) ,
    refl ,
    refl
  where
    vz~ : Var~
      (transport! (λ x → Varw (Γ ▶p (A [ σ ]T)) x 0) (liftT=wkS 0 σ A)
      (V0w Γ Γw (A [ σ ]T) (Tyw[] Aw Γw σw)))
      (tr (M.Tm ((₁ Γm) M.▶ ₁ Am M.[ ₁ σm ]T)) (M.[][]T {A = ₁ Am}) M.vz)

    vz~ rewrite (liftT=wkS 0 σ A) =
      Γm ,
      (_ , Ty[]~ Γm Δm σm Am) ,
      refl ,
       ! (M.[][]T {A = ₁ Am})  ,
      ≅↓ (↓≅  (from-transp (M.Tm (₁ Γm M.▶ ₁ Am M.[ ₁ σm ]T)) (M.[][]T {A = ₁ Am}) refl)  !≅)

id~ : ∀ {Γ}{Γw : Conw Γ}(Γm : ∃ (Con~ Γw)) → Sub~ (idpw Γw) (M.id {₁ Γm})
-- id~ {Γ}{Γw} Γm = {!!}
id~ {.∙p} {∙w} (_ , HoTT.lift refl) = refl , M.εη
id~ {(Γ ▶p A)} {▶w Γw Aw} (_ , Γm , Am , refl) =
  Γm ,
   (_ , wkSub~ Γm (M.id , id~ Γm) Am) ,
   Am ,
   (tm₁ , tm₂) ,
   refl ,
   e

   where
    tm₁ : M.Tm (₁ Γm M.▶ ₁ Am) (₁ Am M.[ M.id M.∘ M.wk ]T)
    tm₁ = transport! (λ s → M.Tm _ (₁ Am M.[ s ]T)) M.idl M.vz

    tm₁≅vz : tm₁ ≅ M.vz
    tm₁≅vz = ↓≅ ( from-transp! (λ s → M.Tm (₁ Γm M.▶ ₁ Am) (₁ Am M.[ s ]T)) M.idl refl )

    e : M.id ≡ (M.id M.∘ M.wk M.,s tm₁)
    e = ! ( ap (λ x → ₁ x M.,s ₂ x)
      (pair=  M.idl (≅↓ tm₁≅vz))
      ◾ M.πη)

    tm₂ :  Tm~
      (transport! (λ B → Tmw (Γ ▶p A) B (V 0))
      (wkT=wkS (idp ∣ Γ ∣) A ◾ ap wkT ([idp]T Aw))
      (vw (V0w Γ Γw A Aw)))
      tm₁
    tm₂ rewrite (wkT=wkS (idp ∣ Γ ∣) A ◾ ap wkT ([idp]T Aw)) =
      Γm ,
      Am ,
      refl ,
      ap (₁ Am M.[_]T) M.idl ,
      ≅↓ tm₁≅vz

<>~ : ∀{Γ}{Γw : Conw Γ}(Γm : ∃ (Con~ Γw))
    {A}{Aw : Tyw Γ A}(Am  : ∃ (Ty~ Aw {₁ Γm}))
    {t} {tw : Tmw Γ A t } (tm : Σ (M.Tm (₁ Γm) (₁ Am)) (Tm~ tw)) →
    Sub~ (<>w Γw Aw tw)  (M.< ₁ tm >)

-- <>~ {Γ}Γw{A}Aw{t}tw Γm Am tm = {!!}
<>~ {Γ}{Γw}Γm{A}{Aw}Am{t}{tw} tm =
  Γm ,
  (_ , id~ Γm) ,
  Am ,
  (tm₁ , tm₂) ,
  refl ,
  refl
  where
    tm₁ : M.Tm (₁ Γm) (₁ Am M.[ M.id ]T)
    tm₁ = transport! (M.Tm _) M.[id]T (₁ tm)

    tm₂ : Tm~ (transport! (λ A₁ → Tmw Γ A₁ t) ([idp]T Aw) tw) tm₁
    tm₂  rewrite ([idp]T Aw) =
      tr!-over (λ A₁ → Tm~ tw {Am = A₁})
        ( from-transp! (M.Tm (₁ Γm)) M.[id]T refl )
        (₂ tm)
  
