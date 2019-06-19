{-# OPTIONS  --rewriting  #-}

-- proof #~el
open import Level 
open import Hott renaming (_∙_ to _◾_ ;  transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
-- open import Lib2 using (_&_)
-- import Lib2 using (_⁻¹)
open import Syntax as S

module RelationCwfSubstitution {k : Level} where



import ModelCwf {k = k} as M
open import RelationCwf
open import RelationCwfWeakening {k = k}


Var[]~ : ∀ 
   {Γm Δm : M.Con}
   {Γ}{Δ}{σ}{σw : Γ ⊢ σ ⇒ Δ}(σm : ∃ (Sub~ σw {Γm}{Δm}))
   {Am : M.Ty Δm}
    {A}{x}{xw : Δ ⊢ x ∈v A} (xm : ∃ (Var~ xw {Δm}{ Am}))
  → Tm~ (Varw[] xw σw) {Γm} { Am M.[ ₁ σm ]T} (₁ xm M.[ ₁ σm ]t)

  -- Ty[]~ Γm Δm σm Am = {!!}

Var[]~ {Γm} {σw = ,sw  Γw' {σp = σ} σw Aw' {tp = t} tw}
  -- σm
  (sm , Δm' , σm' , Am'' , tm' , eC , eS)
   {xw = V0w Γw {Ap} Aw} (xm , Δm , Am' , refl , refl , refl)
  rewrite wk[,]T Ap t σ
  | prop-has-all-paths Γw' Γw
  | prop-path (ConP Γw) Δm' Δm

  | prop-has-all-paths Aw' Aw
  | prop-path (TyP Aw _) Am'' Am'

  | uip eC refl
  | eS
    =
      tr!-over (λ Em → Tm~ tw {Am = Em}) (M.vz[,] (₁ σm') (₁ Am') (₁ tm')) (₂ tm')

Var[]~ {Γm} {σw = ,sw Δw' {σp = σ} σw Aw' {tp = t} tw}
  (sm , Δm' , σm , Am'' , tm , eC , eS)
  {Am} {xw = VSw Δw Aw {Bp} Bw xw}
  (_ , Δm , Am' , Bm , xm , refl , refl , refl  )
  rewrite wk[,]T Bp t σ
  | prop-has-all-paths Δw' Δw
  | prop-path (ConP Δw) Δm' Δm

  | prop-has-all-paths Aw' Aw
  | prop-path (TyP Aw _) Am'' Am'

  | uip eC refl
  | eS
  =
    tr!-over (λ Em → Tm~ (Varw[] xw σw) {Am = Em})
      {x = M._[_]T (M._[_]T (₁ Bm) (M.π₁ M.id)) (M._,s_ (₁ σm) (₁ tm))}
      {y = M._[_]T (₁ Bm) (₁ σm)}
      {p = M.wk[]T {σ  = ₁ σm} {t = ₁ tm} {B = ₁ Bm}}
      (M.wk[]t {σ = ₁ σm}{t = ₁ tm}{B = ₁ Bm}{b = ₁ xm})
      xm[]~
    -- {! tr!-over (λ Em → Tm~ (Varw[] xw σw) {Am = Em}) {p = M.wk[]T} M.wk[]t xm[]~ !}
    where
      xm[]~ : Tm~ (Varw[] xw σw) (₁ xm M.[ ₁ σm ]t)
      xm[]~ = Var[]~ σm xm

    -- (λ Em → Tm~ (Varw[] xw σw) {Am = Em}) {p = M.wk[]T}M.wk[]t
    --   (Var[]~ σm xm)

Tm[]~ : ∀ 
      {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
      {Δ}{Δw : Δ ⊢}(Δm : ∃ (Con~ Δw))
      {σ}{σw : Γ ⊢ σ ⇒ Δ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
      {Am : M.Ty (₁ Δm)}
      {A}{t}{tw : Δ ⊢ t ∈ A} (tm : ∃ (Tm~ tw {₁ Δm}{ Am}))
      → Tm~ (Tmw[] tw Γw σw) {₁ Γm} { Am M.[ ₁ σm ]T} (₁ tm M.[ ₁ σm ]t)

Ty[]~ : ∀ 
   {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
   {Δ}{Δw : Δ ⊢}(Δm : ∃ (Con~ Δw))
  {σ}{σw : Γ ⊢ σ ⇒ Δ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
  {A}{Aw : Δ ⊢ A} (Am : ∃ (Ty~ Aw {₁ Δm}))
  → Ty~ (Tyw[] Aw Γw σw) {₁ Γm} (₁ Am M.[ ₁ σm ]T)
  -- Ty[]~ {Γm}{Δm}{Γ}Γw{Δ}{σ}{σw}  σm{T}{Tw}Tm  = {!!}

keepEl~ : ∀ {Γp}{Γw : Γp ⊢}(Γm : ∃ (Con~ Γw))
  {Δp}{Δw : Δp ⊢}(Δm : ∃ (Con~ Δw))
  {σp}{σw : Γp ⊢ σp ⇒ Δp} (σm : Σ (M.Sub (₁ Γm) (₁ Δm)) (Sub~ σw))
  {Ap}{Aw : Δp ⊢ Ap ∈ Up}(Am : Σ (M.Tm (₁ Δm) M.U) (Tm~ Aw)) →
  Sub~ (keepw Γw Δw σw  Aw)(₁ σm M.^ M.El (₁ Am))

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
      (transport! (λ x → (Γ ▶p Elp (A [ σ ]t)) ⊢ 0 ∈v x) (liftT=wkS 0 σ (Elp A))
      (V0w Γw  (Tyw[] (Elw Δw Aw) Γw σw)))
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
  ∀ {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
  {Δ}{Δw : Δ ⊢}(Δm : ∃ (Con~ Δw)) (Δw' : Δ ⊢)
  {σ}{σw : Γ ⊢ σ ⇒ Δ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
  {A}{Aw : Δ ⊢ A ∈ Up} (am : ∃ (Tm~ Aw {₁ Δm}{M.U}))
  {B}{Bw : (Δ ▶p Elp A) ⊢ B} (Bm : ∃ (Ty~ Bw {₁ Δm M.▶ M.El (₁ am) }))
  →
  -- Σ (M.Ty (₁ Γm M.▶ M.El (₁ am M.[ ₁ σm ]t)))
    (Ty~ (Tyw[] Bw (▶w Γw (Elw Γw (Tmw[] Aw Γw σw))) (keepw Γw Δw' σw  Aw)))
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
   let σam : ∃ (Sub~ (keepw Γw Δw' σw Aw)) 
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

Ty[]~ {Γ}{Γw}Γm {_}{Δw'}Δm  {σ} {σw} σm {.Up} {Uw Δw} (_ , Level.lift refl) = Level.lift refl

Ty[]~ {Γ}{Γw}Γm {Δ}{Δw}Δm {σ} {σw} σm {.(ΠΠp ( _) _)} {Πw Δw' Aw Bw} (_ , am , Bm , refl) =
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

Ty[]~ {Γ}{Γw}Γm {Δ}{Δw}Δm {σ} {σw} σm {_} {ΠNIw Δw'  Bw} (_ , Bm , refl) =
 (λ a → _ , Ty[]~ Γm Δm σm (Bm a)) ,
   refl


Ty[]~ {Γ}{Γw}Γm {Δ}{Δw'}Δm  {σ} {σw} σm {.(Elp _)} {Elw Δw aw} (_ , am , refl) =
  (_ , ( Tm[]~ Γm Δm σm {tw = aw} am)) ,
  refl


-- Tm[]~ = {!!}
-- Tm[]~ {Γm}{Δm}{Γ}Γw{Δ}{σ}{σw}σm {Am}{A}{t}{tw} tm = {!!}

Tm[]~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ} {σw} σm {Am} {A} {.(V _)} {vw xw} tm = Var[]~ σm tm
Tm[]~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ} {σw} σm {_} {_} {_}
   {appw Δw' Aw {Bp} Bw tw {u} uw}
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
     M.[<>][]T {Γ = ₁ Δm}{M.El (₁ am)}{₁ um} {₁ Bm} 
    ,
     M.$[] {Γ = ₁ Δm}{_}{₁ am} {₁ Bm}{₁ tm} 
   
   where
    am[] : Σ (M.Tm (₁ Γm) M.U) (Tm~ (Tmw[] Aw Γw σw)) 
    am[] = _ , Tm[]~ Γm Δm σm {tw = Aw} am

Tm[]~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ} {σw} σm {_} {_} {_} {appNIw Δw'  Bw tw u}
   (_ , Bm , tm , refl , refl)
   =
   (λ a → _ , Ty[]~ Γm Δm σm (Bm a)) ,
      (_ ,  Tm[]~ Γm Δm σm {tw = tw} tm ) ,
     refl , refl

Tm[]~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ} {σw} σm {_} {_} {_} {appInfw Δw'  Bw tw u}
   (_ , Bm , tm , refl , refl)
   =
   (λ a → _ , Tm[]~ Γm Δm σm {tw = Bw a} (Bm a)) ,
     (_ ,  Tm[]~ Γm Δm σm {tw = tw} tm ) ,
       refl , refl


Tm[]~ {Γ}{Γw}Γm {Δ}{Δw}Δm {σ} {σw} σm {_}{_}{_} {ΠInfw Δw'  Bw}
  (_ , Bm , refl , refl) =
  (λ a → _ , Tm[]~ Γm Δm σm {tw = Bw a} (Bm a)) ,
    refl , refl

-- keep~ {Γ}Γw{Δ}{σ}{σw}{Γm}{Δm}σm{A}{Aw}Am =
-- note that this keep~ is not defined by induction
keep~ : ∀ {Γp}{Γw : Γp ⊢}(Γm : ∃ (Con~ Γw))
  {Δp}{Δw : Δp ⊢}(Δm : ∃ (Con~ Δw))
  {σp}{σw : Γp ⊢ σp ⇒ Δp} (σm : Σ (M.Sub (₁ Γm) (₁ Δm)) (Sub~ σw))
  {Ap}{Aw : Δp ⊢ Ap ∈ Up}(Am : Σ (M.Tm (₁ Δm) M.U) (Tm~ Aw)) →
  Sub~ (keepw Γw Δw σw Aw)(₁ σm M.^ (M.El (₁ Am)))

keep~ {Γ}{Γw}Γm{Δ}{Δw}Δm{σ}{σw}σm{A}{Aw}Am
  rewrite prop-has-all-paths (Sub-Con2w σw) Δw
  =
    Δm ,
    ((₁ σm M.∘ M.wk) , wkSub~ Γm σm ((M.El (₁ Am) M.[ ₁ σm ]T) ,  (_ , Tm[]~ Γm Δm σm {tw = Aw} Am) , refl )
    -- Tm[]~ Γm Δm σm Am )
      -- (Tyw[] Aw Γw σw) (₁ Am M.[ ₁ σm ]T)
      ) ,
    (M.El (₁ Am) , Am , refl) ,
    (tr (M.Tm ((₁ Γm) M.▶ M.El (₁ Am) M.[ ₁ σm ]T)) (M.[][]T {A = M.El (₁ Am)}) M.vz , vz~) ,
    refl ,
    refl
  where
    vz~ : Var~
      (transport! (λ x → (Γ ▶p (Elp A [ σ ]T)) ⊢ 0 ∈v x) (liftT=wkS 0 σ (Elp A))
      (V0w Γw  (Elw Γw (Tmw[] Aw Γw σw))))
      (tr (M.Tm ((₁ Γm) M.▶ M.El (₁ Am) M.[ ₁ σm ]T)) (M.[][]T {A = M.El (₁ Am)}) M.vz)

    vz~ rewrite (liftt=wkS 0 σ A) =
      Γm ,
      ((_ , (_ , Tm[]~ Γm Δm σm {tw = Aw} Am) , refl)) ,
      refl ,
       ! (M.[][]T {A = M.El (₁ Am)})  ,
      ≅↓ (↓≅  (from-transp (M.Tm (₁ Γm M.▶ M.El (₁ Am) M.[ ₁ σm ]T)) (M.[][]T {A = M.El (₁ Am)}) refl)  !≅)

id~ : ∀ {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw)) → Sub~ (idpw Γw) (M.id {₁ Γm})
-- id~ {Γ}{Γw} Γm = {!!}
id~ {.∙p} {∙w} (_ , Level.lift refl) = refl , Level.lift M.εη
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
      (transport! (λ B → (Γ ▶p A) ⊢ V 0 ∈ B)
      (wkT=wkS (idp ∣ Γ ∣) A ◾ ap wkT ([idp]T Aw))
      (vw (V0w Γw Aw)))
      tm₁
    tm₂ rewrite (wkT=wkS (idp ∣ Γ ∣) A ◾ ap wkT ([idp]T Aw)) =
      Γm ,
      Am ,
      refl ,
      ap (₁ Am M.[_]T) M.idl ,
      ≅↓ tm₁≅vz

<>~ : ∀{Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
    {A}{Aw : Γ ⊢ A}(Am  : ∃ (Ty~ Aw {₁ Γm}))
    {t} {tw : Γ ⊢ t ∈ A } (tm : Σ (M.Tm (₁ Γm) (₁ Am)) (Tm~ tw)) →
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

    tm₂ : Tm~ (transport! (λ A₁ → Γ ⊢ t ∈ A₁) ([idp]T Aw) tw) tm₁
    tm₂  rewrite ([idp]T Aw) =
      tr!-over (λ A₁ → Tm~ tw {Am = A₁})
        ( from-transp! (M.Tm (₁ Γm)) M.[id]T refl )
        (₂ tm)


-- not needed for the inhabitation
∘~ : ∀{Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
      {Δ}{Δw : Δ ⊢}(Δm : ∃ (Con~ Δw))
      {σ}{σw : Γ ⊢ σ ⇒ Δ}(σm : ∃ (Sub~ σw {₁ Γm}{₁ Δm}))
      {Y}{Yw : Y ⊢}(Ym : ∃ (Con~ Yw))
      {δ}{δw : Y ⊢ δ ⇒ Γ}(δm : ∃ (Sub~ δw {₁ Ym}{₁ Γm}))
      →
      Sub~ {σ = σ ∘p δ} (∘w σw Yw δw) {₁ Ym}{₁ Δm} (₁ σm M.∘ ₁ δm)

-- ∘~ {Γ}{Γw}Γm {Δ}{Δw}Δm {σ}{σw}σm {Y}{Yw}Ym {δ}{δw}δm = {!σw!}
∘~ {Γ} {Γw} Γm {.∙p} {Δw} Δm {.nil} {nilw} (σm , eC , es) {Y} {Yw} Ym {δ} {δw} δm =
    eC , Level.lift (from-transp _ _ M.εη )
    -- _∙'ᵈ_ {p' = refl} {!M.εη!} M.εη
∘~ {Γ} {Γw} Γm {.(_ ▶p _)} {Δw'} (_ , Δ~') {_} {,sw Δw {σp = σp}σw {Ap = Ap}Aw {tp = tp}tw}
  (_ , Δm' , σm , Am , tm , refl , refl)
  {Y} {Yw} Ym {δ} {δw} δm =
  Δm' ,
  ((₁ σm M.∘ ₁ δm), ∘~ Γm Δm' σm Ym δm) ,
  Am ,
  (tr (M.Tm _) (M.[][]T {A = ₁ Am}) (₁ tm M.[ ₁ δm ]t) , t[]~) ,
  refl ,
  M.,∘ (from-transp _ _ refl)
  where
    t[]~ : Tm~
      (tr (λ A → Y ⊢ (tp [ δ ]t) ∈ A) (! ([∘]T Ap σp δ))
       (Tmw[] tw Yw δw))
      (tr (M.Tm (₁ Ym)) (M.[][]T {A = ₁ Am}{σ = ₁ δm}{δ = ₁ σm}) (₁ tm M.[ ₁ δm ]t))
    t[]~
      rewrite ( ([∘]T Ap σp δ))
      = tr2 (λ A → Tm~ (Tmw[] tw Yw δw) {Am = A}) (M.[][]T{A = ₁ Am}) refl
          (Tm[]~ Ym Γm δm {Am = ₁ Am M.[ ₁ σm ]T}{tw = tw} tm )

