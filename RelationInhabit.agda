{-# OPTIONS  --rewriting  #-}

-- proof Σ#~
open import Level
-- open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import EqLib renaming ( _∙_ to _◾_ ; transport to tr ; fst to ₁ ; snd to ₂)
open import Lib

module RelationInhabit {k : Level} where

import ModelRew {k} as M
open import Syntax {k} as S
open import Relation {k = k}
open import RelationWeakening {k = k}
open import RelationSubstitution {k = k}



Σ▶El~ : ∀ {Γ}{Γw : Γ ⊢} (Γm : ∃ (Con~ Γw))
   {A}
   -- I don't know why this is not inferred..
   (Aw : Γ ⊢ A ∈ Up)(Am : ∃ (Tm~ Aw {₁ Γm}{M.U }))
   → ∃ (Con~ (▶w Γw (Elw Γw Aw)))
Σ▶El~ {Γ}{Γw}Γm{A}Aw Am = Σ▶~ Γm {Aw = Elw Γw Aw}(_ , Am , refl)



ΣCon~ : {Γp : Conp}(Γw : Γp ⊢) → ∃ (Con~ Γw)
ΣTy~ : ∀ {Γ }{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw)) {A}(Aw : Γ ⊢ A) → ∃ (Ty~ Aw {₁ Γm})
ΣTm~ :
 ∀ {Γ } {Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
  {A} {Aw : Γ ⊢ A} (Am : ∃ (Ty~ Aw {₁ Γm}))
  {t}(tw : Γ ⊢ t ∈ A) →
  ∃ (Tm~ tw {₁ Γm}{₁ Am})
ΣVar~ : ∀ {Γ } {Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
  {A} {Aw : Γ ⊢ A} (Am : ∃ (Ty~ Aw {₁ Γm}))
  {x}(xw : Γ ⊢ x ∈v A) →
  ∃ (Var~ xw {₁ Γm}{₁ Am})

-- ΣCon~ Γw = {!!}
ΣCon~ ∙w = _ , lift refl
ΣCon~ (▶w Γw Aw) =
  let Γm = ΣCon~ Γw in
  Σ▶~ Γm (ΣTy~ Γm Aw)

-- ΣTy~ Aw Γm = {!!}
ΣTy~ Γm (Uw  Γw') = _ , lift refl
ΣTy~ {Γw = Γw} Γm (Πw Γw' Aw Bw) =
  let am = ΣTm~ Γm {Aw = (Uw Γw)} (_ , lift refl) Aw  in
  _ , am  ,
   ΣTy~ {Γw = (▶w Γw (Elw Γw Aw))}
    ( Σ▶El~ Γm  Aw am )
      Bw  ,
      refl
ΣTy~ {Γw = Γw} Γm (ΠNIw Γw' Bw) =
  _ , (λ a → ΣTy~ Γm (Bw a)) , refl
  -- {!_!} ,
  -- {!!}

ΣTy~ Γm (Elw Γw aw) = _ , ΣTm~ Γm { Aw = Uw Γw} (_ , lift refl) aw  , refl

-- ΣTm~ Γw' Aw' tw Γm Am = {!tw!}
ΣTm~ {Γw = Γw'} Γm {Aw = Aw'} Am (vw xw) = ΣVar~ Γm Am xw
ΣTm~ {Γw = Γw'} Γm' {Aw =  B[]w} Em (appw {Γp} Γw {ap} aw Bw tw {u} uw) =
    _ , am , Bm , tm , um , eE ,
    from-transp! _ _ refl
  where
    Γm : ∃ (Con~ Γw)
    Γm = (₁ Γm' , tr (λ x → Con~ x _) (prop-has-all-paths _ _) (₂ Γm'))
    Γaw = (▶w Γw (Elw Γw aw))
    am = ΣTm~ Γm {Aw = (Uw Γw)} (_ , lift refl) aw

    Γam : ∃ (Con~ Γaw)
    -- Γam = _ , Γm , (_ , am , refl) , refl
    Γam = Σ▶El~ Γm aw am

    Bm = ΣTy~ {Γw = Γaw} Γam  Bw
    tm = ΣTm~ Γm {Aw = (Πw Γw aw Bw)} (_ , am , Bm , refl) tw
    um = ΣTm~ Γm {Aw = (Elw Γw aw) } (_ , am , refl) uw

    <u>w : Γp ⊢  (< ∣ Γp ∣  ⊢ u >) ⇒ (Γp ▶p Elp ap)
    <u>w = (<>w Γw (Elw Γw aw) uw)

    <u>~ : (Sub~ <u>w {₁ Γm}{₁ Γam} (M.< ₁ um >))
    <u>~ =
      -- {!<>~ Γm (_ , ?) um !}
       <>~ Γm {Aw = Elw Γw aw}(_ , am , refl) um
    -- on a besoin que les substitutions préservent le typage
    B[]~ : Ty~ B[]w (₁ Bm M.[ M.< ₁ um > ]T)
    B[]~
      rewrite
         ! ( [<>]T Bw u )
         | prop-has-all-paths B[]w (Tyw[] Bw Γw <u>w)
           -- {!Tyw[] Bw Γw' ?!}
        = Ty[]~ Γm {Δw = Γaw} Γam {σw  = <u>w} (M.< ₁ um > , <u>~ ) Bm


    eE = fst=  (prop-path (TyP _ _) Em (_ , B[]~))

ΣTm~ {Γw = Γw} Γm' {Aw =  B[]w} Em (appNIw Γw' Bw tw u) =
-- ΣTm~ {Γw = Γw'} Γm' {Aw =  B[]w} Em (appNIw Γw Bw tw u) =
  _ ,
  Bm ,
  tm  ,
  eE ,
  from-transp! _ _ refl
 where
    Γm : ∃ (Con~ Γw)
    Γm = Γm'
    -- Γm = (₁ Γm' , tr (λ x → Con~ x _) (prop-has-all-paths _ _) (₂ Γm'))

    Bm = λ a → ΣTy~ Γm (Bw a)
    tm = ΣTm~ Γm {Aw = (ΠNIw Γw Bw)} (_ , Bm , refl) tw

    B[]~ : Ty~ B[]w (₁ (Bm u))
    B[]~
      rewrite
         -- ! ( [<>]T Bw u )
          prop-has-all-paths B[]w (Bw u)
      -- = {!₂ (  Bm u )!}
      = ₂ (  Bm u )
    eE =  fst=  (prop-path (TyP _ _) Em (_ , B[]~))

{- INF
ΣTm~ {Γw = Γw} Γm' {Aw = Elw Γw'' aw} (_ , am , refl) (appInfw Γw' Bw tw u) =
  _ ,
  Bm ,
  tm ,
  -- {!eB am!} ,
  eB am ,
  from-transp! _ (eB am) refl
  -- from-transp _ _ refl

 where
    Γm : ∃ (Con~ Γw)
    Γm = Γm'
    -- Γm = (₁ Γm' , tr (λ x → Con~ x _) (prop-has-all-paths _ _) (₂ Γm'))

    Bm = λ a → ΣTm~ Γm {Aw = Uw  Γw'}(_ , lift refl) (Bw a)
    tm = ΣTm~ Γm {Aw = Elw Γw (ΠInfw Γw Bw)} (_ , (_ , Bm , refl , refl) , refl ) tw
    eB : (am' : Σ (M.Tm (₁ Γm') M.U) (Tm~ aw))  → M.El (₁ am') ≡ M.El (₁ (Bm u))
    eB rewrite prop-has-all-paths aw (Bw u) = λ am' →
       ap M.El ( fst= (prop-has-all-paths  {{ TmP (Bw u) _ }} am' (Bm u)) )


ΣTm~ {Γw = Γw} Γm' {Aw = Uw Γw''} (_ , lift refl) (ΠInfw Γw' Bw) =
  _ , (λ a → ΣTm~ Γm' {Aw = Uw Γw'} (_ , lift refl) (Bw a)  ) , refl , refl
-}

-- ΣVar~ Γw' Ew' xw Γm Em = {!xw!}
ΣVar~ {Γw = Γw'} Cm {Aw = wkEw} Em (V0w Γw Aw)   =
  _ , Γm , Am , eC , eE ,
    from-transp! _ _ refl
  where
    Γm = ΣCon~ Γw
    Am = ΣTy~ Γm Aw
    ΓAm~ : Con~ Γw' (₁ Γm M.▶ ₁ Am)
    ΓAm~  rewrite prop-has-all-paths Γw' (▶w Γw Aw)
      = Γm , Am , refl
    eC = fst=  (prop-path (ConP _) Cm (_ , ΓAm~ ))
    wE~ : Ty~ wkEw
          (transport! M.Ty eC (₁ Am M.[ M.wk ]T))

    eConPh = ap (λ s → Ty~ _ (₁ Am M.[ s ]T)) (wkTelSᵐ∙= _ _)
    wE~ =
      tr!-over (λ a → Ty~ wkEw {a}) ( from-transp! M.Ty eC refl )
        (tr (λ w → Ty~ w (₁ Am M.[ M.wk {A = ₁ Am} ]T)) (prop-has-all-paths (wkTw Aw Aw) wkEw)
          (coe eConPh (liftT~ Γm Am {Δ = ∙p}{ Γw } Γm Am) ))
          -- {! liftT~ Γm Am {Δ = ∙p}{ Γw } {! M.∙t _ , Level.lift refl !} Am !})

    eE = from-transp! _ _
      -- (fst=  (prop-has-all-paths Em (_ , {!wE~!})))
      (fst=  (prop-path (TyP _ _) Em (_ , wE~ )))

ΣVar~ {Γw = Cw'} Cm {Aw = wkEw} Em (VSw Γw Aw Bw xw)  =
  _ , Γm , Am , Bm , xm , eC , eE ,
  from-transp! _ _ refl

  where
   Γm = ΣCon~ Γw
   Am = ΣTy~  Γm Aw
   Bm = ΣTy~  Γm Bw
   xm = ΣVar~ Γm Bm xw
   ΓAm~ : Con~ Cw' (₁ Γm M.▶ ₁ Am)
   ΓAm~ rewrite prop-has-all-paths Cw' (▶w Γw Aw)
    =  Γm , Am , refl
   eC = fst=  (prop-path (ConP _) Cm (_ , ΓAm~ ))
   wE~ : Ty~ wkEw
    (transport! M.Ty eC (₁ Bm M.[ M.wk ]T))
   eConPh = ap (λ s → Ty~ _ (₁ Bm M.[ s ]T)) (wkTelSᵐ∙= _ _)
    -- TODO: factoriser avec le cas Var~ précédent
   wE~ =
    tr!-over (λ a → Ty~ wkEw {a}) ( from-transp! M.Ty eC refl )
    (tr (λ w → Ty~ w (₁ Bm M.[ M.wk {A = ₁ Am} ]T)) (prop-has-all-paths (wkTw Aw Bw) wkEw)
      ( coe eConPh (liftT~ Γm Am {Δ = ∙p}{ Γw } Γm Bm) ))

   eE = from-transp! _ _
    (fst=  (prop-path (TyP _ _) Em (_ , wE~)))


ΣSub~ : ∀ {Γ } {Γw : Γ ⊢} (Γm : ∃ (Con~ Γw))
     {Δ} {Δw : Δ ⊢} (Δm : ∃ (Con~ Δw))
     {σ}(σw : Γ ⊢ σ ⇒ Δ) → ∃ (Sub~ σw {₁ Γm}{₁ Δm})

-- ΣSub~ {Γ}{Γw}Γm {C}{Cw}Cm σw = ?
ΣSub~ {Γ} {Γw} Γm {.∙p} {∙w} (_ , Level.lift refl) nilw =
  M.ε , refl , Level.lift refl
ΣSub~ {Γ} {Γw} Γm {.(_ ▶p _)} {Cw} Cm (,sw {Δp = Δp} Δw {σp = σ}σw{Ap = A} Aw{tp = t} tw) =
  _ ,
   Δm ,
   σm ,
   Am ,
   ΣTm~ Γm {Aw = Tyw[] Aw Γw σw} A[]m tw    ,
   eC ,
     from-transp! (M.Sub (₁ Γm)) eC refl
   where
     Δm = ΣCon~ Δw
     Am = ΣTy~ Δm Aw
     σm = ΣSub~ Γm Δm σw

     A[]~ :  Ty~ (Tyw[] Aw Γw σw) (₁ Am M.[ ₁ σm ]T)
     A[]~ = Ty[]~ Γm Δm σm Am

     A[]m = (₁ Am M.[ ₁ σm ]T) , A[]~

     -- ΔA~ : ∀ (Cw' : Conw (Δp ▶p A)) → Con~ Cw'  (₁ Δm M.▶ ₁ Am)
     ΔA~  : Con~ Cw  (₁ Δm M.▶ ₁ Am)
     ΔA~ =
      -- prop-has-all-paths Cw (▶w  Δw Aw)
      tr (λ w → Con~ w (₁ Δm M.▶ ₁ Am))
       (prop-has-all-paths (▶w Δw Aw) Cw)
        (Δm , Am , refl)


     eC : ₁ Cm ≡ (₁ Δm M.▶ ₁ Am)
     eC = fst= (prop-path (ConP _) Cm (_ , ΔA~ ))
