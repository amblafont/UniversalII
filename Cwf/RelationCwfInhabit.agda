{-# OPTIONS  --rewriting  #-}

-- proof Σ#~
open import Level 
-- open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import HoTT renaming ( _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
import ModelCwf as M
open import Syntax as S

module RelationCwfInhabit  where

open import RelationCwf
open import RelationCwfWeakening
open import RelationCwfSubstitution



  
ΣCon~ : {Γp : Conp}(Γw : Conw Γp) → ∃ (Con~ Γw)
ΣTy~ : ∀ {Γ }{Γw : Conw Γ}(Γm : ∃ (Con~ Γw)) {A}(Aw : Tyw Γ A) → ∃ (Ty~ Aw {₁ Γm})
ΣTm~ :
 ∀ {Γ } {Γw : Conw Γ}(Γm : ∃ (Con~ Γw))
  {A} {Aw : Tyw Γ A} (Am : ∃ (Ty~ Aw {₁ Γm})) 
  {t}(tw : Tmw Γ A t) →
  ∃ (Tm~ tw {₁ Γm}{₁ Am})
ΣVar~ : ∀ {Γ } {Γw : Conw Γ}(Γm : ∃ (Con~ Γw))
  {A} {Aw : Tyw Γ A} (Am : ∃ (Ty~ Aw {₁ Γm})) 
  {x}(xw : Varw Γ A x) →
  ∃ (Var~ xw {₁ Γm}{₁ Am})

-- ΣCon~ Γw = {!!}
ΣCon~ ∙w = _ , lift refl
ΣCon~ (▶w Γw Aw) =
  let Γm = ΣCon~ Γw in
  _ , Γm , ΣTy~ Γm Aw , refl

-- ΣTy~ Aw Γm = {!!}
ΣTy~ Γm (Uw Γp Γw') = _ , lift refl
ΣTy~ {Γw = Γw} Γm (Πw Γw' Aw Bw) =
  let am = ΣTm~ Γm {Aw = (Uw _ Γw)} (_ , lift refl) Aw  in
  _ , am  ,
   ΣTy~ {Γw = (▶w Γw (Elw Γw Aw))}
    (_ , Γm , (_ , am , refl) , refl)
      Bw  ,
      refl
ΣTy~ Γm (Elw Γw aw) = _ , ΣTm~ Γm { Aw = Uw _ Γw} (_ , lift refl) aw  , refl

-- ΣTm~ Γw' Aw' tw Γm Am = {!tw!}
ΣTm~ {Γw = Γw'} Γm {Aw = Aw'} Am (vw xw) = ΣVar~ Γm Am xw
ΣTm~ {Γw = Γw'} Γm' {Aw =  B[]w} Em (appw Γp Γw ap aw Bp Bw t tw u uw) =
    _ , am , Bm , tm , um , eE ,
    from-transp! _ _ refl 
  where
    Γm : ∃ (Con~ Γw)
    Γm = (₁ Γm' , tr (λ x → Con~ x _) (prop-has-all-paths _ _) (₂ Γm'))
    Γaw = (▶w Γw (Elw Γw aw))
    am = ΣTm~ Γm {Aw = (Uw Γp Γw)} (_ , lift refl) aw 

    Γam : ∃ (Con~ Γaw)
    Γam = _ , Γm , (_ , am , refl) , refl

    Bm = ΣTy~ {Γw = Γaw} Γam  Bw   
    tm = ΣTm~ Γm {Aw = (Πw Γw aw Bw)} (_ , am , Bm , refl) tw   
    um = ΣTm~ Γm {Aw = (Elw Γw aw) } (_ , am , refl) uw 

    <u>w : Subw Γp (Γp ▶p Elp ap) (< ∣ Γp ∣  ⊢ u >)
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


    eE = fst=  (prop-has-all-paths Em (_ , B[]~))
  

-- ΣVar~ Γw' Ew' xw Γm Em = {!xw!}
ΣVar~ {Γw = Γw'} Cm {Aw = wkEw} Em (V0w Γp Γw Ap Aw)   = 
  _ , Γm , Am , eC , eE ,
    from-transp! _ _ refl
  where
    Γm = ΣCon~ Γw
    Am = ΣTy~ Γm Aw
    ΓAm~ : ∀ Γw' → Con~ Γw' (₁ Γm M.▶ ₁ Am)
    ΓAm~ (▶w Γw' Aw') rewrite
      prop-has-all-paths Γw' Γw
      | prop-has-all-paths Aw' Aw
      = Γm , Am , refl
    eC = fst=  (prop-has-all-paths Cm (_ , ΓAm~ Γw'))
    wE~ : Ty~ wkEw
          (transport! M.Ty eC (₁ Am M.[ M.wk ]T))
    wE~ =
      tr!-over (λ a → Ty~ wkEw {a}) ( from-transp! M.Ty eC refl )
        (tr (λ w → Ty~ w (₁ Am M.[ M.wk {A = ₁ Am} ]T)) (prop-has-all-paths (wkTw Aw Aw) wkEw)
          (liftT~ Γm Am {Δ = ∙p}{ Γw } (M.∙t _ , HoTT.lift refl) Am))

    eE = from-transp! _ _
      -- (fst=  (prop-has-all-paths Em (_ , {!wE~!})))
      (fst=  (prop-has-all-paths Em (_ , wE~ )))

ΣVar~ {Γw = Cw'} Cm {Aw = wkEw} Em (VSw Γp Γw Ap Aw Bp Bw xp xw)  =
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
   eC = fst=  (prop-has-all-paths Cm (_ , ΓAm~ ))
   wE~ : Ty~ wkEw
    (transport! M.Ty eC (₁ Bm M.[ M.wk ]T))
    -- TODO: factoriser avec le cas Var~ précédent
   wE~ =
    tr!-over (λ a → Ty~ wkEw {a}) ( from-transp! M.Ty eC refl )
    (tr (λ w → Ty~ w (₁ Bm M.[ M.wk {A = ₁ Am} ]T)) (prop-has-all-paths (wkTw Aw Bw) wkEw)
      (liftT~ Γm Am {Δ = ∙p}{ Γw } (M.∙t _ , HoTT.lift refl) Bm))

   eE = from-transp! _ _
    (fst=  (prop-has-all-paths Em (_ , wE~)))


ΣSub~ : ∀ {Γ } {Γw : Conw Γ} (Γm : ∃ (Con~ Γw))
     {Δ} {Δw : Conw Δ} (Δm : ∃ (Con~ Δw))
     {σ}(σw : Subw Γ Δ σ) → ∃ (Sub~ σw {₁ Γm}{₁ Δm})

-- ΣSub~ {Γ}{Γw}Γm {C}{Cw}Cm σw = ?
ΣSub~ {Γ} {Γw} Γm {.∙p} {∙w} (_ , HoTT.lift refl) nilw =
  M.ε , refl , refl
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
     ΔA~ rewrite prop-has-all-paths Cw (▶w  Δw Aw) =
       Δm , Am , refl

     eC : ₁ Cm ≡ (₁ Δm M.▶ ₁ Am)
     eC = fst= (prop-has-all-paths Cm (_ , ΔA~ ))
