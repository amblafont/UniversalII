-- In this file, we prove that the postulated morphism satisfies the relation
{-# OPTIONS  --rewriting   #-}
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import ModelRecord
open import monlib
open import Syntax
open import SyntaxIsRecord
open import SyntaxIsRecord2
open import ModelRewIsRecord 
open import ModelRewIsRecord2
open import ModelMorphism
import Model
open import Relation
open import RelationProp
open import RelationInhabit
open import RelWeakening
open import RelSubst
-- open import Data.String


module ModelMorRewRel {l} where
  open import ModelMorRew {l}


  Conᴹ~ : ∀ {Γp}Γw → let Γ = Γp , Γw in Con~' _ (₂ Γ) (Conᴹ Γ)
  Tyᴹ~ : ∀ (Γ : S1.Con){Ap}Aw → let A = Ap , Aw in Ty~' _ _ (₂ A) (Conᴹ Γ)(Tyᴹ {Γ} A)
  Tmᴹ~ : ∀ (Γ : S1.Con)(A : S1.Ty Γ)
    {tp}tw →
    -- (t : S1.Tm Γ A)
    let t = tp , tw in
     Tm~' _ _  _ (₂ t) (Conᴹ Γ)(Tyᴹ {Γ} A) (Tmᴹ {Γ} {A} t)
  Varᴹ~ : ∀ (Γ : S1.Con)(A : S1.Ty Γ)
    {xp : ℕ} (xw : Varw (₁ Γ)(₁ A) xp)
    -- (x : Σ _ (Varw (₁ Γ) (₁ A)))
    →
    Var~' _ _  _ xw (Conᴹ Γ)(Tyᴹ {Γ} A) (Tmᴹ {Γ} {A} (_ , vw xw))

  Conᴹ~ {.∙p} ∙w = refl
  Conᴹ~ {(Γp ▶p _)}  (▶w Γw Aw) =
    -- a where clause is a problem for the temrination checker
    let Γr = Conᴹ~ Γw  in
    let Ar = Tyᴹ~  (Γp , Γw)  Aw in
    (_ , Γr) ,
    (_ , Ar) ,
    refl 

  -- this rewrite is necessary so that the rewrite rule applies
  Tyᴹ~ Γ {.Up}  (Uw _ Γw) rewrite prop-has-all-paths Γw (₂ Γ) = refl
  Tyᴹ~ Γ {.(ΠΠp (Elp _) _)} ( Πw Γw Aw Bw)
    rewrite prop-has-all-paths Γw (₂ Γ) 
    =
    let Ar = Tmᴹ~ Γ (S1.U Γ)  Aw in
    let Br = Tyᴹ~ (Γ S1.▶ (S1.El Γ (_ , Aw)))  Bw in
      (_ , Ar) ,
       (_ , Br) ,
       refl
      
  Tyᴹ~ (Γp , Γw') {.(Elp _)} ( Elw Γw aw) 
    rewrite prop-has-all-paths Γw' Γw
    =
    let Γ = Γp , Γw in
     (_ , Tmᴹ~ Γ (S1.U Γ) aw) , refl


  Tmᴹ~ Γ A {.(V _)}  (vw xw) =  Varᴹ~ Γ A xw 
  Tmᴹ~ (Γp , Γw') (.(l-subT 0 up Bp) , sBw) {.(app t up)}  (appw .Γp Γw Ap Aw Bp Bw t tw up uw) 
    rewrite prop-has-all-paths Γw' Γw
    | prop-has-all-paths sBw (subTw {Δp = ∙p} uw Bw)
    =
    let Γ = (Γp , Γw) in
    let A = (Ap , Aw) in
    let B = (Bp , Bw) in
    (_ , Tmᴹ~ Γ (S1.U Γ) Aw) ,
    (_ , Tyᴹ~ (Γ S1.▶ (S1.El Γ A)) Bw) ,
    (_ , Tmᴹ~ Γ (S1.ΠΠ Γ A B) tw) ,
    (_ , Tmᴹ~ Γ (S1.El Γ A) uw) ,
      helper
     
     -- (λ uu → pair=
     --  {!e-subT uu!}
     --  {!!})
     --  unit'
     where
      Γ = (Γp , Γw)
      A = (Ap , Aw)
      B = (Bp , Bw)
      u = (up , uw)
      e-subT = λ uu → subTᴹ syntax2 m2 mor1 uu {_ , Γw}{S1.El Γ A}{u}{B}

      statment = _
      helper : statment
      helper2 : ⊤' → statment

      helper = helper2 unit'

      helper2 uu =
        pair=
        (e-subT uu)
        (from-transp! _ _
          (appᴹ uu Γ A B (_ , tw) u 
            ◾
            transport-! _ (e-subT uu) _)
          )

  Varᴹ~ (.(Γp ▶p Ap) ,  ▶w Γw Aw) (.(liftT 0 Ap) , lAw) {.0} (V0w Γp Γw' Ap Aw')
    rewrite prop-has-all-paths Γw Γw'
    | prop-has-all-paths Aw Aw'
    | prop-has-all-paths lAw (wkTw Aw' Aw')
    =
     
    let Γ = (Γp , Γw') in
    let Γr = Conᴹ~ Γw'  in
    let Ar = Tyᴹ~ Γ Aw' in
     (_ , Γr) ,
     ( _ , Ar) ,
     
     ₁mk-triple=
      e-wkT
      (from-transp! _ e-wkT (transport-! _ e-wkT _))

         

    where
      e-wkT = wkTᴹ syntax2 m2 mor1 {Γ = (Γp , Γw')}{(Ap , Aw')}{(Ap , Aw')}
       -- {!refl!}
     
  Varᴹ~ (.(Γp ▶p Ap) , ▶w Γw Aw ) (.(liftT 0 Bp) , lBw) {.(S xp)}( VSw Γp Γw' Ap Aw' Bp Bw xp xw) 
    rewrite prop-has-all-paths Γw Γw'
    | prop-has-all-paths Aw Aw'
    | prop-has-all-paths lBw (wkTw Aw' Bw)
    =
     
    let Γ = (Γp , Γw') in
    let A = (Ap , Aw') in
    let B = (Bp , Bw) in
    let liftx =
          (N.liftt (Conᴹ (Γp , Γw')) (N.∙t (Conᴹ (Γp , Γw')))
          (Tyᴹ (Ap , Aw')) (Tyᴹ (Bp , Bw)) (Tmᴹ (V xp , vw xw)))
    in
    let liftx' =
          (MM.liftt (Conᴹ (Γp , Γw')) (N.∙t (Conᴹ (Γp , Γw')))
            (Tyᴹ (Ap , Aw'))
            (MM.tr-Ty (^^ᴹ (Γp , Γw') (∙p , Γw')) (Tyᴹ (Bp , Bw)))
          (MM.tr2-Tm (^^ᴹ (Γp , Γw') (∙p , Γw')) (Tmᴹ (V xp , vw xw))))
    in
    let eqe =
          (ap
          (λ x →
          N.liftT (Conᴹ (Γp , Γw')) (N.∙t (Conᴹ (Γp , Γw'))) (Tyᴹ (Ap , Aw'))
          (MM.tr-Ty x (Tyᴹ (Bp , Bw))))
          {x = (^^ᴹ (Γp , Γw') (∙p , Γw'))}
          {y = refl} (uip _ _))
    in

     (_ , Conᴹ~ Γw') ,
    (_ , Tyᴹ~ Γ Aw') ,
    (_ , Tyᴹ~ Γ Bw) ,
    (_ , Varᴹ~ Γ B xw) ,
    ₁mk-triple= e-wkT 
      (from-transp! _ _
        (
        (
         ap (λ p → Tmᴹ {Γ S1.▶ A} {S1.wkT Γ A B} (V (S xp) , vw p)) (prop-has-all-paths _ _)
        ◾
        lifttᴹ Γ (S1.∙t Γ) A B (_ , vw xw)
        )
        ◾
        ( (
        _
        =⟨
        
        ap (λ e → coe e liftx') (uip _ _)
        ◾
        coe-∙ (ap (N.Tm _) eqe)
          (ap (λ v → N.Tm (Conᴹ (Γp , Γw') N.▶ Tyᴹ (Ap , Aw')) v) (! e-wkT))
          liftx'
        
        ⟩
        -- we use uip here (don't know if it's necessary)
        tr (λ v → N.Tm (Conᴹ (Γp , Γw') N.▶ Tyᴹ (Ap , Aw')) v)
        (! e-wkT)
        (MM.tr-Tm
           eqe
           liftx')
        =⟨
         ap (tr _ (! e-wkT))
           (ap
              (λ e →
                 MM.tr-Tm
                 (ap
                  (λ x →
                     N.liftT (Conᴹ (Γp , Γw')) (N.∙t (Conᴹ (Γp , Γw'))) (Tyᴹ (Ap , Aw'))
                     (MM.tr-Ty x (Tyᴹ (Bp , Bw))))
                  {x = e} {y = refl} (uip _ _))
                 (MM.liftt (Conᴹ (Γp , Γw')) (N.∙t (Conᴹ (Γp , Γw')))
                  (Tyᴹ (Ap , Aw')) (MM.tr-Ty e (Tyᴹ (Bp , Bw)))
                  (MM.tr2-Tm e (Tmᴹ (V xp , vw xw)))))
              {x = ^^ᴹ (Γp , Γw') (∙p , Γw')} {y = refl} (uip _ _))
         ⟩
        tr (λ v → N.Tm (Conᴹ (Γp , Γw') N.▶ Tyᴹ (Ap , Aw')) v)
          (! e-wkT) liftx
        =⟨
        transport-! _ e-wkT liftx
        ⟩
        transport! (λ v → N.Tm (Conᴹ (Γp , Γw') N.▶ Tyᴹ (Ap , Aw')) v)
          e-wkT liftx

        ∎
        )
        )
        ))
    where
      e-wkT = wkTᴹ syntax2 m2 mor1 {Γ = (Γp , Γw')}{(Ap , Aw')}{(Bp , Bw)}
      e-▶wkC = (▶wkCᴹ (Γp , Γw') (∙p , Γw') (Ap , Aw'))
      -- e-wkt = wktᴹ syntax2 m2 mor1 {Γ = (Γp , Γw')}{(Ap , Aw')}{(Bp , Bw)}
    
    

