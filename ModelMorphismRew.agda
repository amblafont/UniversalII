{-
Postulate a model morphism with rewrite rules, show that it is related to the syntax
           -}

{-# OPTIONS  --rewriting  #-}

open import Level
open import EqLib renaming (   fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )
  hiding (_∘_ ; _⁻¹ ; Π ; _$_)
open import Data.Nat renaming (suc to S)
open import Lib hiding (tr2)

module ModelMorphismRew {k : Level}  where

open import Model

open import Syntax {i = k} hiding ([<>]T)
open import SyntaxIsModel {i = k} renaming (module Syn to S)
import ModelRew {k = k} as M

open import ModelMorphism
open import RelationInhabit
open import Relation {k = k}
open import RelationSubstitution



{- ----------

Uniqueness:
we postulate a morphism (with some rewrite rules) and show that it is equals
to the one we constructed


-}
postulate
  m1 : CwFMor syntaxCwF M.RewCwF

  -- m1base : baseCwFMor syntaxCwF M.RewCwF
  -- m1next : nextCwFMor m1base

open CwFMor m1 

-- Agda won't recognize ,ʳ as a legal rewrite rule
postulate
  ,ʳ'   : ∀ {Γp Γw Ap Aw} →
      let Γ = (Γp , Γw) in
      let A = (Ap , Aw) in
      Conʳ (Γ S.▶ A) ↦ (Conʳ Γ M.▶ Tyʳ A)

{-# REWRITE ,ʳ'  #-}

postulate
  ,ʳ=1   : ∀ {Γ}{A} →
      ,ʳ {Γ}{A} ↦ refl

{-# REWRITE ,ʳ=1  #-}


-- these are true of any morphism, but
-- it is simpler to prove for the postulated morphism with rew rules

π₁ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
          (Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))
          ≡
          (M.π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))

π₁ʳ {Γ}{Δ}{A}{σ}
    -- rewrite ! (S.πη {σ = σ})
  =
  tr (λ s → Subʳ (S.π₁ s) ≡ M.π₁ (Subʳ s))
    -- {!! ( S.πη {σ = σ})!}
    (  S.πη {σ = σ})
    (! (( ap M.π₁ ( ,sʳ {σ = S.π₁ σ}{t = S.π₂ σ} )) ◾ M.π₁β  ) )


π₂ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
          (Tmʳ {Γ} {A S.[ S.π₁ σ ]T} (S.π₂ {Γ} {Δ} {A} σ))
          ==
          (M.π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))
          [ M.Tm _  ↓   []Tʳ {A = A}{σ = S.π₁ σ} ◾ ap (M._[_]T (Tyʳ A)) (π₁ʳ {σ = σ})  ]
π₂ʳ {Γ}{Δ}{A}{σ}  =
    ≅↓ helper
    where
      helper :
        (Tmʳ {Γ} {A S.[ S.π₁ σ ]T} (S.π₂ {Γ} {Δ} {A} σ)) ≅
          (M.π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))
      helper
      -- rewrite ! (S.πη {σ = σ})
        =
        tr (λ σ →
                  (Tmʳ {Γ} {A S.[ S.π₁ σ ]T} (S.π₂ {Γ} {Δ} {A} σ)) ≅
          (M.π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))
          )
          (S.πη {σ = σ})
          (
        (↓≅ (from-transp (M.Tm (Conʳ Γ)) ([]Tʳ {A = A}{σ = S.π₁ σ}) {u = Tmʳ (S.π₂ σ)} refl) )
            ∘≅
            (
          (↓≅ (apd M.π₂ ( ,sʳ {σ = S.π₁ σ}{t = S.π₂ σ} ))
          ∘≅ ↓≅ (M.π₂β {σ = Subʳ (S.π₁ σ)})
            )
          !≅))


wkʳ : ∀ {Γ : S.Con}{A : S.Ty Γ} →
  Subʳ (S.wk {A = A}) ≡ M.wk {A = Tyʳ A}
wkʳ {Γ}{A} = π₁ʳ ◾ ap M.π₁ idʳ

vzʳ : ∀{Γ : S.Con}{A : S.Ty Γ} →
  Tmʳ (S.vz {A = A}) == M.vz {A = Tyʳ A}
      [ M.Tm _ ↓ []Tʳ {A = A}{σ = S.wk} ◾ ap (λ s → M._[_]T (Tyʳ A) s) wkʳ ]
vzʳ {Γ}{A} = ≅↓ (↓≅ (π₂ʳ {A = A}{σ = S.id})
  ∘≅ ↓≅
      ( apd {A = M.Sub (Conʳ Γ M.▶ Tyʳ A)(Conʳ Γ M.▶ Tyʳ A)}
        (M.π₂ )
        {x = Subʳ ( S.id {Γ = Γ S.▶ A})}
        {y = M.id}
        idʳ ))

vsʳ : ∀{Γ : S.Con}{A : S.Ty Γ}{t : S.Tm Γ A}{B : S.Ty Γ} →
  Tmʳ (S.vs {B = B}t) == M.vs (Tmʳ t)
      [ M.Tm _ ↓ []Tʳ {A = A}{σ = S.wk} ◾ ap (λ s → M._[_]T (Tyʳ A) s) wkʳ ]

vsʳ {Γ}{A}{x}{B} =
  []tʳ {t = x}
  ∙ᵈ
  ↓-ap-in _ ((M._[_]T (Tyʳ A)))
      ( apd {A = M.Sub (Conʳ (Γ S.▶ B))(Conʳ Γ) }
          {B = λ s → M.Tm (Conʳ (Γ S.▶ B)) (M._[_]T (Tyʳ A) s)}
        (M._[_]t (Tmʳ x)) (wkʳ {A = B}) )

postulate
   m2 : UnivΠMor {ll = k} syntaxUnivΠ M.RewUnivΠ m1

open UnivΠMor m2
-- open nextCwFMor (nextcwfmor m2)

{-# REWRITE Uʳ  #-}

postulate
  Uʳ=1 : ∀{Γ} → Uʳ {Γ} ↦ refl

{-# REWRITE Uʳ=1  #-}




-- Agda does not accept Elʳ as a valid rewrite rule
postulate
    Elʳ' : ∀ {Γ : S.Con}
            {xp}{xw} →
          (Tyʳ {Γ} (Elp xp , Elw (₂ Γ)xw)) ↦ (M.El  (Tmʳ  {Γ = Γ}{A = _ , Uw (₂ Γ)} (xp , xw)))
{-# REWRITE Elʳ'  #-}

postulate
  Elʳ=1 : ∀{Γ}{x} → Elʳ {Γ}{x} ↦ refl
{-# REWRITE Elʳ=1  #-}





-- Agda does not accept Πʳ as a valid rewrite rule
postulate
    Πʳ' : ∀{Γ}
          {ap}{aw : (₁ Γ) ⊢ ap ∈ Up }
          {Bp}{Bw : ((₁ Γ) ▶p Elp ap) ⊢ Bp} →
          -- let Γ = (Γp , Γw) in
          let a : S.Tm Γ (S.U {Γ})
              a = (ap , aw)
          in
          let B : S.Ty (Γ S.▶ S.El {Γ} a)
              B = (Bp , Bw)
          in

          (Tyʳ {Γ}
            (_ , Πw (₂ Γ) aw Bw))
          ↦
          (M.Π {Conʳ Γ} (Tmʳ {Γ} {S.U {Γ}} a)
            ((Tyʳ {Γ S.▶ S.El {Γ} a} B)))
{-# REWRITE Πʳ'  #-}

postulate
  Πʳ=1 : ∀{Γ}{a}{B} → Πʳ {Γ}{a}{B} ↦ refl

{-# REWRITE Πʳ=1  #-}






-- Agda does not accept ΠNIʳ as a valid rewrite rule
postulate
    ΠNIʳ' : ∀{Γ}
          {T : Set k}
          {Bp : T → Typ}{Bw : ∀ (a : T) → (₁ Γ) ⊢ (Bp a)} →
          let B = λ a → _ , (Bw a) in
          (Tyʳ {Γ}
            (_ , ΠNIw (₂ Γ) Bw))
          ↦ (M.ΠNI {Conʳ Γ} {T}
            ((λ a → Tyʳ (B a))))

{-# REWRITE ΠNIʳ'  #-}

postulate
  ΠNIʳ=1 : ∀ {Γ}{T}{B} → ΠNIʳ {Γ}{T}{B} ↦ refl

{-# REWRITE ΠNIʳ=1  #-}




-- Agda does not accept ΠNIʳ as a valid rewrite rule
postulate
    ΠInfʳ' : ∀{Γ}
          {T : Set k}
          {Bp : T → Tmp}{Bw : ∀ (a : T) → (₁ Γ) ⊢ (Bp a) ∈ Up} →
          -- let Γ = (Γp , Γw) in
          let B = λ a → _ , (Bw a) in

          (Tmʳ {Γ} {U}
            (_ , ΠInfw (₂ Γ) Bw))
          ↦
          (M.ΠInf {Conʳ Γ} {T}
          -- (Tmʳ {Γ} {S.U {Γ}} a)
            (
            -- tr M.Ty (nextCwFMor.,ʳ m1next {A = S.El a} )
            (λ a → Tmʳ {_}{U} (B a))))

{-# REWRITE ΠInfʳ'  #-}

postulate
  ΠInfʳ=1 : ∀ {Γ}{T}{B} → ΠInfʳ {Γ}{T}{B} ↦ refl

{-# REWRITE ΠInfʳ=1  #-}







{-

This morphism satisifes the relations

-}




morCon~ : ∀ {Γ}(Γw : Γ ⊢) → Con~ Γw (Conʳ (Γ , Γw))
morTy~ : ∀ {Γ}Γw{A}(Aw : Γ ⊢ A) → Ty~ Aw (Tyʳ {Γ = (Γ , Γw)}(A , Aw))
morTm~ : ∀ {Γ}Γw{A}(Aw : Γ ⊢ A){t}(tw : Γ ⊢ t ∈ A) → Tm~ tw (Tmʳ {Γ = (Γ , Γw)}{(A , Aw)} (t , tw))
morVar~ : ∀ {Γ}Γw{A}(Aw : Γ ⊢ A){x}(xw : Γ ⊢ x ∈v A) → Var~ xw (Tmʳ {Γ = (Γ , Γw)}{(A , Aw)} (V x , vw xw))

morTy~  Γw {.Up} (Uw Γw') rewrite prop-has-all-paths Γw' Γw = lift refl

morTy~ {Γ} Γw' {.(ΠΠp ( _) _)} (Πw Γw Aw Bw)
    rewrite prop-has-all-paths Γw Γw'
  =
  (_ , morTm~ Γw' (Uw Γw') Aw) ,
  (_ , morTy~ (▶w Γw' (Elw Γw' Aw))  Bw) ,
  refl

morTy~ {Γ} Γw'  (ΠNIw Γw Bw) rewrite prop-has-all-paths Γw Γw'
  = (λ a → _ , morTy~ Γw' (Bw a)) , refl

morTy~ {Γ} Γw' {.(Elp _)} (Elw Γw aw) rewrite prop-has-all-paths Γw' Γw =
  (_ , morTm~ Γw (Uw Γw) aw  ) ,
  refl

morCon~ {.∙p} ∙w = Level.lift ∙ʳ
morCon~ {.(_ ▶p _)} (▶w Γw Aw) =
  (_ , morCon~ Γw) ,
  (_ , morTy~ Γw Aw) ,
  refl
  -- ,ʳ

-- morTm~ {Γ}Γw{A}Aw {t}tw = ?
morTm~ {Γ} Γw {A} Aw {.(V _)} (vw xw) = morVar~ Γw Aw xw
morTm~  Γw  sBw  (appw Γw' aw Bw tw uw)
  =
  (_ , morTm~ Γw (Uw Γw) aw) ,
  (_ , morTy~ (▶w Γw (Elw Γw aw)) Bw) ,
  -- {!? , ? morTm~ (▶w Γw (Elw Γw aw)) Bw!} ,
  (_ , morTm~ Γw (Πw Γw aw Bw) tw) ,
  (_ , morTm~ Γw (Elw Γw aw) uw) ,
    (eT , et Γw' (prop-has-all-paths Γw' Γw))
  where
    Γ : S.Con
    Γ = (_ , Γw)

    ElA : S.Ty Γ
    ElA = (_ , Elw Γw aw)

    u : S.Tm Γ ElA
    u = (_ , uw)

    B : S.Ty (Γ S.▶ ElA)
    B = (_ , Bw)

    B[] : S.Ty Γ
    B[] = (_ , sBw)

    ΠAB : S.Ty Γ
    ΠAB = S.Π (_ , aw) B
    t : S.Tm Γ ΠAB
    t = (_ , tw)

    eT :   (Tyʳ B[] ≡ Tyʳ B M.[ M.< Tmʳ u > ]T)
    eT = ap Tyʳ {x = B[]}{y = B S.[ S.< u > ]T } (Ty= (₁[<>]T {B = B})) ◾
        [<>]T {u = u}{B}

    et : ∀ Γw' (e : Γw' ≡ Γw) →
      (Tmʳ (app _ _ , appw Γw' aw Bw tw uw))
      ==
      ((Tmʳ t) M.$ (Tmʳ u))
      [ (M.Tm (Conʳ Γ)) ↓ eT ]

    et _ refl
      =
        help (₁[<>]T {B = B}{u = u}) _
        ∙ᵈ
        ($ʳ t u)



        where
          apptu = (app _ _ , appw Γw aw Bw tw uw)
      -- | (₁[<>]T {B = B}{u = u})

          help :
            ∀ {B}(e : _ ≡ B)Bw →
            -- let e = (₁[<>]T {B = B}{u = u}) in
            Tmʳ {Γ = Γ}apptu
            == Tmʳ (app _ _ , tr (λ C →  _ ⊢ _ ∈ C) ( e) (₂ apptu))
              [ M.Tm (Conʳ Γ) ↓ ap Tyʳ (Ty= {A = _ , sBw}{B = (B , Bw)}e) ]

          help refl Bw rewrite prop-has-all-paths sBw Bw = refl

morTm~ {Γp} Γw  sBw  (appNIw Γw'  Bw {t = t}tw u)
  rewrite prop-has-all-paths sBw (Bw u)
    | prop-has-all-paths Γw Γw'
  =
    ((λ a → _ , morTy~ Γw' (Bw a)) ,
    ((_ , morTm~ Γw' (ΠNIw Γw' Bw) tw) ,
    (refl ,
    et)))

  where
    et :
      Tmʳ (appNI t u , appNIw Γw' Bw tw u) ≡  (Tmʳ {A = _ , ΠNIw Γw' Bw} (t , tw)) M.$NI u
    et = $NIʳ (_ , tw) u

morTm~ {Γp} Γw  sBw  (appInfw Γw'  Bw {t = t}tw u)
  rewrite prop-has-all-paths sBw (Elw Γw' (Bw u))
    | prop-has-all-paths Γw Γw'
  =
    ((λ a → _ , morTm~ Γw' (Uw Γw') (Bw a)) ,
    ((_ , morTm~ Γw' (Elw Γw' (ΠInfw Γw' Bw)) tw) ,
    (refl ,
    et)))

  where
    et :
      Tmʳ (appNI t u , appInfw Γw' Bw tw u) ≡ (Tmʳ {A = _ , Elw Γw' (ΠInfw Γw' Bw)} (t , tw)) M.$Inf u
    et = $Infʳ (_ , tw) u

morTm~  Γw' (Uw Γw'') (ΠInfw Γw Bw)
    rewrite prop-has-all-paths Γw'' Γw'
          | prop-has-all-paths Γw Γw'
          =
  -- (λ a → {! (? , ?)!}) , {!!}
  (λ a →  (_ , morTm~ Γw' (Uw Γw') (Bw a))) , (refl , refl)




morVar~  Γw'  wAw {.0} (V0w Γw Aw)
  rewrite prop-has-all-paths Γw' (▶w Γw Aw)
    =
      (_ , morCon~ Γw) ,
      (_ , morTy~ Γw Aw) ,
      refl ,
      (eT ,
      -- ≅↓ (↓≅ {!vzʳ!})
      ≅↓   ( et (vw (V0w  Γw Aw)))
      )
    where
      Γ = (_ , Γw)
      A = (_ , Aw)
      eT : Tyʳ {Γ = (_ , ▶w Γw Aw)}
        (liftT 0 _ , wAw) ≡ (Tyʳ {Γ = (_ , Γw)}A M.[ M.π₁ M.id ]T)
      eT = ap Tyʳ (Ty= (wk=[wk]T Aw)) ◾ []Tʳ {A = A }{σ = S.wk} ◾ ap (λ s → M._[_]T (Tyʳ A) s) wkʳ
      -- eT = ap Tyʳ (Ty= {!!}) ◾ ?

      et : ∀ xw →


        -- (Tmʳ (V 0 , vw (V0w Γp Γw Ap Aw)))
        -- (Tmʳ {Γ = Γ S.▶ A}{A = _ , {!wkTw Aw Aw!}}(V 0 , xw))
        (Tmʳ {Γ = Γ S.▶ A}{A = _ , wAw}(V 0 , xw))
        ≅ (M.π₂ (M.id {Conʳ (Γ S.▶ A)}))
        -- [ (λ CE → M.Tm (₁ CE) (₂ CE)) ↓ (ap ((Conʳ (Γp , Γw) M.▶ Tyʳ (Ap , Aw)) ,_) eT) ]
      et xw =  ↓≅ (ap↓ {A = S.Ty  _}{B = S.Tm (Γ S.▶ A)}{C = λ C → M.Tm _ (Tyʳ C)} Tmʳ
        -- {p = (Ty= (wk=[wk]T Aw))}
        {u = V 0 , xw}{v = S.vz }
          (Tm=↓ (Ty= (wk=[wk]T Aw)) refl))
        ∘≅ ↓≅ (vzʳ {A = A})
      -- et xw = =≅ {!ap (Tmʳ {A = (A S.[ S.wk ]T)}) {x = (V 0 , xw)}{y = S.vz}!} ∘≅ ↓≅ vzʳ



morVar~ {.(Γp ▶p Ap)} Γw' {.(liftT 0 Bp)} Cw {.(S xp)} (VSw {Γp} Γw {Ap} Aw {Bp} Bw {xp} xw)
  rewrite prop-has-all-paths Γw' (▶w Γw Aw)
  =
  (_ , morCon~ Γw) ,
  (_ , morTy~ Γw Aw) ,
  (_ , morTy~ Γw Bw) ,
  (_ , morVar~ Γw Bw xw) ,
  refl ,
  eT ,
  ≅↓ et
  where
  Γ = (Γp , Γw)
  A = (Ap , Aw)
  B = (Bp , Bw)
  eT : Tyʳ {Γ = ((Γp ▶p Ap) , ▶w Γw Aw)}
      (liftT 0 Bp , Cw) ≡ (Tyʳ {Γ = (_ , Γw)}(Bp , Bw) M.[ M.π₁ M.id ]T)
  eT = ap Tyʳ (Ty= (wk=[wk]T Bw)) ◾ []Tʳ {A = B }{σ = S.wk} ◾ ap (λ s → M._[_]T (Tyʳ B) s) wkʳ
  x = (V xp , vw xw)
  sx = (V (S xp) , vw (VSw Γw Aw Bw xw))

  et :  (Tmʳ (V (S xp) , vw (VSw Γw Aw Bw xw)))
    ≅ (Tmʳ x M.[ M.π₁ M.id ]t)
  et =
      ↓≅ (ap↓ {A = S.Ty  _}{B = S.Tm (Γ S.▶ A)}{C = λ C → M.Tm _ (Tyʳ C)} Tmʳ
        {p = Ty= (wk=[wk]T Bw)}
        {u = sx}
        {v = S.vs x}
        -- {p = ?}
          -- {!Tm=↓ (Ty= (wk=[wk]T Bw)) refl!}
          ( Tm=↓ {t = sx}{u = S.vs x}(Ty= (wk=[wk]T Bw)) (wk=[wk]t (₂ x)) )
      )
    ∘≅ ↓≅ (vsʳ {t = x}{B = A})


morSub~ : ∀ {Γ}Γw{Δ}(Δw : Δ ⊢){σ}(σw : Γ ⊢ σ ⇒ Δ) → Sub~ σw (Subʳ {Γ = (Γ , Γw)}{(Δ , Δw)} (σ , σw))
-- morSub~ {Γ}Γw{Δ}Δw {σ}σw = ?
morSub~ {Γ} Γw {.∙p} ∙w {.nil} nilw = ∙ʳ ,
    Level.lift (from-transp _ _ M.εη)

-- {!m.∙ʳ!} , {!!}
morSub~ {Γp} Γw {.(_ ▶p _)} ΔAw  (,sw Δw σw Aw tw)
  rewrite prop-has-all-paths ΔAw (▶w Δw Aw)
  =

    (_ , morCon~ Δw) ,
    (_ , morSub~ Γw Δw σw) ,
    (_ , morTy~ Δw Aw) ,
    (_ ,   t~ (morTm~ Γw (Tyw[] Aw Γw σw) tw) ) ,
    refl ,
    ,sʳ
  where
  Γ = _ , Γw
  Δ = _ , Δw
  σ : S.Sub Γ Δ
  σ = _ , σw
  A : S.Ty Δ
  A = _ , Aw
  t~ : ∀ {tm} (tm~ : Tm~ tw tm) → Tm~ tw
    (tr (M.Tm (Conʳ Γ)) ([]Tʳ {A = A}{σ = σ})
    tm)

  t~ with
      (Tyʳ (A S.[ σ ]T))  |
      ([]Tʳ {Γ = _ , Γw}{_ , Δw}{A = (_ , Aw)}{σ = (_ , σw)})
  t~ | _ | refl = λ tm~ → tm~
