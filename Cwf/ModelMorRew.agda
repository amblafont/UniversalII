{-  
Postulate a model morphism with rewrite rules, show that it is related to the syntax
           -}

{-# OPTIONS  --rewriting --prop #-}

open import Level 
open import Hott renaming (   fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )
  hiding (_∘_ ; _⁻¹ ; Π ; _$_)


open import Data.Nat renaming (suc to S)

open import monlib hiding (tr2)



module ModelMorRew {k : Level}  where


open import ModelRecord


open import Syntax {i = k}
open import SyntaxIsModel {k = k} renaming (module Syn to S)
import ModelCwf {k = k} as M

open import ModelMorphism 
open import RelationCwfInhabit
open import RelationCwf {k = k}
open import RelationCwfSubstitution



{- ----------

Uniqueness:
we postulate a morphism (with some rewrite rules) and show that it is equals
to the one we constructed


-}
postulate
  Conʳ : S.Con → M.Con
  Tyʳ  : ∀ {Γ} → S.Ty Γ → M.Ty (Conʳ Γ)
  Tmʳ  : ∀ {Γ A} → S.Tm Γ A → M.Tm (Conʳ Γ) (Tyʳ A)
  Subʳ : ∀ {Γ Δ} → S.Sub Γ Δ → M.Sub (Conʳ Γ) (Conʳ Δ)
  ,ʳ   : ∀ {Γp Γw Ap Aw} →
      let Γ = (Γp , Γw) in
      let A = (Ap , Aw) in
      Conʳ (Γ S.▶ A) ↦ (Conʳ Γ M.▶ Tyʳ A)

{-# REWRITE ,ʳ  #-}


m1base : baseCwFMor syntaxCwF M.RewCwF
m1base = record { Conʳ = Conʳ ; Tyʳ = Tyʳ ; Tmʳ = Tmʳ ; Subʳ = Subʳ ; ,ʳ = refl }

postulate
  m1next : nextCwFMor m1base

m1 : CwFMor syntaxCwF M.RewCwF
m1 = record { basecwfmor = m1base
            ; nextcwfmor = m1next }

module _ where
  private
    module m = CwFMor m1
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
      (! (( ap M.π₁ (m.,sʳ {σ = S.π₁ σ}{t = S.π₂ σ})) ◾ M.π₁β  ) )


  π₂ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
            (m.Tmʳ {Γ} {A S.[ S.π₁ σ ]T} (S.π₂ {Γ} {Δ} {A} σ))
            ==
            (M.π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))
            [ M.Tm _  ↓   m.[]Tʳ {A = A}{σ = S.π₁ σ} ◾ ap (M._[_]T (m.Tyʳ A)) (π₁ʳ {σ = σ})  ]
  π₂ʳ {Γ}{Δ}{A}{σ}  =
     ≅↓ helper
     where
       helper : 
         (m.Tmʳ {Γ} {A S.[ S.π₁ σ ]T} (S.π₂ {Γ} {Δ} {A} σ)) ≅
           (M.π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))
       helper 
       -- rewrite ! (S.πη {σ = σ})
         =
         tr (λ σ → 
                    (m.Tmʳ {Γ} {A S.[ S.π₁ σ ]T} (S.π₂ {Γ} {Δ} {A} σ)) ≅
            (M.π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))
           )
            (S.πη {σ = σ})
           (
          (↓≅ (from-transp (M.Tm (Conʳ Γ)) (m.[]Tʳ {A = A}{σ = S.π₁ σ}) {u = m.Tmʳ (S.π₂ σ)} refl) )
              ∘≅
              (
            (↓≅ (apd M.π₂ (m.,sʳ {σ = S.π₁ σ}{t = S.π₂ σ}))
            ∘≅ ↓≅ (M.π₂β {σ = m.Subʳ (S.π₁ σ)}) 
              )
            !≅))
         

  wkʳ : ∀ {Γ : S.Con}{A : S.Ty Γ} →
    m.Subʳ (S.wk {A = A}) ≡ M.wk {A = m.Tyʳ A} 
  wkʳ {Γ}{A} = π₁ʳ ◾ ap M.π₁ m.idʳ

  vzʳ : ∀{Γ : S.Con}{A : S.Ty Γ} →
    m.Tmʳ (S.vz {A = A}) == M.vz {A = m.Tyʳ A}
       [ M.Tm _ ↓ m.[]Tʳ {A = A}{σ = S.wk} ◾ ap (λ s → M._[_]T (m.Tyʳ A) s) wkʳ ]
  vzʳ {Γ}{A} = ≅↓ (↓≅ (π₂ʳ {A = A}{σ = S.id})
    ∘≅ ↓≅
       ( apd {A = M.Sub (m.Conʳ Γ M.▶ m.Tyʳ A)(m.Conʳ Γ M.▶ m.Tyʳ A)}
          (M.π₂ )
          {x = m.Subʳ ( S.id {Γ = Γ S.▶ A})}
          {y = M.id}
          m.idʳ ))

  vsʳ : ∀{Γ : S.Con}{A : S.Ty Γ}{t : S.Tm Γ A}{B : S.Ty Γ} →
    m.Tmʳ (S.vs {B = B}t) == M.vs (m.Tmʳ t)
       [ M.Tm _ ↓ m.[]Tʳ {A = A}{σ = S.wk} ◾ ap (λ s → M._[_]T (m.Tyʳ A) s) wkʳ ]

  vsʳ {Γ}{A}{x}{B} =
    m.[]tʳ {t = x}
    ∙ᵈ
    ↓-ap-in _ ((M._[_]T (m.Tyʳ A)))
       ( apd {A = M.Sub (Conʳ (Γ S.▶ B))(m.Conʳ Γ) }
            {B = λ s → M.Tm (Conʳ (Γ S.▶ B)) (M._[_]T (Tyʳ A) s)}
          (M._[_]t (m.Tmʳ x)) (wkʳ {A = B}) )


postulate
    Uʳ  : {Γ : S.Con} → Tyʳ (S.U {Γ}) ↦ M.U
{-# REWRITE Uʳ  #-}

postulate
    Elʳ : ∀ {Γ : S.Con}
            {xp}{xw} →
          -- {x : S.Tm Γ (S.U {Γ})} →
          -- (Tyʳ {Γ} (S.El x)) ↦ (M.El  (Tmʳ   x))
          (Tyʳ {Γ} (Elp xp , Elw (₂ Γ)xw)) ↦ (M.El  (Tmʳ  {Γ = Γ}{A = _ , Uw _ (₂ Γ)} (xp , xw)))

{-# REWRITE Elʳ  #-}


postulate
    Πʳ : ∀{Γ}
           -- {Γ : S.Con}
          -- {a : S.Tm Γ (S.U {Γ})} {B : S.Ty (Γ S.▶ S.El {Γ} a)}
          -- {Γp}{Γw : Conw Γp}
          {ap}{aw : Tmw (₁ Γ) Up ap}
          {Bp}{Bw : Tyw ((₁ Γ) ▶p Elp ap) Bp} →
          -- let Γ = (Γp , Γw) in
          let a : S.Tm Γ (S.U {Γ}) 
              a = (ap , aw)
          in 
          let B : S.Ty (Γ S.▶ S.El {Γ} a)
              B = (Bp , Bw)
          in
             
          (Tyʳ {Γ}
            (_ , Πw (₂ Γ) aw Bw))
            -- (S.Π {Γ} a B))
          ↦
          (M.Π {Conʳ Γ} (Tmʳ {Γ} {S.U {Γ}} a)
            (
            -- tr M.Ty (nextCwFMor.,ʳ m1next {A = S.El a} )
            (Tyʳ {Γ S.▶ S.El {Γ} a} B)))

{-# REWRITE Πʳ  #-}

postulate
    $ʳ : ∀ {Γ}{a : S.Tm Γ S.U}{B : S.Ty (Γ S.▶ S.El a)}(t : S.Tm Γ (S.Π a B))
          (u : S.Tm Γ (S.El a)) → 
        Tmʳ (t S.$ u) == ((Tmʳ t) M.$  (Tmʳ u)) [ M.Tm _ ↓  CwFMor.[<>]T m1 {u = u}{B = B} ]

postulate
    ΠNIʳ : ∀{Γ}
          {T : Set k}
          {Bp : T → Typ}{Bw : ∀ (a : T) → Tyw (₁ Γ) (Bp a)} →
          -- let Γ = (Γp , Γw) in
          let B = λ a → _ , (Bw a) in
             
          (Tyʳ {Γ}
            (_ , ΠNIw (₂ Γ) Bw))
          ↦
          (M.ΠNI {Conʳ Γ} {T}
          -- (Tmʳ {Γ} {S.U {Γ}} a)
            (
            -- tr M.Ty (nextCwFMor.,ʳ m1next {A = S.El a} )
            (λ a → Tyʳ (B a))))

{-# REWRITE ΠNIʳ  #-}

postulate
    $NIʳ : ∀ {Γ}{T : Set k}{B : T → Ty Γ}(t : S.Tm Γ (S.ΠNI B))
          (u : T) → 
        Tmʳ (t S.$NI u) ≡ ((Tmʳ t) M.$NI  u)

postulate
    ΠInfʳ : ∀{Γ}
          {T : Set k}
          {Bp : T → Tmp}{Bw : ∀ (a : T) → Tmw (₁ Γ) Up (Bp a)} →
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

{-# REWRITE ΠInfʳ  #-}

postulate
    $Infʳ : ∀ {Γ}{T : Set k}{B : T → S.Tm Γ U}(t : S.Tm Γ (S.El (S.ΠInf B)))
          (u : T) → 
        Tmʳ (t S.$Inf u) ≡ ((Tmʳ t) M.$Inf  u)


m2 : UnivΠMor {ll = k} syntaxUnivΠ M.RewUnivΠ m1
m2 = record { univmor =
  record { Uʳ = refl ; Elʳ = refl } ;
  Πmor = record
     { Πʳ = refl ; $ʳ = (λ  {Γ} {a} {B} t u →  $ʳ t u    ) ;
       ΠNIʳ = refl ; $NIʳ = $NIʳ ;
       ΠInfʳ = refl ; $Infʳ = $Infʳ 
  } }
  {- 
  nextCwFMor.[]Tʳ m1next ∙'
ap (M._[_]T (Tyʳ B))
(to-transp!
 (from-transp (M.Sub (Conʳ Γ)) refl
  (to-transp (nextCwFMor.,sʳ m1next) ◾
   M.,s= (nextCwFMor.idʳ m1next)
   (≅↓
    ((↓≅ (from-transp (M.Tm (Conʳ Γ)) (nextCwFMor.[]Tʳ m1next) refl)
      !≅)
     ∘≅
     ↓≅
     (ap↓ Tmʳ
      (from-transp! (Tm Γ)
       (Ty= (ap Elp ([idp]t (₂ a)))
        | Elp (₁ a [ iter ∣ ₁ Γ ∣ (λ σ → V 0 :: map (liftt 0) σ) nil ]t)
        | ap Elp ([idp]t (₂ a)))
       refl))
     ∘≅ (↓≅ (from-transp! (M.Tm (Conʳ Γ)) M.[id]T refl) !≅))))))
     -}

  -- Πmor = record { Πʳ = refl ; $ʳ = (λ { {Γ} {a} {B} t u {e} p → {! $ʳ t u !} }) } }






-- module _  (m2 : UnivΠMor syntaxUnivΠ M.RewUnivΠ m1) where
module _   where
    private
      module m where
        open CwFMor m1 public
        open UnivΠMor m2 public


    morCon~ : ∀ {Γ}(Γw : Conw Γ) → Con~ Γw (m.Conʳ (Γ , Γw))
    morTy~ : ∀ {Γ}Γw{A}(Aw : Tyw Γ A) → Ty~ Aw (m.Tyʳ {Γ = (Γ , Γw)}(A , Aw))
    morTm~ : ∀ {Γ}Γw{A}(Aw : Tyw Γ A){t}(tw : Tmw Γ A t) → Tm~ tw (m.Tmʳ {Γ = (Γ , Γw)}{(A , Aw)} (t , tw))
    morVar~ : ∀ {Γ}Γw{A}(Aw : Tyw Γ A){x}(xw : Varw Γ A x) → Var~ xw (m.Tmʳ {Γ = (Γ , Γw)}{(A , Aw)} (V x , vw xw))

    morTy~ {.Γp} Γw {.Up} (Uw Γp Γw') rewrite prop-has-all-paths Γw' Γw = lift refl

    morTy~ {Γ} Γw' {.(ΠΠp (Elp _) _)} (Πw Γw Aw Bw)
        rewrite prop-has-all-paths Γw Γw' 
      =
      (_ , morTm~ Γw' (Uw _ Γw') Aw) ,
      (_ , morTy~ (▶w Γw' (Elw Γw' Aw))  Bw) ,
      refl

    morTy~ {Γ} Γw'  (ΠNIw Γw Bw) rewrite prop-has-all-paths Γw Γw' 
      = (λ a → _ , morTy~ Γw' (Bw a)) , refl

    morTy~ {Γ} Γw' {.(Elp _)} (Elw Γw aw) rewrite prop-has-all-paths Γw' Γw =
      (_ , morTm~ Γw (Uw _ Γw) aw  ) ,
      refl  

    morCon~ {.∙p} ∙w = Level.lift m.∙ʳ
    morCon~ {.(_ ▶p _)} (▶w Γw Aw) =
      (_ , morCon~ Γw) ,
      (_ , morTy~ Γw Aw) ,
      refl
      -- m.,ʳ

    -- morTm~ {Γ}Γw{A}Aw {t}tw = ?
    morTm~ {Γ} Γw {A} Aw {.(V _)} (vw xw) = morVar~ Γw Aw xw 
    morTm~ {.Γp} Γw {.(l-subT 0 up Bp)} sBw {.(app tp up)} (appw Γp Γw' Ap aw Bp Bw tp tw up uw)
      =
      (_ , morTm~ Γw (Uw _ Γw) aw) ,
      (_ , morTy~ (▶w Γw (Elw Γw aw)) Bw) ,
      -- {!? , ? morTm~ (▶w Γw (Elw Γw aw)) Bw!} ,
      (_ , morTm~ Γw (Πw Γw aw Bw) tw) ,
      (_ , morTm~ Γw (Elw Γw aw) uw) ,
       (eT , et Γw' (prop-has-all-paths Γw' Γw))
      where
        Γ : S.Con
        Γ = (Γp , Γw)

        ElA : S.Ty Γ
        ElA = (_ , Elw Γw aw)

        u : S.Tm Γ ElA
        u = (up , uw)

        B : S.Ty (Γ S.▶ ElA)
        B = (Bp , Bw)

        B[] : S.Ty Γ
        B[] = (l-subT 0 up Bp , sBw)

        ΠAB : S.Ty Γ
        ΠAB = S.Π (_ , aw) B
        t : S.Tm Γ ΠAB
        t = (tp , tw)

        eT :   (m.Tyʳ B[] ≡ m.Tyʳ B M.[ M.< m.Tmʳ u > ]T)
        eT = ap m.Tyʳ {x = (l-subT 0 up Bp , sBw)}{y = B S.[ S.< u > ]T } (Ty= (₁[<>]T {B = B})) ◾
           m.[<>]T {u = u}{B} 

        et : ∀ Γw' (e : Γw' ≡ Γw) → 
          (m.Tmʳ (app tp up , appw Γp Γw' Ap aw Bp Bw tp tw up uw))
          ==
          ((m.Tmʳ t) M.$ (m.Tmʳ u))
          [ (M.Tm (Conʳ (Γp , Γw))) ↓ eT ]

        et _ refl
          = 
            help (₁[<>]T {B = B}{u = u}) _
           ∙ᵈ
            ($ʳ t u)
           
            

           where
             apptu = (app tp up , appw Γp Γw Ap aw Bp Bw tp tw up uw) 
          -- | (₁[<>]T {B = B}{u = u})

             help :
                ∀ {B}(e : _ ≡ B)Bw →
                -- let e = (₁[<>]T {B = B}{u = u}) in
                Tmʳ {Γ = Γ}apptu
                == Tmʳ (app tp up , tr (λ C → Tmw _ C _) ( e) (₂ apptu))
                  [ M.Tm (m.Conʳ Γ) ↓ ap m.Tyʳ (Ty= {A = _ , sBw}{B = (B , Bw)}e) ]
              
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
          Tmʳ (appNI t u , appNIw Γw' Bw tw u) ≡ M.app$NI (m.Tmʳ {A = _ , ΠNIw Γw' Bw} (t , tw)) u
        et = $NIʳ (_ , tw) u

    morTm~ {Γp} Γw  sBw  (appInfw Γw'  Bw {t = t}tw u)
      rewrite prop-has-all-paths sBw (Elw Γw' (Bw u))
        | prop-has-all-paths Γw Γw'
      =
       ((λ a → _ , morTm~ Γw' (Uw _ Γw') (Bw a)) ,
       ((_ , morTm~ Γw' (Elw Γw' (ΠInfw Γw' Bw)) tw) ,
       (refl ,
       et)))

      where
        et :
          Tmʳ (appNI t u , appInfw Γw' Bw tw u) ≡ M.app$Inf (m.Tmʳ {A = _ , Elw Γw' (ΠInfw Γw' Bw)} (t , tw)) u
        et = $Infʳ (_ , tw) u

    morTm~ {.Γp} Γw' (Uw Γp Γw'') (ΠInfw Γw Bw)
       rewrite prop-has-all-paths Γw'' Γw'
             | prop-has-all-paths Γw Γw'
             =
      -- (λ a → {! (? , ?)!}) , {!!}
      (λ a →  (_ , morTm~ Γw' (Uw _ Γw') (Bw a))) , (refl , refl)
      
          

      
    morVar~ {.(Γp ▶p Ap)} Γw' {.(liftT 0 Ap)} wAw {.0} (V0w Γp Γw Ap Aw)
      rewrite prop-has-all-paths Γw' (▶w Γw Aw)
       =
          (_ , morCon~ Γw) ,
          (_ , morTy~ Γw Aw) ,
          refl ,
          (eT ,
          -- ≅↓ (↓≅ {!vzʳ!})
          ≅↓   ( et (vw (V0w Γp Γw Ap Aw)))
          )
        where
          Γ = (Γp , Γw)
          A = (Ap , Aw)
          eT : Tyʳ {Γ = ((Γp ▶p Ap) , ▶w Γw Aw)}
            (liftT 0 Ap , wAw) ≡ (m.Tyʳ {Γ = (_ , Γw)}A M.[ M.π₁ M.id ]T)
          eT = ap m.Tyʳ (Ty= (wk=[wk]T Aw)) ◾ m.[]Tʳ {A = A }{σ = S.wk} ◾ ap (λ s → M._[_]T (m.Tyʳ A) s) wkʳ
          -- eT = ap m.Tyʳ (Ty= {!!}) ◾ ?

          et : ∀ xw →
             
            
            -- (Tmʳ (V 0 , vw (V0w Γp Γw Ap Aw)))
            -- (Tmʳ {Γ = Γ S.▶ A}{A = _ , {!wkTw Aw Aw!}}(V 0 , xw))
            (Tmʳ {Γ = Γ S.▶ A}{A = _ , wAw}(V 0 , xw))
            ≅ (M.π₂ (M.id {m.Conʳ (Γ S.▶ A)}))
            -- [ (λ CE → M.Tm (₁ CE) (₂ CE)) ↓ (ap ((Conʳ (Γp , Γw) M.▶ Tyʳ (Ap , Aw)) ,_) eT) ]
          et xw =  ↓≅ (ap↓ {A = S.Ty  _}{B = S.Tm (Γ S.▶ A)}{C = λ C → M.Tm _ (m.Tyʳ C)} m.Tmʳ
            -- {p = (Ty= (wk=[wk]T Aw))}
            {u = V 0 , xw}{v = S.vz }
             (Tm=↓ (Ty= (wk=[wk]T Aw)) refl))
            ∘≅ ↓≅ (vzʳ {A = A})
          -- et xw = =≅ {!ap (m.Tmʳ {A = (A S.[ S.wk ]T)}) {x = (V 0 , xw)}{y = S.vz}!} ∘≅ ↓≅ vzʳ
          


    morVar~ {.(Γp ▶p Ap)} Γw' {.(liftT 0 Bp)} Cw {.(S xp)} (VSw Γp Γw Ap Aw Bp Bw xp xw)
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
         (liftT 0 Bp , Cw) ≡ (m.Tyʳ {Γ = (_ , Γw)}(Bp , Bw) M.[ M.π₁ M.id ]T)
      eT = ap m.Tyʳ (Ty= (wk=[wk]T Bw)) ◾ m.[]Tʳ {A = B }{σ = S.wk} ◾ ap (λ s → M._[_]T (m.Tyʳ B) s) wkʳ
      x = (V xp , vw xw)
      sx = (V (S xp) , vw (VSw Γp Γw Ap Aw Bp Bw xp xw))

      et :  (m.Tmʳ (V (S xp) , vw (VSw Γp Γw Ap Aw Bp Bw xp xw)))
        ≅ (m.Tmʳ x M.[ M.π₁ M.id ]t)
      et = 
         ↓≅ (ap↓ {A = S.Ty  _}{B = S.Tm (Γ S.▶ A)}{C = λ C → M.Tm _ (m.Tyʳ C)} m.Tmʳ
           {p = Ty= (wk=[wk]T Bw)}
           {u = sx}
           {v = S.vs x}
           -- {p = ?}
              -- {!Tm=↓ (Ty= (wk=[wk]T Bw)) refl!}
              ( Tm=↓ {t = sx}{u = S.vs x}(Ty= (wk=[wk]T Bw)) (wk=[wk]t (₂ x)) )
         )
        ∘≅ ↓≅ (vsʳ {t = x}{B = A})


    morSub~ : ∀ {Γ}Γw{Δ}(Δw : Conw Δ){σ}(σw : Subw Γ Δ σ) → Sub~ σw (m.Subʳ {Γ = (Γ , Γw)}{(Δ , Δw)} (σ , σw))
    -- morSub~ {Γ}Γw{Δ}Δw {σ}σw = ?
    morSub~ {Γ} Γw {.∙p} ∙w {.nil} nilw = m.∙ʳ ,
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
       m.,sʳ
     where
      Γ = _ , Γw
      Δ = _ , Δw
      σ : S.Sub Γ Δ
      σ = _ , σw
      A : S.Ty Δ
      A = _ , Aw
      t~ : ∀ {tm} (tm~ : Tm~ tw tm) → Tm~ tw
        (tr (M.Tm (Conʳ Γ)) (m.[]Tʳ {A = A}{σ = σ})
        tm)

      t~ with 
          (Tyʳ (A S.[ σ ]T))  |
          (m.[]Tʳ {Γ = _ , Γw}{_ , Δw}{A = (_ , Aw)}{σ = (_ , σw)})
      t~ | _ | refl = λ tm~ → tm~




