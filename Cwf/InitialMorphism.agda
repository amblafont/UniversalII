{-  copied from finitaryQiit/modelTemplate
some complementary lemmas about the syntax
           -}

{-# OPTIONS  --rewriting  #-}

open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )

  hiding (_∘_ ; _⁻¹ ; Π ; _$_)



open import monlib hiding (tr2)



module InitialMorphism   where


open import ModelRecord


open import Syntax
open import SyntaxIsModel renaming (module Syn to S)
import ModelCwf as M

open import ModelMorphism
open import RelationCwfInhabit
open import RelationCwf
open import RelationCwfSubstitution

Conʳ : S.Con → M.Con
Conʳ = λ Γ → ₁ (ΣCon~  (₂ Γ))

Tyʳ  : ∀ {Γ} → S.Ty Γ → M.Ty (Conʳ Γ)
Tyʳ {Γ}A =   ₁ (ΣTy~ (ΣCon~  (₂ Γ)) (₂ A))

Tmʳ  : ∀ {Γ A} → S.Tm Γ A → M.Tm (Conʳ Γ) (Tyʳ A)
Tmʳ {Γ}{A}t = ₁ (ΣTm~ (ΣCon~  (₂ Γ)) (ΣTy~ (ΣCon~  (₂ Γ))(₂ A)) (₂ t))

Subʳ : ∀ {Γ Δ} → S.Sub Γ Δ → M.Sub (Conʳ Γ) (Conʳ Δ)
Subʳ {Γ}{Δ}σ = ₁ (ΣSub~ (ΣCon~  (₂ Γ))(ΣCon~  (₂ Δ))  (₂ σ))

[]Tʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ Δ} →
      Tyʳ (A S.[ σ ]T) ≡ Tyʳ A M.[ Subʳ σ ]T

[]Tʳ {Γ}{Δ}{A}{σ} =
  let Γm = (ΣCon~ (₂ Γ))
      Δm = (ΣCon~ (₂ Δ))
  in
  fst=
    (prop-has-all-paths
      (ΣTy~ (ΣCon~ (₂ Γ)) (Tyw[] (₂ A) (₂ Γ) (₂ σ)))
      (_ , Ty[]~ Γm Δm (ΣSub~ Γm Δm (₂ σ))(ΣTy~ Δm (₂ A)))
    )

[]tʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {t : S.Tm Δ A} {σ : S.Sub Γ Δ} →
           Tmʳ {Γ}  (t S.[ σ ]t )
           == 
           (Tmʳ {Δ} {A} t) M.[ Subʳ σ ]t
            [ M.Tm _  ↓ []Tʳ {A = A}{σ = σ} ]

[]tʳ {Γ}{Δ}{A}{t}{σ} =
  aux tm[]
  where
   Γm = ΣCon~ (₂ Γ)
   Δm = ΣCon~ (₂ Δ)
   Am = (ΣTy~ Δm (₂ A))
   σm = (ΣSub~ Γm Δm (₂ σ))

   Am[] = ΣTy~ Γm (₂ (A S.[ σ ]T))

   tm[] : ∃ (Tm~ (Tmw[] (₂ t) (₂ Γ) (₂ σ)))
   tm[] = ΣTm~ Γm Am[] (₂ (t S.[ σ ]t))

   aux : ∀ (tm[]' : ∃ (Tm~ (Tmw[] (₂ t) (₂ Γ) (₂ σ)))) → ₁ tm[]' == 
           (Tmʳ {Δ} {A} t) M.[ Subʳ σ ]t
            [ M.Tm _  ↓ []Tʳ {A = A}{σ = σ} ]
            -- [ M.Tm _  ↓ {![]Tʳ {A = A}{σ = σ} = {!tm[]!}!} ]

   -- aux rewrite []Tʳ {A = A}{σ = σ} = {!tm[]!}
   aux tm[]' rewrite []Tʳ {A = A}{σ = σ} =
     
      fst=
        (prop-has-all-paths
          {{  TmP (Tmw[] (₂ t) (₂ Γ) (₂ σ)) (₁ Am M.[ ₁ σm ]T)  }}
          tm[]'
          (_ ,  Tm[]~ Γm Δm σm {tw = ₂ t}(ΣTm~ Δm Am (₂ t)) )
        )
     
idʳ : {Γ : S.Con} → Subʳ {Γ = Γ} S.id ≡ M.id
idʳ {Γ} = fst=
             (prop-has-all-paths
               (ΣSub~ Γm Γm (₂ S.id) )
               (_ , id~ Γm)
              )
    where
      Γm = ΣCon~ (₂ Γ)

-- π₁ʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
--       Subʳ (S.π₁ σ) ≡ M.π₁  (Subʳ σ)

-- π₁ʳ {Γ} {Δ} {A} {.(_ :: _) , ,sw Δw σw Aw tw} = {!refl!}


,sʳ :  {Γ Δ : S.Con} {σ : S.Sub Γ Δ} {A : S.Ty Δ}
      {t : S.Tm Γ (A S.[ σ ]T)} →
      Subʳ (σ S.,s t) ≡ (Subʳ σ M.,s tr (M.Tm (Conʳ Γ)) ([]Tʳ {A = A}{σ = σ}) (Tmʳ t))
      -- it should computes here..
,sʳ {Γ}{Δ}{σ}{A}{t} =
  {!M.,s=!}

iniMor : CwFMor syntaxCwF M.RewCwF
iniMor = record
           { basecwfmor = record { Conʳ = Conʳ
           ; Tyʳ = Tyʳ
           ; Tmʳ = Tmʳ
           ; Subʳ = Subʳ
           ; ,ʳ = refl
           }
           ; nextcwfmor = record { 

             ∙ʳ = refl
           ; []Tʳ = λ {Γ}{Δ}{A}{σ} → []Tʳ {A = A}{σ = σ}
           ; []tʳ = λ{Γ}{Δ}{A}{t}{σ} → []tʳ {t = t}{σ = σ}
           ; idʳ = λ{Γ}→ idʳ {Γ}
           ; ∘ʳ = {!refl!}
           ; εʳ = refl
           -- ça devrait calculer ici par refl ! TODO: réfléchir à pourquoi ce n'est pas le
           -- cas
           ; ,sʳ = {!helper!}
           -- ; π₁ʳ = λ {Γ}{Δ}{A}{σ} → {! π₁ʳ {A = A}{σ = σ} !}
           -- ; π₂ʳ = {!!}
           }
           }

appʳ : {Γ : S.Con} {a : S.Tm Γ S.U} {B : S.Ty (Γ S.▶ S.El a)}
      {t : S.Tm Γ (S.Π a B)} →
      Tmʳ (S.app t) ≡
      UnivΠ.app M.RewUnivΠ ( (Tmʳ t))

appʳ {Γ}{a}{B}{t}
  -- rewrite helper{A = S.El a}{B = B}
  = {!helper refl {a = S.app t}!}

iniMorUnivΠ : UnivΠMor syntaxUnivΠ M.RewUnivΠ iniMor
iniMorUnivΠ = record {
  Uʳ = refl ;
  Elʳ = refl ;
  Πʳ = refl ;
  -- réfléchir à pourquoi ce n'est pas le cas
  -- I think refl doesn't work because app is primitive in the model rather than _$_
  -- (especially in the model morphism in fact)
  appʳ = {!refl!} }


{- ----------

Uniqueness:
we postulate a morphism (with some rewrite rules) and show that it is equals
to the one we constructed


-}
postulate
  Conʳ' : S.Con → M.Con
  Tyʳ'  : ∀ {Γ} → S.Ty Γ → M.Ty (Conʳ' Γ)
  Tmʳ'  : ∀ {Γ A} → S.Tm Γ A → M.Tm (Conʳ' Γ) (Tyʳ' A)
  Subʳ' : ∀ {Γ Δ} → S.Sub Γ Δ → M.Sub (Conʳ' Γ) (Conʳ' Δ)
  ,ʳ'   : ∀ {Γp Γw Ap Aw} →
      let Γ = (Γp , Γw) in
      let A = (Ap , Aw) in
      Conʳ' (Γ S.▶ A) ↦ (Conʳ' Γ M.▶ Tyʳ' A)

{-# REWRITE ,ʳ'  #-}


m1base : baseCwFMor syntaxCwF M.RewCwF
m1base = record { Conʳ = Conʳ' ; Tyʳ = Tyʳ' ; Tmʳ = Tmʳ' ; Subʳ = Subʳ' ; ,ʳ = refl }

postulate
  m1next : nextCwFMor m1base

m1 : CwFMor syntaxCwF M.RewCwF
m1 = record { basecwfmor = m1base
            ; nextcwfmor = m1next }

postulate
    Uʳ'  : {Γ : S.Con} → Tyʳ' (S.U {Γ}) ↦ M.U
{-# REWRITE Uʳ'  #-}

postulate
    Elʳ' : ∀ {Γ : S.Con}
            {xp}{xw} →
          -- {x : S.Tm Γ (S.U {Γ})} →
          -- (Tyʳ' {Γ} (S.El x)) ↦ (M.El  (Tmʳ'   x))
          (Tyʳ' {Γ} (Elp xp , Elw (₂ Γ)xw)) ↦ (M.El  (Tmʳ'  {Γ = Γ}{A = _ , Uw _ (₂ Γ)} (xp , xw)))

{-# REWRITE Elʳ'  #-}


postulate
    Πʳ' : ∀{Γ}
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
             
          (Tyʳ' {Γ}
            (_ , Πw (₂ Γ) aw Bw))
            -- (S.Π {Γ} a B))
          ↦
          (M.Π {Conʳ' Γ} (Tmʳ' {Γ} {S.U {Γ}} a)
            (
            -- tr M.Ty (nextCwFMor.,ʳ m1next {A = S.El a} )
            (Tyʳ' {Γ S.▶ S.El {Γ} a} B)))

{-# REWRITE Πʳ'  #-}

$ʳ : ∀ {Γ}{a : S.Tm Γ S.U}{B : S.Ty (Γ S.▶ S.El a)}(t : S.Tm Γ (S.Π a B))
      (u : S.Tm Γ (S.El a)) → S.Tm Γ (B S.[ S.< u > ]T) →
    Tmʳ' (t S.$ u) == ((Tmʳ' t) M.$  (Tmʳ' u)) [ M.Tm _ ↓  CwFMor.[<>]T m1 {u = u}{B = B} ]
$ʳ {Γ}{a}{B}t u = {!!}





module _  (m2 : UnivΠMor syntaxUnivΠ M.RewUnivΠ m1) where
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

    morTy~ {Γ} Γw' {.(Elp _)} (Elw Γw aw) rewrite prop-has-all-paths Γw' Γw =
      (_ , morTm~ Γw (Uw _ Γw) aw  ) ,
      refl  

    morCon~ {.∙p} ∙w = HoTT.lift m.∙ʳ
    morCon~ {.(_ ▶p _)} (▶w Γw Aw) =
      (_ , morCon~ Γw) ,
      (_ , morTy~ Γw Aw) ,
      refl
      -- m.,ʳ

    -- morTm~ {Γ}Γw{A}Aw {t}tw = ?
    morTm~ {Γ} Γw {A} Aw {.(V _)} (vw xw) = morVar~ Γw Aw xw 
    morTm~ {.Γp} Γw {.(l-subT 0 up Bp)} sBw {.(app tp up)} (appw Γp Γw' Ap aw Bp Bw tp tw up uw)
      -- rewrite prop-has-all-paths Γw' Γw
        -- | prop-has-all-paths {{ {!!} }} (l-subT 0 up Bp) {!!}
        -- ((Bp , Bw) S.[ S.<_> {Γ = Γp , Γw}{_ , Elw Γw aw}(up , uw) ]T)
      -- | prop-has-all-paths {{ ? }} (l-subT 0 up Bp , sBw)
      --   ((Bp , Bw) S.[ S.<_> {Γ = Γp , Γw}{_ , Elw Γw aw}(up , uw) ]T)
      =
      (_ , morTm~ Γw (Uw _ Γw) aw) ,
      (_ , morTy~ (▶w Γw (Elw Γw aw)) Bw) ,
      -- {!? , ? morTm~ (▶w Γw (Elw Γw aw)) Bw!} ,
      (_ , morTm~ Γw (Πw Γw aw Bw) tw) ,
      (_ , morTm~ Γw (Elw Γw aw) uw) ,
      {!!}
      -- {! m.[<>]T {u = u}{B = B} !} ,
      -- {!$ʳ {Γ}{_ , aw}{_ , Bw}(_ , tw)u!}
      where
        Γ : S.Con
        Γ = (Γp , Γw)

        ElA : S.Ty Γ
        ElA = (_ , Elw Γw aw)

        u : S.Tm Γ ElA
        u = (up , uw)

        B : S.Ty (Γ S.▶ ElA)
        B = (Bp , Bw)

        ΠAB : S.Ty Γ
        ΠAB = S.Π (_ , aw) B
        t : S.Tm Γ ΠAB
        t = (tp , tw)

        aux : ∀ Bp' sBw' →
          Σ
            -- (Tyʳ' (l-subT 0 up Bp , sBw) ≡
            (Tyʳ' (Bp' , sBw') ≡
            m.Tyʳ B M.[ M.< m.Tmʳ u > ]T)
            (λ eC →
              (m.Tmʳ (app tp up , appw Γp Γw' Ap aw Bp Bw tp tw up uw))
              ==
              (m.Tmʳ t M.$ m.Tmʳ u)
              [ (M.Tm (Conʳ' (Γp , Γw))) ↓ ? ]
              -- eC

              )
        aux = ?
        -- aux with (l-subT 0 up Bp) | sBw
        -- ...  | B[] | sBww = {!!}

      {- 
      where
        Γ : S.Con
        Γ = (Γp , Γw)

        ElA : S.Ty Γ
        ElA = (_ , Elw Γw aw)

        B : S.Ty (Γ S.▶ ElA)
        B = (Bp , Bw)

        u : S.Tm Γ ElA
        u = (up , uw)
        -}

        -- eT : Tyʳ' (l-subT 0 up Bp , sBw) ≡
        --      m.Tyʳ B M.[ M.< m.Tmʳ  u > ]T
        -- eT =
          
        --     (Tyʳ' (l-subT 0 up Bp , sBw))

        --       =⟨ {!m.[]Tʳ!} ⟩
        --     (Tyʳ' (B S.[ S.< u > ]T))

        --       =⟨ m.[]Tʳ {A = B}{σ = S.< u >} ⟩
        --     (m.Tyʳ B M.[ m.Subʳ (S.< u >) ]T)

        --       =⟨ ap (λ s → M._[_]T (m.Tyʳ B) s) m.<>ʳ ⟩
        --     (m.Tyʳ B M.[ M.< m.Tmʳ  u > ]T)
        --   =∎
          

      
    morVar~ {.(Γp ▶p Ap)} Γw' {.(liftT 0 Ap)} wAw {.0} (V0w Γp Γw Ap Aw)
      rewrite prop-has-all-paths Γw' (▶w Γw Aw)
       =
      (_ , morCon~ Γw) ,
      (_ , morTy~ Γw Aw) ,
      refl ,
      ({!eT!} ,
      {!!})
     where
      eT : Tyʳ' {Γ = ((Γp ▶p Ap) , ▶w Γw Aw)}
         (liftT 0 Ap , wAw) == (m.Tyʳ {Γ = (_ , Γw)}(Ap , Aw) M.[ M.π₁ M.id ]T)
      eT = {!!}

    morVar~ {.(Γp ▶p Ap)} Γw' {.(liftT 0 Bp)} Cw {.(S xp)} (VSw Γp Γw Ap Aw Bp Bw xp xw)
      rewrite prop-has-all-paths Γw' (▶w Γw Aw)
      =
     (_ , morCon~ Γw) ,
     (_ , morTy~ Γw Aw) ,
     (_ , morTy~ Γw Bw) ,
     (_ , morVar~ Γw Bw xw) ,
     refl ,
     eT ,
     {!!}
     where
      eT : Tyʳ' {Γ = ((Γp ▶p Ap) , ▶w Γw Aw)}
         (liftT 0 Bp , Cw) == (m.Tyʳ {Γ = (_ , Γw)}(Bp , Bw) M.[ M.π₁ M.id ]T)
      eT = {!!}

    morSub~ : ∀ {Γ}Γw{Δ}(Δw : Conw Δ){σ}(σw : Subw Γ Δ σ) → Sub~ σw (m.Subʳ {Γ = (Γ , Γw)}{(Δ , Δw)} (σ , σw))
    -- morSub~ {Γ}Γw{Δ}Δw {σ}σw = ?
    morSub~ {Γ} Γw {.∙p} ∙w {.nil} nilw = m.∙ʳ ,
      from-transp _ _ M.εη
    -- {!m.∙ʳ!} , {!!}
    morSub~ {Γ} Γw {.(_ ▶p _)} ΔAw {.(_ :: _)} (,sw Δw σw Aw tw) =
       (_ , morCon~ Δw) ,
       (_ , morSub~ Γw Δw σw) ,
       (_ , morTy~ Δw Aw) ,
       ({!m.Tmʳ {Γ = (_ , Γw)}{A = (_ , ?)}(_ , tw)!} ,  {!morTm~ Γw _ tw!} ) ,
       {!!} ,
       {!!}


    -- uniqueness
    Conʳ'= : ∀ {Γ : S.Con} → Conʳ' Γ ≡ Conʳ Γ
    Conʳ'= {Γ} = fst= (prop-has-all-paths (_ , morCon~ (₂ Γ)) (ΣCon~ (₂ Γ)))

    Tyʳ'= : ∀ {Γ : S.Con}{A : S.Ty Γ} → Tyʳ' A == Tyʳ A [ M.Ty ↓ Conʳ'= {Γ} ]

    Tyʳ'= {Γ}{A} with Conʳ' Γ | Tyʳ' A | morTy~ (₂ Γ) (₂ A) | Conʳ'= {Γ}
    -- ...   | Γm | Am | A~ | e = {!e!}
    Tyʳ'= {Γ} {A} | .(₁ (ΣCon~ (₂ Γ))) | Am | A~ | refl =
      fst= (prop-has-all-paths (_ , A~) (ΣTy~ (ΣCon~ (₂ Γ)) (₂ A)))

    Tmʳ'= : ∀ {Γ : S.Con}{A}{t : S.Tm Γ A} → Tmʳ' t == Tmʳ t
      [ (λ x → M.Tm (₁ x)(₂ x)) ↓ pair= (Conʳ'= {Γ}) (Tyʳ'= {Γ} {A}) ]

    Tmʳ'= {Γ}{A}{t} 
      with 
        Conʳ' Γ | Tyʳ' A | Tmʳ' t | morTm~ (₂ Γ)(₂ A) (₂ t) | Conʳ'= {Γ} | Tyʳ'= {Γ}{A}
    
    -- ... | Γm | Am | tm | t~ | eΓ | eA = {!eΓ!}
    ... | _ | _ | tm | t~ | refl | refl =
      fst= (prop-has-all-paths {{ TmP (₂ t) _ }} (_ , t~) (ΣTm~ (ΣCon~ (₂ Γ)) (ΣTy~ (ΣCon~ (₂ Γ)) (₂ A)) (₂ t)))


    Subʳ'= : ∀ {Γ Δ : S.Con}{σ : S.Sub Γ Δ} → Subʳ' σ == Subʳ σ
      [ (λ x → M.Sub (₁ x)(₂ x)) ↓ pair×= (Conʳ'= {Γ}) (Conʳ'= {Δ}) ]

    Subʳ'= {Γ}{Δ}{σ}
      with 
        Conʳ' Γ | Conʳ' Δ | Subʳ' σ | morSub~ (₂ Γ)(₂ Δ) (₂ σ) | Conʳ'= {Γ} | Conʳ'= {Δ}
    -- ... | Γm | Δm | σm | σ~ | eΓ | eΔ = {!!}
    Subʳ'= {Γ} {Δ} {σ} | .(₁ (ΣCon~ (₂ Γ))) | .(₁ (ΣCon~ (₂ Δ))) | σm | σ~ | refl | refl =
      fst= (prop-has-all-paths (_ , σ~) (ΣSub~ (ΣCon~ (₂ Γ)) (ΣCon~ (₂ Δ)) (₂ σ) ))

