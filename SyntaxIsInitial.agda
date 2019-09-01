{-  copied from finitaryQiit/modelTemplate
some complementary lemmas about the syntax
           -}

{-# OPTIONS  --rewriting  #-}

open import Level
open import EqLib renaming (   fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )
  hiding (_∘_ ; _⁻¹ ; Π ; _$_)
open import Lib hiding (tr2)

module SyntaxIsInitial {k : Level}  where

open import Model

open import Syntax {i = k}
open import SyntaxIsModel {i = k} renaming (module Syn to S)

-- A: U, B : A -> U , ∙ : A , ▶ : (Γ : A) → B Γ → A , u : (Γ:A) → B Γ , el (Γ : A) →
-- ex1 : Con
-- ex1 = {!!}

import ModelRew {k = k} as M

open import ModelMorphism
open import RelationInhabit {k = k}
open import Relation {k = k}
open import RelationSubstitution {k = k}
-- open import ModelMorphismRew {k = k}

ΣConʳ : ∀ (Γ : S.Con) → ∃ (Con~ (₂ Γ))
ΣConʳ Γ = ΣCon~ (₂ Γ)

Conʳ : S.Con → M.Con
Conʳ = λ Γ → ₁ (ΣConʳ Γ)

ΣTyʳ : ∀ {Γ} → (A : S.Ty Γ) → ∃ (Ty~ (₂ A) {Conʳ Γ})
ΣTyʳ {Γ}A = ΣTy~ (ΣConʳ Γ) (₂ A)

Tyʳ  : ∀ {Γ} → S.Ty Γ → M.Ty (Conʳ Γ)
Tyʳ {Γ}A =   ₁ (ΣTyʳ A)

ΣTmʳ  : ∀ {Γ A} → (t : S.Tm Γ A) → ∃ (Tm~ (₂ t) {Conʳ Γ} {Tyʳ A})
ΣTmʳ {Γ}{A}t = (ΣTm~ (ΣConʳ  Γ) (ΣTyʳ A) (₂ t))


Tmʳ  : ∀ {Γ A} → S.Tm Γ A → M.Tm (Conʳ Γ) (Tyʳ A)
Tmʳ {Γ}{A}t = ₁ (ΣTmʳ t)

ΣSubʳ : ∀ {Γ Δ}(σ : S.Sub Γ Δ ) → ∃ (Sub~ (₂ σ ){Conʳ Γ} {Conʳ Δ})
ΣSubʳ {Γ}{Δ}σ = (ΣSub~ (ΣConʳ  Γ)(ΣConʳ  Δ)  (₂ σ))

Subʳ : ∀ {Γ Δ} → S.Sub Γ Δ → M.Sub (Conʳ Γ) (Conʳ Δ)
Subʳ {Γ}{Δ}σ = ₁ (ΣSubʳ σ)


[]Tʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ Δ} →
      Tyʳ (A S.[ σ ]T) ≡ Tyʳ A M.[ Subʳ σ ]T

[]Tʳ {Γ}{Δ}{A}{σ} =
  let Γm = (ΣCon~ (₂ Γ))
      Δm = (ΣCon~ (₂ Δ))
  in
  fst=
    (prop-path (TyP _ _)
      (ΣTyʳ (A S.[ σ ]T))
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

   tm[] : ∃ (Tm~ (Tmw[] (₂ t) (₂ Γ) (₂ σ)))
   -- tm[] = ΣTm~  Γm Am[] (₂ (t S.[ σ ]t))
   tm[] = ΣTmʳ  (t S.[ σ ]t)

   aux : ∀ (tm[]' : ∃ (Tm~ (Tmw[] (₂ t) (₂ Γ) (₂ σ)))) → ₁ tm[]' ==
           (Tmʳ {Δ} {A} t) M.[ Subʳ σ ]t
            [ M.Tm _  ↓ []Tʳ {A = A}{σ = σ} ]
            -- [ M.Tm _  ↓ {![]Tʳ {A = A}{σ = σ} = {!tm[]!}!} ]

   -- aux rewrite []Tʳ {A = A}{σ = σ} = {!tm[]!}
   aux tm[]' rewrite []Tʳ {A = A}{σ = σ} =

      fst=
        (prop-has-all-paths
          {{  TmP (Tmw[] (₂ t) (₂ Γ) (₂ σ)) ( Tyʳ A M.[ Subʳ σ ]T)  }}
          tm[]'
          (_ ,  Tm[]~ (ΣConʳ Γ) (ΣConʳ Δ) (ΣSubʳ σ) {tw = ₂ t}(ΣTmʳ t) )
        )

idʳ : {Γ : S.Con} → Subʳ {Γ = Γ} S.id ≡ M.id
idʳ {Γ} = fst=
             (prop-path (SubP _ _ _)
               (ΣSubʳ S.id )
               (_ , id~ (ΣConʳ Γ))
              )

-- π₁ʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
--       Subʳ (S.π₁ σ) ≡ M.π₁  (Subʳ σ)

-- π₁ʳ {Γ} {Δ} {A} {.(_ :: _) , ,sw Δw σw Aw tw} = {!refl!}


,sʳ :  {Γ Δ : S.Con} {σ : S.Sub Γ Δ} {A : S.Ty Δ}
      {t : S.Tm Γ (A S.[ σ ]T)} →
      Subʳ (σ S.,s t) ≡ (Subʳ σ M.,s tr (M.Tm (Conʳ Γ)) ([]Tʳ {A = A}{σ = σ}) (Tmʳ t))
      -- it should computes here..
,sʳ {Γ}{Δ}{σ}{A}{t} =
   helper _
   where
     tm = ΣTm~ (ΣConʳ Γ)(_ , Ty[]~ (ΣConʳ Γ)(ΣConʳ Δ) (ΣSubʳ σ)(ΣTyʳ A))  (₂ t)


     eq : ∀ {B : M.Ty (Conʳ Γ)}(p : Tyʳ (A S.[ σ ]T) ≡ B)
          -- (tm' : Σ (M.Tm (₁ (ΣConʳ Γ)) (₁ (ΣTyʳ A) M.[ ₁ (ΣSubʳ σ) ]T))(Tm~ (₂ t))) →
          (tm' : Σ (M.Tm (₁ (ΣConʳ Γ)) B)(Tm~ (₂ t))) →
       ₁ tm' ≡ tr (M.Tm (Conʳ Γ)) p (Tmʳ t)
       -- ₁ tm' ≡ tr (M.Tm (Conʳ Γ)) ([]Tʳ {A = A}{σ} ) (Tmʳ t)
     eq refl tm' = fst= (prop-has-all-paths {{ TmP (₂ t) _ }} tm' (ΣTmʳ t))
     -- ! (to-transp {B = M.Tm (Conʳ Γ)}{p = []Tʳ {A = A}{σ} }{!₁ tm!})

     helper : ∀ e →
       transport! (M.Sub (Conʳ Γ)) e
        (Subʳ σ M.,s ₁ tm)
      ≡ (Subʳ σ M.,s tr (M.Tm (Conʳ Γ)) ([]Tʳ {A = A}{σ = σ}) (Tmʳ t))
     helper refl =
       ap (λ u →  (Subʳ σ) M.,s u)
         ( eq ([]Tʳ {A = A}{σ = σ}) tm )

∘ʳ : {Γ Δ : S.Con} {Σ₁ : S.Con} {σ : S.Sub Δ Σ₁}
      {δ : S.Sub Γ Δ} →
      Subʳ (σ S.∘ δ) ≡ Subʳ σ M.∘ Subʳ δ

∘ʳ {Γ}{Δ}{Y}{σ}{δ }  =
  fst=
             (prop-path (SubP _ _ _)
               (ΣSubʳ (σ S.∘ δ) )
               (_ , ∘~ (ΣConʳ Δ)(ΣConʳ Y)(ΣSubʳ σ)(ΣConʳ Γ)(ΣSubʳ δ))
              )



iniMor : CwFMor syntaxCwF M.RewCwF
iniMor = record
           {  Conʳ = Conʳ
           ; Tyʳ = Tyʳ
           ; Tmʳ = Tmʳ
           ; Subʳ = Subʳ
           ; ,ʳ = refl
           ; ∙ʳ = refl
           ; []Tʳ = λ {Γ}{Δ}{A}{σ} → []Tʳ {A = A}{σ = σ}
           ; []tʳ = λ{Γ}{Δ}{A}{t}{σ} → []tʳ {t = t}{σ = σ}
           ; idʳ = λ{Γ}→ idʳ {Γ}
           -- tiens? Est-ce nécessaire ?
           ; ∘ʳ =  λ {Γ}{Δ}{Y}{σ}{δ } → ∘ʳ{Γ}{Δ}{Y}{σ}{δ}
           ; εʳ = refl
           -- ça devrait calculer ici par refl ! TODO: réfléchir à pourquoi ce n'est pas le
           -- cas
           ; ,sʳ = λ {Γ}{Δ}{σ}{A}{t} → ,sʳ {Γ}{Δ}{σ}{A}{t}
           -- ; π₁ʳ = λ {Γ}{Δ}{A}{σ} → {! π₁ʳ {A = A}{σ = σ} !}
           -- ; π₂ʳ = {!!}
           }

iniUnivMor : UnivMor syntaxUnivΠ M.RewUnivΠ iniMor
iniUnivMor = record {
    Uʳ = refl ;
    Elʳ = refl
  }


$ʳ~ : ∀ {Γ}{a : S.Tm Γ S.U}{B : S.Ty (Γ S.▶ S.El a)}(t : S.Tm Γ (S.Π a B))
  (u : S.Tm Γ (S.El a))
  -- {Γm}{Am}(tm : Σ )
   → Tm~ (₂ (t S.$ u)) ((Tmʳ {A = (S.Π a B)}t) M.$ (Tmʳ {A = S.El a} u))

-- $ʳ~ {Γ}{a}{B}t u tm um = ?
$ʳ~ {Γ}{a}{B}t u
    =
   tr {A = ∃  λ C →  (₁ Γ) ⊢ (app (₁ t) (₁ u) ) ∈ C   }
     (λ x → Tm~ {A = ₁ x}(₂ x) (Tmʳ t M.$ Tmʳ u))
     {x = _ , tuw }
     {y = (₁ (B S.[ S.< u > ]T)) , ₂ (t S.$ u)}
     (pair=
       (₁[<>]T {B = B}{u = u})
       (from-transp _ _ (prop-has-all-paths _ _)))
     helper
  where
    tuw = (appw  (₂ Γ)  (₂ a)  (₂ B)  (₂ t)  (₂ u))

    helper : Tm~ tuw
      ( (Tmʳ {A = (S.Π a B)}t) M.$ (Tmʳ {A = S.El a} u))
    helper =
      ΣTmʳ a ,
      ΣTyʳ B ,
      ΣTmʳ t ,
      ΣTmʳ u ,
      refl ,
      refl

$ʳ : ∀ {Γ}{a : S.Tm Γ S.U}{B : S.Ty (Γ S.▶ S.El a)}(t : S.Tm Γ (S.Π a B))
      (u : S.Tm Γ (S.El a)) e →
    Tmʳ (t S.$ u)
    -- ₁ (ΣTm~ (ΣCon~ (₂ Γ)) (ΣTy~ (ΣCon~ (₂ Γ)) (₂ (B S.[ S.< u > ]T)))
    --   (
    --   tr (λ B' → Tmw (₁ Γ) B' (app (₁ t) (₁ u))) (₁[<>]T {A = El a}{B = B}{u} )
    --   (appw (₁ Γ) (₂ Γ) (₁ a) (₂ a) (₁ B) (₂ B) (₁ t) (₂ t) (₁ u) (₂ u)))
    -- )
    ==
      ((Tmʳ {A = (S.Π a B)}t) M.$ (Tmʳ {A = S.El a} u)) [ M.Tm _ ↓
      e
        ]
$ʳ {Γ}{a}{B}t u e
  =
    helper e ($ʳ~ t u)
    where
      helper : ∀ {A }(p : Tyʳ (B S.[ S.< u > ]T) ≡ A) {tu : _}(tu~ : Tm~ (₂ (t S.$ u)) tu) →
        Tmʳ (t S.$ u) == tu [ M.Tm _ ↓ p ]
      helper refl tu~ = fst=
        (prop-has-all-paths {{  TmP (₂ (t S.$ u)) (Tyʳ (B S.[ S.< u > ]T) )  }}
        (ΣTmʳ (t S.$ u))
        (_ , tu~))

$NIʳ : ∀ {Γ}{T : Set k}{B : T → S.Ty Γ}(t : S.Tm Γ (S.ΠNI B))
      (u : T)  →
    Tmʳ (t S.$NI u)
    ≡
      ((Tmʳ {A = (S.ΠNI B)}t) M.$NI u)
      -- [ M.Tm _ ↓ e]

$NIʳ {T = T}{B = B}t u =
  ap (λ e → coe! e (M._$NI_ (Tmʳ t) u)) {y = refl} (uip _ _)

$Infʳ : ∀ {Γ}{T : Set k}{B : T → S.Tm Γ S.U}(t : S.Tm Γ (S.El (S.ΠInf B)))
      (u : T)  →
    Tmʳ (t S.$Inf u)
    ≡
      ((Tmʳ {A = (S.El (S.ΠInf B))}t) M.$Inf u)
$Infʳ {T = T}{B = B}t u =
   ap (λ e → coe! e (M._$Inf_ (Tmʳ t) u)) {y = refl} (uip _ _)


iniMorUnivΠ : UnivΠMor syntaxUnivΠ M.RewUnivΠ iniMor
iniMorUnivΠ = record {
  univmor = iniUnivMor
  -- record {
  --   Uʳ = refl ;
  --   Elʳ = refl }
    ;
  Πmor = record {
  Πʳ = refl ;
  -- réfléchir à pourquoi ce n'est pas le cas
  -- I think refl doesn't work because app is primitive in the model rather than _$_
  -- (especially in the model morphism in fact)
  -- $ʳ = {!λ {Γ}{a}{b}t u → $ʳ {Γ}{a}{b} t u!} }
  -- So slow!!!
  -- $ʳ = λ {Γ}{a}{b}t u {e} q → $ʳ {Γ}{a}{b} t u _
  $ʳ = λ {Γ}{a}{b}t u → $ʳ {Γ}{a}{b} t u _ ;
  ΠNIʳ = refl ;
  $NIʳ = λ t u → $NIʳ t u ;
  ΠInfʳ = refl ;
  $Infʳ = λ t u → $Infʳ t u
  }
  }


{- ----------

Uniqueness:
we postulate a morphism (with some rewrite rules) and show that it is equals
to the one we constructed


-}

module Mor where
  open import ModelMorphismRew {k = k} public
  open CwFMor m1 public
  open UnivΠMor m2 public

-- uniqueness
Conʳ'= : ∀ {Γ : S.Con} → Mor.Conʳ Γ ≡ Conʳ Γ
Conʳ'= {Γ} = fst= (prop-path (ConP _) (_ , Mor.morCon~ (₂ Γ)) (ΣCon~ (₂ Γ)))

Tyʳ'= : ∀ {Γ : S.Con}{A : S.Ty Γ} → Mor.Tyʳ A == Tyʳ A [ M.Ty ↓ Conʳ'= {Γ} ]

Tyʳ'= {Γ}{A} with Mor.Conʳ Γ | Mor.Tyʳ A | Mor.morTy~ (₂ Γ) (₂ A) | Conʳ'= {Γ}
-- ...   | Γm | Am | A~ | e = {!e!}
Tyʳ'= {Γ} {A} | .(₁ (ΣCon~ (₂ Γ))) | Am | A~ | refl =
  fst= (prop-path (TyP _ _) (_ , A~) (ΣTyʳ A  ))

Tmʳ'= : ∀ {Γ : S.Con}{A}{t : S.Tm Γ A} → Mor.Tmʳ t == Tmʳ t
  [ (λ x → M.Tm (₁ x)(₂ x)) ↓ pair= (Conʳ'= {Γ}) (Tyʳ'= {Γ} {A}) ]

Tmʳ'= {Γ}{A}{t}
  with
    Mor.Conʳ Γ | Mor.Tyʳ A | Mor.Tmʳ t | Mor.morTm~ (₂ Γ)(₂ A) (₂ t) | Conʳ'= {Γ} | Tyʳ'= {Γ}{A}

-- ... | Γm | Am | tm | t~ | eΓ | eA = {!eΓ!}
... | _ | _ | tm | t~ | refl | refl =
  fst= (prop-has-all-paths {{ TmP (₂ t) _ }} (_ , t~)
      -- (ΣTm~ (ΣCon~ (₂ Γ)) (ΣTy~ (ΣCon~ (₂ Γ)) (₂ A)) (₂ t)))
      (ΣTmʳ t))


Subʳ'= : ∀ {Γ Δ : S.Con}{σ : S.Sub Γ Δ} → Mor.Subʳ σ == Subʳ σ
  [ (λ x → M.Sub (₁ x)(₂ x)) ↓ pair×= (Conʳ'= {Γ}) (Conʳ'= {Δ}) ]

Subʳ'= {Γ}{Δ}{σ}
  with
    Mor.Conʳ Γ | Mor.Conʳ Δ | Mor.Subʳ σ | Mor.morSub~ (₂ Γ)(₂ Δ) (₂ σ) | Conʳ'= {Γ} | Conʳ'= {Δ}
-- ... | Γm | Δm | σm | σ~ | eΓ | eΔ = {!!}
Subʳ'= {Γ} {Δ} {σ} | .(₁ (ΣCon~ (₂ Γ))) | .(₁ (ΣCon~ (₂ Δ))) | σm | σ~ | refl | refl =
  fst= (prop-path (SubP _ _ _) (_ , σ~) (ΣSubʳ σ))
