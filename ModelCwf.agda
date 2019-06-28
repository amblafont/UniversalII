{-# OPTIONS  --rewriting  #-}
{-
TODO: réfélchir à de meilleures preuves

This file postulates a model which enjoys some rewrite rule for some equalities, in order
to simplify the construction of the recursor from the syntax.

Note that agda does not allow (yet?) to define a record with rewrite rules. That's why we postulate it.

The postulated rewrite rules are actually satisfied for the syntax seen as a model.

It would be nice if we later only use the recursor for models which actually satisifies
these equations definitionally.



-}



open import Level
open import Hott hiding (_∘_ ; _⁻¹ ; Π ; _$_)
open import monlib hiding (tr2)

module ModelCwf {k : Level.Level}   where

open import ModelRecord


-- infixl 7 _[_]T
-- infixl 5 _,s_
-- infix  6 _∘_
-- infixl 8 _[_]t
-- infixl 4 _▶_
module Postulats where

  postulate
    i : Level
    j : Level
    RewCwF : CwF {i} {j}

  open  CwF RewCwF


  -- Universe
  --------------------------------------------------------------------------------

  postulate
    U    : ∀{Γ} → Ty Γ
    -- U[]  : {Γ Δ : Con} {σ : Sub Γ Δ} → _≡_ {i} {Ty Γ} (_[_]T {Γ} {Δ} (U {Δ}) σ) (U {Γ})
    U[]  : {Γ Δ : Con} {σ : Sub Γ Δ} → _↦_ {i} {Ty Γ} (_[_]T {Γ} {Δ} (U {Δ}) σ) (U {Γ})
  {-# REWRITE U[]  #-}

  postulate
    El   : ∀{Γ}(a : Tm Γ U) → Ty Γ

    El[] :
      {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} →
      _↦_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (El {Δ} a) σ)
      (El {Γ} (a [ σ ]t))
  {-# REWRITE El[]  #-}



  -- Inductive function
  --------------------------------------------------------------------------------
  postulate
    Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ
    Π[] :
      {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)} →
      ((Π a B) [ σ ]T) ↦ Π (a [ σ ]t) (B [ (_^_  σ  (El a)) ]T)

  {-# REWRITE Π[]  #-}


  postulate
    -- app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
    app$ : ∀ {Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}(t : Tm Γ (Π a B))(u : Tm Γ (El a)) → Tm Γ (B [ < u > ]T)

  -- TODO: voir si on peut le demander en définitional: est ce la cas dans la syntaxe ?
    app$[] :
        ∀ {Y}{Γ}{σ : Sub Y Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}{t : Tm Γ (Π a B)}{u : Tm Γ (El a)}
        → ((app$ t u) [ σ ]t) == ( app$  (t [ σ ]t)  (u [ σ ]t)) [ Tm _ ↓ [<>][]T {Γ}{El a}{u}{B} ]


  -- Non-Inductive function
  --------------------------------------------------------------------------------
  postulate
    ΠNI : ∀{Γ}{T : Set k}(B : T → Ty Γ) → Ty Γ
    ΠNI[] :
      {Γ Δ : Con} {σ : Sub Γ Δ} {T : Set k} {B : T → Ty Δ} →
      ((ΠNI B) [ σ ]T) ↦ ΠNI  (λ b → (B b) [ σ ]T)
  {-# REWRITE ΠNI[]  #-}


  postulate
    -- app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
    app$NI : ∀ {Γ}{T : Set k}{B : T → Ty Γ}(t : Tm Γ (ΠNI B))(u : T) → Tm Γ (B u)

    app$NI[] :
        ∀ {Y}{Γ}{σ : Sub Y Γ}{T : Set k}{B : T → Ty Γ}{t : Tm Γ (ΠNI B)}{u : T}
        → ((app$NI t u) [ σ ]t) ↦ ( app$NI  (t [ σ ]t)  u)

  {-# REWRITE app$NI[]  #-}

  -- Infinitary parameters
  --------------------------------------------------------------------------------
  postulate
    ΠInf : ∀{Γ}{T : Set k}(B : T → Tm Γ U) → Tm Γ U
    ΠInf[] :
      {Γ Δ : Con} {σ : Sub Γ Δ} {T : Set k} {B : T → Tm Δ U} →
      ((ΠInf B) [ σ ]t) ↦ ΠInf  (λ b → (B b) [ σ ]t)
  {-# REWRITE ΠInf[]  #-}


  postulate
    -- app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
    app$Inf : ∀ {Γ}{T : Set k}{B : T → Tm Γ U}(t : Tm Γ (El (ΠInf B)))(u : T) → Tm Γ (El (B u))

    app$Inf[] :
        ∀ {Y}{Γ}{σ : Sub Y Γ}{T : Set k}{B : T → Tm Γ U}{t : Tm Γ (El (ΠInf B))}{u : T}
        → ((app$Inf t u) [ σ ]t) ↦ ( app$Inf  (t [ σ ]t)  u)

  {-# REWRITE app$Inf[]  #-}


  RewUnivΠ : UnivΠ {k = k} RewCwF
  RewUnivΠ = record
               { U = U
               ; U[] = refl
               ; El = El
               ; El[] = refl
               ; Π = Π
               ; Π[] = refl
               ; _$_ = app$
               ; $[] = app$[]
               ; _$NI_ = app$NI
               ; $NI[] = refl
               ; _$Inf_ = app$Inf
               ; $Inf[] = refl
               }

  open UnivΠ RewUnivΠ using (_$_ ; _$NI_ ; _$Inf_)

-- module ModelRew where
-- accessibles depuis l'exterieur
open Postulats public
open CwF RewCwF public
open UnivΠ RewUnivΠ using (_$_ ; $[] ; _$NI_ ; _$Inf_ ) public
