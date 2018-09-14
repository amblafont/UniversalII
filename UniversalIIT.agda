{-# OPTIONS  --rewriting #-}
-- an attempt with rewrite rules, but by postulating the model rather than defining a record (because rewrite rules don't work)

-- open import HoTT.Base
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
module UniversalIIT where
-- {-# REWRITE apply-false #-}


-- open import Lib renaming (_Σ,_ to _,_)
-- open import Lib renaming (_Σ,_ to _,_)

-- Intrinsic models
--------------------------------------------------------------------------------

module Model1 {ℓ}  where
  infixl 5 _▶_
  infixl 5 _^^_
  postulate
    Con  : Set ℓ
    Telescope : Con → Set ℓ
    Ty   : Con → Set ℓ
    Tm   : (Γ : Con) → Ty Γ → Set ℓ
    -- Var   : (Γ : Con) → Ty Γ → Set ℓ

    ∙    : Con
    _▶_  : (Γ : Con) → Ty Γ → Con


    _^^_ : (Γ : Con)(Δ : Telescope Γ) → Con

    ∙t    : ∀ Γ → Telescope Γ
    _▶t_  : ∀ {Γ}(Δ : Telescope Γ) → Ty (Γ ^^ Δ) → Telescope Γ

    ^^∙t : (Γ : Con) → (Γ ^^ ∙t Γ) ↦ Γ
    ^^▶t : (Γ : Con)(Δ : Telescope Γ)(A : Ty (Γ ^^ Δ)) →
      (Γ ^^ (Δ ▶t A)) ↦ ((Γ ^^ Δ) ▶ A)




    U    : (Γ : Con) → Ty Γ
    El   : (Γ : Con) → Tm Γ (U Γ) → Ty Γ
    ΠΠ    : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ


    wkC : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ) → Telescope (Γ ▶ Ex)

    wk∙t : (Γ : Con)(Ex : Ty Γ) → wkC Γ Ex (∙t _) ↦ ∙t _

  {-# REWRITE ^^∙t  #-}
  {-# REWRITE ^^▶t  #-}
  {-# REWRITE wk∙t  #-}

  postulate

    liftT : (Γ : Con)(Δ : Telescope Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ)) → Ty ((Γ ▶ Ex) ^^ wkC Γ Ex Δ)
    liftt : (Γ : Con)(Δ : Telescope Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ))(t : Tm _ A) →
      Tm ((Γ ▶ Ex) ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A)

    -- wk▶t : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ)
    --   (A : Ty (Γ ^^ Δ)) → ((Γ ▶ Ex) ^^ wkC Γ Ex (Δ ▶t A)) ↦ (((Γ ▶ Ex) ^^ (wkC Γ Ex Δ)) ▶ liftT Γ Δ Ex A)
    wk▶t : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ)(A : Ty (Γ ^^ Δ)) →
      (wkC Γ Ex (Δ ▶t A)) ↦ ((wkC Γ Ex Δ) ▶t liftT Γ Δ Ex A)



  {-# REWRITE wk▶t  #-}

  wkT : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ) → Ty (Γ ▶ Ex)
  wkT Γ Ex A = liftT Γ (∙t Γ) Ex A

  wkt : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ)(t : Tm Γ A) → Tm (Γ ▶ Ex) (wkT Γ Ex A)
  wkt Γ Ex A t = liftt Γ (∙t Γ) Ex A t

  postulate
    V0 : (Γ : Con)(A : Ty Γ) → Tm (Γ ▶ A) (wkT Γ A A)
    -- VS : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ) (x : Var Γ A) → Var (Γ ▶ Ex) (wkT Γ Ex A)

    subT : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → Ty (Γ ▶ Ex) → Ty Γ
    subt : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → (A : Ty (Γ ▶ Ex) ) (u : Tm _ A )→ Tm Γ (subT Γ Ex t A)

    -- v : (Γ : Con)(A : Ty Γ)(x : Var Γ A) → Tm Γ A
    app : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) (t : Tm Γ (ΠΠ Γ A B)) (u : Tm Γ A) →
      Tm Γ (subT Γ A u B)


-- Presyntax
--------------------------------------------------------------------------------

infixl 6 _▶p_

data Conp : Set
data Typ  : Set
data Tmp : Set
-- data Varp : Set

data Conp where
  ∙p   : Conp
  _▶p_ : Conp → Typ → Conp

data Typ where
  Up  : Typ
  Elp : Tmp → Typ
  ΠΠp  : Typ → Typ → Typ

data Tmp where
  V : ℕ → Tmp
  app : Tmp → Tmp → Tmp


-- data Varp where
--   v0 : Conp → Typ → Varp  
--   vS : Conp → Typ → Varp → Typ → Varp

-- first integer : we don't touch variables below
liftT : ℕ → Typ → Typ
liftt : ℕ → Tmp → Tmp
liftV : ℕ → ℕ → ℕ

liftT p Up = Up
liftT p (Elp x) = Elp (liftt p x)
-- Γ , Δ ⊢ A
-- Γ , C , wkC Δ ⊢ w_Δ A
-- Γ , Δ , A ⊢ B
-- Γ , C , wkC Δ , wk_Δ A ⊢ w_Δ+1 B
liftT p (ΠΠp A B) = ΠΠp (liftT p A) (liftT (1 + p) B)

liftt n (V x) = V (liftV n x)
liftt n (app t u) = app (liftt n t)(liftt n u)

-- x if x < n and S x otherwise
liftV O x = S x
liftV (S n) O = 0
liftV (S n) (S x) = S (liftV n x)

wkT : Typ → Typ
wkT  = liftT 0

wkt : Tmp → Tmp
wkt = liftt 0

-- Γ ⊢ t : ∏ A B
-- Γ ⊢ u : A
-- -----------
-- Γ ⊢ t u : B [0 <- u; S n <- n]

-- Γ , C , p ⊢ A   Γ ⊢ t : C
-- Γ , p ⊢ A [p <-- t ; (S n > p) <-- n]

-- l-subT p l T = T [ p <-- l ; (n > p) <-- V (n-1)
-- the idea being:
--    Γ , C , p ⊢ A    et    Γ ⊢ t : C
--   then Γ , p ⊢ l-subT p t A
l-subT : (p : ℕ)(l : Tmp) (T : Typ) → Typ
l-subt : (p : ℕ)(l : Tmp) (t : Tmp) → Tmp
l-subV : (p : ℕ)(l : Tmp) (x : ℕ) → Tmp

-- don't touch if it is below p
l-subV O l O = l
l-subV O l (S x) = V x
l-subV (S p) l O = V 0
-- Γ , C , p+1 ⊢ x+1   (and Γ ⊢ t : C)
-- donc Γ , C , p ⊢  x   (and Γ ⊢ t : C)
-- donc Γ , p ⊢ l-sub p t x
-- donc Γ , p+1 ⊢ wk (l-sub p t x)

-- prenons l'exemple x = 0 et p = 2. On veut que wk (l-sub p t x) = 1
-- Or, l-sub 2 t 0 = V 0
l-subV (S p) l (S x) = wkt (l-subV p l x)

l-subt p l (V x) = (l-subV p l x)
l-subt p l (app t u) = app (l-subt p l t)(l-subt p l u)

l-subT p l Up = Up
l-subT p l (Elp x) = Elp (l-subt p l x)
-- Γ , C , p,  A ⊢ B and Γ ⊢ t : C
-- then Γ , p , A ⊢ l-sub p+1 t B
l-subT p l (ΠΠp A B) = ΠΠp (l-subT p l A) (l-subT (1 + p) l B)

subT : (l : Tmp) (T : Typ) → Typ
subt : (l : Tmp) (t : Tmp) → Tmp
subV : (l : Tmp) (x : ℕ) → Tmp

subT = l-subT 0
subt = l-subt 0
subV = l-subV 0
-- first integer : we don't touch variables below
-- second integer : we add it to the other variables
-- Γ, Δ ⊢ A
-- Γ , E , Δ ⊢ lift |Δ| |E| A

-- liftT : ℕ → ℕ → Typ → Typ
-- liftt : ℕ → ℕ → Tmp → Tmp
-- liftV : ℕ → ℕ → Varp → Varp

-- liftT p q (Up Γ) = {!!}
-- liftT p q (Elp Γ) = {!!}
-- liftT p q (ΠΠp Γ A B) = {!!}

-- liftt p q (V Γ A n) = {!!}

-- liftV p q (v0 x x₁) = {!!}
-- liftV p q (vS x x₁ x₂ x₃) = {!!}

-- wkC : Conp → Oconp → Typ → Oconp

{-

Con2p : Conp → Type
  ∙2 : (Γ : Conp) → Con2p Γ
  ▶2 : Γ , 

wkC Γ n A =

-}

-- wkT : ℕ → Typ → Typ → Typ
-- wkTm : ℕ → Typ → Tm → Tm
-- wkV : ℕ → Typ → Var → Var

-- wkT n Wp (Up Γp) = Up (Γp ▶p Wp)
-- wkT n Wp (Elp Γp) = Elp (Γp ▶p Wp)
-- wkT n Wp (ΠΠp Γp Ap Bp) = {!ΠΠ (Γp ▶p Wp)!}

-- wkTm n Wp (V Γp Ap xp) = {!!}

-- wkV n Wp (v0 Γp Ap) = {!!}
-- wkV n Wp (vS Γp Ap xp Bp) = {!!}



  
-- Well-formedness predicates
--------------------------------------------------------------------------------

-- It is easy to show that w is propositional, but we don't actually
-- need that proof here. Also, note that Tyw Γ A implies Conw Γ.
data Conw : (Γp : Conp) → Set
data Tyw  : Conp → (Ap : Typ)   → Set
data Tmw : Conp → Typ →   Tmp → Set
data Varw : Conp → Typ → ℕ → Set


data Conw where
  ∙w : Conw ∙p
  ▶w : ∀ {Γp} (Γw : Conw Γp){Ap}(Aw : Tyw Γp Ap) → Conw (Γp ▶p Ap)
data Tyw where
  Uw : (Γp : Conp)(Γw : Conw Γp) → Tyw Γp Up
  Πw : ∀ {Γp : Conp}(Γw : Conw Γp){ap : Tmp}(Aw : Tmw Γp Up ap){Bp : Typ}(Bw : Tyw (Γp ▶p Elp ap) Bp)
    → Tyw Γp (ΠΠp (Elp ap) Bp)
  Elw : ∀ {Γp}(Γw : Conw Γp){ap}(aw : Tmw Γp Up ap) → Tyw Γp (Elp ap)
data Tmw where
  vw : ∀ {Γp} {Ap : Typ}{xp : ℕ}(xw : Varw Γp Ap xp) →
    Tmw Γp Ap (V xp)
  appw : (Γp : Conp)(Γw : Conw Γp)(ap : Tmp)(aw : Tmw Γp Up ap)(Bp : Typ)
     (Bw : Tyw (Γp ▶p Elp ap ) Bp)
     (t : Tmp)(tw : Tmw Γp (ΠΠp (Elp ap) Bp) t)
     (u : Tmp)(tw : Tmw Γp (Elp ap) u)
     → Tmw Γp (subT u Bp) (app t u)
data Varw where
  V0w : (Γp : Conp) (Γw : Conw Γp) (Ap : Typ) (Aw : Tyw Γp Ap) → Varw (Γp ▶p Ap) (wkT Ap) 0
  VSw : (Γp : Conp) (Γw : Conw Γp) (Ap : Typ) (Aw : Tyw Γp Ap)
     (Bp : Typ) (Bw : Tyw Γp Bp)(xp : ℕ)(xw : Varw Γp Bp xp)
     → Varw (Γp ▶p Ap) (wkT Bp) (1 + xp)
 
-- wkTw is not enough : consider the Π case.
-- what we need : Γ , Δ ⊢ Bp, then Γ , A , wkC Δ ⊢ lift |Δ| Bp

-- liftC : ℕ → Conp → Conp
-- liftC p Δ = {!!}


infixl 5 _^^_
_^^_ : Conp → Conp → Conp

Γ ^^ ∙p = Γ
Γ ^^ (Δ ▶p x) =  (Γ ^^ Δ) ▶p x

∣_∣ : Conp → ℕ
∣ ∙p ∣ = 0
∣ Γ ▶p x ∣ = S ∣ Γ ∣

wkC : Conp → Conp
wkC ∙p = ∙p
wkC (Γ ▶p A) = wkC Γ ▶p liftT ∣ Γ ∣ A

-- OConw : Conp → Conp → Set
-- OConw Γp ∙p = Conw Γp
-- OConw Γp (Δp ▶p x) = OConw Γp Δp × Tyw (Γp ^^ Δp) x
-- data OConw : Conp → Conp → Set
-- data OConw where
--   o∙ : {Γ : Conp}(Γw : Conw Γ) → OConw Γ ∙p
--   o▶ : {Γ : Conp}{Δ : Conp}(Δw : OConw Γ Δ)


-- rec on Δp
-- wkCw : ∀ Γp Δp (Δw : OConw Γp Δp) {Ap} (Aw : Tyw Γp Ap) → OConw (Γp ▶p Ap) (wkC Δp)
-- wkCw Γp ∙p Δw {Ap} Aw = ▶w Δw Aw
-- wkCw Γp (Δp ▶p x) Δw {Ap} Aw = (wkCw Γp Δp (₁ Δw) Aw) , {!!}

-- do we really need to show this ?
wkCw' : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp (Δw : Conw (Γp ^^ Δp)) → Conw ((Γp ▶p Ap) ^^ wkC Δp)
liftTw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp{Bp}(Bw : Tyw (Γp ^^ Δp) Bp) → Tyw ((Γp ▶p Ap) ^^ wkC Δp) (liftT ∣ Δp ∣ Bp)
lifttw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp{Bp}{tp}(tw : Tmw (Γp ^^ Δp) Bp tp) →
  Tmw ((Γp ▶p Ap) ^^ wkC Δp) (liftT ∣ Δp ∣ Bp) (liftt ∣ Δp ∣ tp)
liftVw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp{Bp}{xp}(xw : Varw (Γp ^^ Δp) Bp xp) →
  Varw ((Γp ▶p Ap) ^^ wkC Δp) (liftT ∣ Δp ∣ Bp) (liftV ∣ Δp ∣ xp)

wkCw'  Aw ∙p Δw = ▶w Δw Aw
wkCw' Aw (Δp ▶p Bp) (▶w Δw Bw)  = ▶w (wkCw' Aw Δp Δw) (liftTw Aw Δp Bw)

liftTw Aw Δp (Uw .(_ ^^ Δp) Γw) = Uw _ (wkCw' Aw Δp Γw)
liftTw Aw Δp (Πw Γw {ap = ap} aw Bw) = Πw (wkCw' Aw Δp Γw)
   (lifttw Aw Δp aw ) (liftTw Aw (Δp ▶p Elp ap) Bw)
   -- (liftTw Aw {!!} {!!})
liftTw Aw Δp (Elw Γw {ap = ap} aw) = Elw (wkCw' Aw Δp Γw) (lifttw Aw Δp aw)


lifttw Aw Δp (vw xw) = vw (liftVw Aw Δp xw)
lifttw Aw Δp (appw .(_ ^^ Δp) Γw ap aw Bp Bw t tw u uw) =
   
   HoTT.transport (λ x → Tmw _ x _) {!!}
   (appw _ (wkCw' Aw Δp Γw) _ (lifttw Aw Δp aw) _ (liftTw Aw (Δp ▶p Elp ap) Bw)
   (liftt ∣ Δp ∣ t) (lifttw Aw Δp tw) (liftt ∣ Δp ∣ u) (lifttw Aw Δp uw)
   )
   

-- liftVw Aw ∙p xw = VSw _ {!!} _ Aw _ {!!} _ xw
liftVw {Ap = Bp} Bw ∙p (V0w Γp Γw Ap Aw) = VSw (Γp ▶p Ap) (▶w Γw Aw) Bp Bw (wkT Ap)
   (liftTw Aw ∙p Aw) 0 (V0w Γp Γw Ap Aw)
liftVw Aw ∙p (VSw Γp Γw Ap Aw' Bp Bw xp xw) =
  VSw _ (▶w Γw Aw') _ Aw _ (liftTw Aw' ∙p Bw) _ (VSw Γp Γw Ap Aw' Bp Bw xp xw)

liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (V0w .(_ ^^ Δp) Γw .Bp Aw) =
  HoTT.transport (λ x → Varw (((Γp ▶p T) ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Bp) x 0) {!!}
     (V0w ((Γp ▶p T) ^^ wkC Δp) (wkCw' Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Aw))
liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (VSw .(_ ^^ Δp) Γw .Bp Bw Ap Aw xp xw) =
  HoTT.transport (λ x → Varw _ x _)  {!!}
   (VSw ((Γp ▶p T) ^^ wkC Δp) (wkCw' Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Bw)
   _ (liftTw Tw Δp Aw) _ (liftVw Tw Δp xw))
   

wkTw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap){Bp}(Bw : Tyw Γp Bp) → Tyw (Γp ▶p Ap) (wkT Bp)
wkTw Aw Bw = liftTw Aw ∙p Bw 

{-

Lemmas about commutations of lift
TODO: demander à Theo

-}
comm_liftV : ∀ p q → liftV (S p) (liftV 0 q) ≡ liftV 0 (liftV p q)
comm_liftV p q = {!!}

comm_liftT : ∀ p q → liftT (S p) (liftT 0 q) ≡ liftT 0 (liftT p q)
comm_liftT p q = {!!}


-- wktw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap){tp}{Bp}(tw : Tmw Γp Bp tp) → Tmw (Γp ▶p Ap) (liftT 1 Bp) (liftt 1 tp)

-- wkTw Aw (Uw Γp Γw) = Uw _ (▶w Γw Aw)
-- wkTw Aw (Πw {Γp} Γw {ap} aw {Bp} Bw) = Πw (▶w Γw Aw) (wktw _ _) {!!}

-- wktw {Γp}{Ap} Aw {tp}{Bp} tw = {!!}
-- Varw : (xp : Varp) → Typ → Conp → Set

-- Conw ∙p = ⊤
-- Conw (Γp ▶p Ap) = ?

-- Tyw (Up Γp) Δp = Conw Γp × (Γp ≡ Δp)
-- Tyw (Elp Γp) Δp = Conw Γp × ((Γp ▶p Up Γp) ≡ Δp)
-- Tyw (ΠΠp Γp Ap Bp) Δp = Conw Γp × Tyw Ap Γp × Tyw Bp (Γp ▶p Ap) × (Γp ≡ Δp)

-- Tmw (V Γp Ap xp) Bp Δp = {!!}
-- Varw xp Bp Δp × ( Γp ≡ Δp) × (Ap ≡ Bp)

-- needs weakening
-- Varw (v0 Γp Ap) Bp Δp = Conw Γp × Tyw Ap Γp × ({!!} ≡ Bp) × ((Γp ▶p Ap) ≡ Δp)
-- Varw (vS Γp Ap xp Cp) Bp Δp = Conw Γp × Tyw Ap Γp × Varw xp Ap Γp × ({!!} ≡ Bp) × ((Γp ▶p Cp) ≡ Δp)

-- Conw and Tyw are hprop (needed for the uniqueness of the recursor)
-- ConwP : (Γp : Conp) → is-prop (Conw Γp)
-- TywP : (Γp : Conp)(Ap : Typ)  → is-prop (Tyw Ap Γp)

-- ConwP ∙p = {!!}
-- ConwP (Γp ▶p Ap) = ×-level (ConwP Γp) (TywP Γp Ap)

-- need to show that the syntax is a hset
-- TywP Γp (Up Δp) = ×-level (ConwP Δp) {!!}
-- TywP Γp (ΠΠp Δp Ap Bp) = ×-level (ConwP Δp) (×-level (TywP Δp Ap) (×-level (TywP (Δp ▶p Ap) Bp) {!!}))
-- TywP Γp (Elp Δp) = ×-level (ConwP Δp) {!!}

-- Inductive-inductive syntax
--------------------------------------------------------------------------------

{-
syn : Model {lzero}
syn = record {
    Con = Σ Conp Conw
  ; Ty  = λ {(Γp , _) → Σ Typ λ Ap → Tyw Ap Γp}
  ; ∙   = ∙p , tt
  ; _▶_ = λ {(Γp , Γw) (Ap , Aw) → (Γp ▶p Ap) , Γw , Aw}
  ; U   = λ {(Γp , Γw) → Up Γp , Γw , refl}
  ; El  = λ {(Γp , Γw) → Elp Γp , Γw , refl}
  ; ΠΠ   = λ {(Γp , Γw)(Ap , Aw)(Bp , Bw) → ΠΠp Γp Ap Bp , Γw , Aw , Bw , refl}}

-}
-- module Syn = ConTy ConTySyn

-- Recursion for inductive-inductive syntax
--------------------------------------------------------------------------------


module _ {α} where
  module M = Model1 {α}






  instance
    ConwP : (Γp : Conp) → is-prop (Conw Γp)
    TywP : (Γp : Conp)(Ap : Typ)  → is-prop (Tyw Γp Ap)
    VarwP : (Γp : Conp)(Ap : Typ)(xp : ℕ)  → is-prop (Varw Γp Ap xp)

    ConwP = {!!}
    TywP = {!!}
    VarwP = {!!}

  -- ConC : (Γp : Conp) → Conw Γp → is-contr (Σ M.Con λ Γm → Con~ Γp Γm)
  -- TyC : (Ap : Typ)(Γp : Conp) → Tyw Ap Γp → (Γm : M.Con) → Con~ Γp Γm → is-contr (Σ (M.Ty Γm) λ Am → Ty~ Ap (Γm , Am))
  
  -- Logical relation between the presyntax and the M model expressing
  -- that presyntactic and semantic values have the same structure
  -- in these versions, we assume for Ty~' that Γm is already realted to Γw
  -- and the same for Tm~'  and Var~' (although Var~' enforces that Γm is related to Γw)
  -- the advantage : I won't need to show that Ty~' implies Con~'
  -- However I would still need to prove that _w are HProp (consider you would state
  --   the main theorem for Ty~' and the case of context extension)
  Con~' : (Γp : Conp)(Γw : Conw Γp) → M.Con → Set α
  Ty~'  : (Γp : Conp)(Ap : Typ)(Aw : Tyw Γp Ap) (Δm : M.Con) (Cm : M.Ty Δm)  → Set α
  Tm~'  : (Γp : Conp)(Ap : Typ)(tp : Tmp)(tw : Tmw Γp Ap tp)(Δm : M.Con)(Cm : M.Ty Δm)(zm : M.Tm _ Cm)  → Set α
  Var~'  : (Γp : Conp)(Ap : Typ)(xp : ℕ)(xw : Varw Γp Ap xp)(Δm : M.Con)(Cm : M.Ty Δm)(zm : M.Tm _ Cm)  → Set α

  Con~' .∙p ∙w Γm = Γm ≡ M.∙
  Con~' .(Γp ▶p Ap) (▶w {Γp} Γw {Ap} Aw) Δm =
    Σ (Σ _ (Con~' _ Γw))
    λ Γm → Σ (Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    λ Am → Δm ≡ (₁ Γm M.▶ ₁ Am )

  Ty~' Γp .Up (Uw .Γp Γw) Δm Cm = Cm ≡ M.U Δm
  Ty~' Γp .(ΠΠp (Elp ap) Bp) (Πw  Γw {ap} Aw {Bp} Bw) Δm Cm =
    Σ (Σ _ (Tm~' _ _ ap Aw Δm (M.U Δm) ))
    λ am → Σ (Σ _ (Ty~' _ Bp Bw (Δm M.▶ M.El Δm  (₁ am))))
    λ Bm → Cm ≡ M.ΠΠ Δm _ (₁ Bm)
  Ty~' Γp _ (Elw Γw aw) Δm Cm =
    Σ (Σ _ (Tm~' _ _ _ aw Δm (M.U Δm) ))
    λ am → Cm ≡ M.El _ (₁ am)

  Tm~' Γp Ap .(V _) (vw xw) Δm Cm zm = Var~' _ _ _ xw Δm Cm zm
  Tm~' Γp .(l-subT 0 u Bp) .(app t u) (appw .Γp Γw ap aw Bp Bw t tw u uw) Δm Cm zm =
    Σ (Σ _ (Tm~' _ _ ap aw Δm (M.U Δm)))
    λ am → Σ (Σ _ (Ty~' _ Bp Bw (Δm M.▶ M.El Δm  (₁ am))))
    λ Bm → Σ (Σ _ (Tm~' _ _ t tw Δm (M.ΠΠ Δm _ (₁ Bm))))
    λ tm → Σ (Σ _ (Tm~' _ _ u uw Δm (M.El Δm (₁ am))))
    λ um → (Cm , zm) ≡ M.subT Δm (M.El Δm (₁ am)) (₁ um) (₁ Bm) ,
    M.app Δm (M.El Δm (₁ am)) (₁ Bm) (₁ tm) (₁ um)

  Var~' .(Γp ▶p Ap) .(liftT 0 Ap) .0 (V0w Γp Γw Ap Aw) Δm Cm zm =
    Σ (Σ _ (Con~' Γp Γw ))
    λ Γm → Σ (Σ _ (Ty~' _ Ap Aw (₁ Γm) ))
    λ Am →
    -- this left associative stuff makes it easier to inhbabite thanks to pair=
    _,_  {A = Σ _ M.Ty}{B = λ x → M.Tm (₁ x)(₂ x)}
    (Δm , Cm) zm ≡
    (((₁ Γm M.▶ ₁ Am)  , _ ) , ( M.V0 (₁ Γm) (₁ Am)))
  -- _,_ {B = λ Γm → Σ (M.Ty Γm) λ Am → M.Tm Γm Am}
  --  Δm (Cm , zm) ≡
  -- (₁ Γm M.▶ ₁ Am)  , _ , M.V0 (₁ Γm) (₁ Am) 

  -- Var~' .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Δm Cm zm = {!!}
  Var~' .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Δm Cm zm =
    Σ (Σ _ (Con~' Γp Γw ))
    λ Γm → Σ (Σ _ (Ty~' _ Ap Aw (₁ Γm) ))
    λ Am → Σ (Σ _ (Ty~' _ Bp Bw (₁ Γm) ))
    λ Bm → Σ (Σ _ (Var~' _ _ _ xw (₁ Γm) (₁ Bm) )) 
    λ xm →
    -- this left associative stuff makes it easier to inhbabite thanks to pair=
    _,_  {A = Σ _ M.Ty}{B = λ x → M.Tm (₁ x)(₂ x)}
    (Δm , Cm) zm ≡
    (((₁ Γm M.▶ ₁ Am)  , _ ) , ( M.wkt _ _ _ (₁ xm)))

    -- _,_ {B = λ Γm → Σ (M.Ty Γm) λ Am → M.Tm Γm Am}
    -- Δm (Cm , zm) ≡
    -- (₁ Γm M.▶ ₁ Am)  , _ , M.wkt _ _ _ (₁ xm)

  mkΣTm : (Γm : M.Con)(A : M.Ty Γm)(t : M.Tm Γm A) → Σ (Σ _ M.Ty) λ x → M.Tm (₁ x)(₂ x)
  mkΣTm Γ A t = ((Γ , A) , t)
-- helper to inhabit v1 ~ zm
  v1~ : ∀ {Γp : Conp}(Γw : Conw Γp){Ap}(Aw : Tyw Γp Ap){Exp}(Exw : Tyw (Γp ▶p Ap) Exp) →
    ∀ (Γm : Σ _ (Con~' Γp Γw))
       (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
       -- this will be deduced later (weakening preserves the relation)
       (Ar : Ty~' _ _ (wkTw Aw Aw) (₁ Γm M.▶ ₁ Am) (M.wkT (₁ Γm) (₁ Am) (₁ Am)))
       (Exm : Σ _ (Ty~' _ _ Exw (₁ Γm M.▶ ₁ Am))) → 
    ∀ Δm Cm zm → 
     mkΣTm Δm Cm zm ≡
         ((((₁ Γm M.▶ (₁ Am)) M.▶ (₁ Exm)) , M.wkT _ (₁ Exm) (M.wkT _ (₁ Am) (₁ Am)) ) ,
          M.wkt _ (₁ Exm) _ (M.V0 _ (₁ Am))) 
     →
    Var~' _ _ _
       (VSw _ (▶w Γw Aw) _ Exw _ (wkTw Aw Aw) 0 (V0w _ Γw _ Aw)) Δm Cm zm
  v1~ Γw Aw Exw Γm Am Ar Exm Δm Cm zm eq =
    transport!
    {A = Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x) }
    (λ x →
      Var~' _ _ _
      (VSw _ (▶w Γw Aw) _ Exw _ (wkTw Aw Aw) 0 (V0w _ Γw _ Aw)) (₁ (₁ x)) (₂ (₁ x)) (₂ x)
    ) eq
    (
    ((_ , Γm , Am , refl)) , 
    Exm , (((M.wkT _ (₁ Am)(₁ Am)) , Ar) ,
    (M.V0 (₁ Γm) (₁ Am) , Γm , Am , refl) , refl))

  v1~' : ∀ {Γp : Conp}(Γw : Conw Γp){Ap}(Aw : Tyw Γp Ap){Exp}(Exw : Tyw (Γp ▶p Ap) Exp) 
    (wxw : Varw (Γp ▶p Ap ▶p Exp) (wkT (wkT Ap)) (1)) →
    ∀ (Γm : Σ _ (Con~' Γp Γw))
    (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    -- this will be deduced later (weakening preserves the relation)
    (Ar : Ty~' _ _ (wkTw Aw Aw) (₁ Γm M.▶ ₁ Am) (M.wkT (₁ Γm) (₁ Am) (₁ Am)))
    (Exm : Σ _ (Ty~' _ _ Exw (₁ Γm M.▶ ₁ Am))) → 
    ∀ Δm Cm zm → 
    mkΣTm Δm Cm zm ≡
    ((((₁ Γm M.▶ (₁ Am)) M.▶ (₁ Exm)) , M.wkT _ (₁ Exm) (M.wkT _ (₁ Am) (₁ Am)) ) ,
    M.wkt _ (₁ Exm) _ (M.V0 _ (₁ Am))) 
    →
    Var~' _ _ _
    wxw Δm Cm zm
  v1~' Γw Aw Exw wxw
    with prop-path (VarwP _ _ _) wxw (VSw _ (▶w Γw Aw) _ Exw _ (wkTw Aw Aw) 0 (V0w _ Γw _ Aw))
  v1~' Γw Aw Exw .(VSw (_ ▶p _) (▶w Γw Aw) _ Exw (liftT 0 _) (liftTw Aw ∙p Aw) 0 (V0w _ Γw _ Aw)) | refl
    = v1~ Γw Aw Exw


  Telescope~ : ∀ {Γp}Δp (Δw : Conw (Γp ^^ Δp)) (Γm : M.Con)(Δm : M.Telescope Γm) → Set α
  Telescope~ ∙p Δw Γm Δm = Δm ≡ M.∙t Γm
  Telescope~ (Δp ▶p A) (▶w Δw Aw) Γm Em =
    Σ (Σ _ (Telescope~ Δp Δw Γm)) λ Δm →
    Σ (Σ _ (Ty~' _ A Aw (Γm M.^^ (₁ Δm)))) λ Am →
    Em ≡ (₁ Δm M.▶t ₁ Am)

{-


Some useful lemmas

-}


  -- to infer typeclasses
  it : ∀{a}{A : Set a} {{_ : A}} → A
  it {{x}} = x
  
  instance
    pathto-is-prop : ∀ {l}{A : Set l} (x : A) → is-prop (Σ A (λ t → t ≡ x))
    -- we know it is contractile, thus uses typeclass resolution
    pathto-is-prop x = raise-level ⟨-2⟩ it

    -- this needs uip (not contractile although)
    Σpathto-is-prop : ∀ {l l'}{A : Set l}{P : A → Set l'}(x : A)(y : Σ A P) → is-prop (Σ (P x) ( λ z → x , z ≡ y) )
    Σpathto-is-prop x y = all-paths-is-prop  λ { (a , refl) (.a , refl) → refl  }

    {-


The relation is almost functional (at most 1 inhabitant)

-}
  -- needs UIP or that M.Con & M.Ty are hset
  -- this is needed for one of the case to that liftV~
  instance 
    ConP : ∀ Γp Γw → is-prop (Σ _ (Con~' Γp Γw))
    TelescopeP : ∀ Γp Δp Δw Γm → is-prop (Σ _ (Telescope~ {Γp} Δp Δw Γm))
    TyP : ∀ Γp Ap Aw Γm → is-prop (Σ _ (Ty~' Γp Ap Aw Γm))
    TmP : ∀ Γp Ap tp tw Γm Am → is-prop (Σ _ (Tm~' Γp Ap tp tw Γm Am))
    VarP : ∀ Γp Ap xp xw Γm Am → is-prop (Σ _ (Var~' Γp Ap xp xw Γm Am))

    ConP .∙p ∙w = pathto-is-prop M.∙

    ConP .(_ ▶p _) (▶w Γw Aw) =

      equiv-preserves-level
      -- ((Σ-emap-r λ Γm → {!? ∘e Σ₁-×-comm!} ∘e Σ₁-×-comm) ⁻¹)
      (Σ₁-×-comm   ∘e
      -- -- this superfluous ∘e makes Σ₁-×-comm automatically infer its arguments..
      Σ-emap-r λ Γm → Σ₁-×-comm ∘e ide _)
        {{helper }}
      where
      helper : is-prop  (Σ (Σ M.Con (Con~' _ Γw))
        (λ z →
        Σ (Σ (M.Ty (₁ z)) (Ty~' _ _ Aw (₁ z)))
        (λ a → Σ M.Con (λ z₁ → z₁ ≡ (₁ z M.▶ ₁ a)))))
      helper = 
        Σ-level (ConP _ Γw)
          λ Γm → Σ-level (TyP _ _ Aw (₁ Γm))
          λ Am → it


    TelescopeP Γp ∙p Δw Γm = it
    TelescopeP Γp (Δp ▶p x) (▶w Δw Aw) Γm =
      equiv-preserves-level
      ( Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e ide _)
      {{ Σ-level it
        λ Δm →
        Σ-level (TyP _ _ Aw (Γm M.^^ ₁ Δm))
        λ Am → it }}

    TyP Γp .Up (Uw .Γp Γw) Γm = it
    TyP Γp .(ΠΠp (Elp _) _) (Πw Γw Aw Aw₁) Γm =
     equiv-preserves-level
     (
     Σ₁-×-comm ∘e Σ-emap-r λ Am' →
     Σ₁-×-comm ∘e Σ-emap-r λ Bm' →
      ide _
     )
     {{ Σ-level (TmP _ _ _ Aw Γm (M.U Γm)) λ Am' →
     Σ-level (TyP _ _ Aw₁ (Γm M.▶ M.El Γm (₁ Am'))) λ Bm' →
         it
     
     }}

    TyP Γp .(Elp _) (Elw Γw aw) Γm =
      equiv-preserves-level Σ₁-×-comm 
      {{ Σ-level (TmP _ _ _ aw Γm (M.U Γm)) λ Am' →
        it }}

    TmP Γp Ap .(V _) (vw xw) Γm Am = VarP _ _ _ xw Γm Am

    TmP Γp .(l-subT 0 u Bp) .(app t u) (appw .Γp Γw ap₁ tw Bp Bw t tw₁ u tw₂) Γm Am =
      
      equiv-preserves-level
      (
        Σ₁-×-comm ∘e Σ-emap-r λ Am' →
        Σ₁-×-comm ∘e Σ-emap-r λ Bm' →
        Σ₁-×-comm ∘e Σ-emap-r λ tm' →
        Σ₁-×-comm ∘e Σ-emap-r λ um' →
        ide _
      )
      {{ Σ-level (TmP _ _ _ tw Γm (M.U Γm)) λ Am' →
        Σ-level ((TyP _ _ Bw _)) λ Bm' →
        Σ-level (TmP _ _ _ tw₁ _ _) λ tm' →
        Σ-level (TmP _ _ _ tw₂ _ _) λ um' →
          it
      
      }}
      

    VarP .(Γp ▶p Ap) .(liftT 0 Ap) .0 (V0w Γp Γw Ap Aw) Γm Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
       ide _)
      {{ Σ-level it λ Γm' →
      Σ-level (TyP _ _ Aw (₁ Γm')) λ Am' →
      Σpathto-is-prop (Γm , Am) _
      }}

    VarP .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Γm Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
      Σ₁-×-comm ∘e Σ-emap-r λ Bm →
      Σ₁-×-comm ∘e Σ-emap-r λ xm →
      ide _
      )
      {{ Σ-level it λ Γm' →
      Σ-level (TyP _ _ Aw (₁ Γm')) λ Am' →
      Σ-level (TyP _ _ Bw (₁ Γm')) λ Bm' →
      Σ-level (VarP _ _ _ xw (₁ Γm')(₁ Bm')) λ xm' →
      Σpathto-is-prop (Γm , Am) _
      
      }}


{-


Preservation of the relation by weakening


-}

  -- actually this can be defined before and indepedantly of the other weakening lemmas
  ^^~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
          {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) )) →
          Con~' _ Δw ((₁ Γm) M.^^ (₁ Δm))



  liftT~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Exp} Exw (Exm : Σ _ (Ty~' Γp Exp Exw (₁ Γm)) )
    {Bp} Bw wBw Bm
    → Ty~' (Γp ^^ Δp) Bp Bw ((₁ Γm) M.^^ (₁ Δm))  Bm
    → Ty~' ((Γp ▶p Exp)^^ (wkC Δp)) (liftT ∣ Δp ∣ Bp) wBw
      (((₁ Γm) M.▶ (₁ Exm)) M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm))
      (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) Bm) 

  liftT~ Γw Γm Δw Δm Exw Exm Bw wBw Bm = {!!}

  -- shortcut
  wkT~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw)))
    {Exp} (Exw : Tyw Γp Exp)(Exm : Σ _ (Ty~' Γp Exp Exw (₁ Γm)))
    {Ap} (Aw : Tyw Γp Ap)(Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    wAw
    → Ty~' (Γp ▶p Exp) (wkT Ap) wAw
    (₁ Γm M.▶ ₁ Exm)
    (M.wkT (₁ Γm) (₁ Exm)(₁ Am))
  wkT~ Γw Γm Exw Exm Aw Am wAw = liftT~ Γw Γm {∙p} Γw
    (M.∙t (₁ Γm) , refl) Exw Exm Aw wAw (₁ Am) (₂ Am)

      -- let us start form minmal requirement
  liftV~ : ∀ {Γp} {Γw} (Γm : Σ _ (Con~' Γp Γw))
        {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
      {Exp} Exw (Exm : Σ _ (Ty~' Γp Exp Exw (₁ Γm)) )
      {Bp} Bm

      {xp} xw
      -- should this wxw be given ?
      --- yes so that it does not unfold unwantingly the goal
      wxw
      xm
      → Var~' (Γp ^^ Δp) Bp xp xw
        ((₁ Γm) M.^^ (₁ Δm)) Bm xm
      → Var~' ((Γp ▶p Exp)^^ (wkC Δp)) (liftT ∣ Δp ∣ Bp) (liftV ∣ Δp ∣ xp)
        wxw
        -- (liftVw {Ap = Exp} Exw Δp {Bp = Bp} {xp} xw )
        (((₁ Γm) M.▶ (₁ Exm)) M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm)) (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) Bm) (M.liftt (₁ Γm) (₁ Δm) (₁ Exm) Bm xm)



  wkTelescope~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
                   {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
                   {Ep} Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm))) →
        Telescope~ (wkC Δp) (wkCw' Ew Δp Δw) (₁ Γm M.▶ ₁ Em) (M.wkC (₁ Γm) (₁ Em) (₁ Δm))

  wkTelescope~ Γw Γm {∙p} Δw Δm Ew Em rewrite (₂ Δm) = refl

  wkTelescope~ Γw Γm {Δp ▶p Ap} (▶w Δw Aw) (_ , Δm , Am , refl) Ew Em =
    ( M.wkC (₁ Γm) (₁ Em) (₁ Δm) , wkTelescope~ Γw Γm Δw Δm Ew Em) ,
    (M.liftT (₁ Γm) (₁ Δm)(₁ Em) (₁ Am) , liftT~ Γw Γm Δw Δm Ew Em Aw (liftTw Ew Δp Aw) (₁ Am) (₂ Am)) ,
    refl
        -- let us start form minmal requirement
  -- ^^~ : ∀ {Γp} Γw Γm
  -- wkTelescope~ : ∀ {Γp} Γm
  --       -- (Γm : Σ _ Con~' Γp Γw)
  --       {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw Γm ))
  --       {Exp} Exw (Exm : Σ _ (Ty~' Γp Exp Exw Γm) )
  --       → Telescope~ {((Γp ▶p Exp)^^ (wkC Δp)) ?
  --         ((Γm M.▶ (₁ Exm)) M.^^ M.wkC Γm (₁ Exm) (₁ Δm))

  -- wkTelescope~ {Γp} Γm Δw Δm {Exp} Exw Exm = ?

  -- todo: utiliser ces lemmes avant, par exemple dans v1
  trVar~' : {Γp : Conp}{Ap : Typ}{xp : ℕ}(xw : Varw Γp Ap xp)
    (xw' : Varw Γp Ap xp)
    {Δm : M.Con}{Cm : M.Ty Δm}(zm : M.Tm _ Cm)  → Var~' _ _ _ xw _ _ zm → Var~' _ _ _ xw' _ _ zm
  trVar~' xw xw' zm = tr (λ xw → Var~' _ _ _ xw _ _ zm) (prop-path (VarwP _ _ _) xw xw')

  trCon~' : {Γp : Conp}(Γw : Conw Γp)(Γw' : Conw Γp)
    (Γm : M.Con) → Con~' _ Γw Γm → Con~' _ Γw' Γm
  trCon~' Γw Γw' Γm = tr (λ Γw → Con~' _ Γw Γm) (prop-path (ConwP _) Γw Γw')

-- Σ means we bundle the model stuff and its relational proof together in a Σ type in the conclusion
  ΣCon~'▶ : ∀ {Γp}{Γw : Conw Γp}{Ap} {Aw : Tyw Γp Ap}
    (Γm : Σ M.Con (Con~' Γp Γw))
    (Am   : Σ (M.Ty (₁ Γm)) (Ty~' Γp Ap Aw (₁ Γm)))
    (ΓAw :
    Conw (Γp ▶p Ap)) → Σ M.Con (Con~' (Γp ▶p Ap) ΓAw)
  ΣCon~'▶ {Γw = Γw} {Aw = Aw} Γm Am ΓAw = 
    (₁ Γm M.▶ ₁ Am) ,
    (trCon~' (▶w Γw Aw) ΓAw (₁ Γm M.▶ ₁ Am)
      (Γm , (Am , refl)))

-- this is also induced by ΣliftT~'
  ΣwkTy~' : ∀ {Γp}{Γw : Conw Γp}{Ap} {Aw : Tyw Γp Ap}{Bp}{Bw : Tyw Γp Bp}
      (Γm : Σ M.Con (Con~' Γp Γw))
      (Am   : Σ (M.Ty (₁ Γm)) (Ty~' Γp Ap Aw (₁ Γm)))
      (Bm   : Σ (M.Ty (₁ Γm)) (Ty~' Γp Bp Bw (₁ Γm))) →
      Σ (M.Ty (₁ Γm M.▶ ₁ Am)) (Ty~' (Γp ▶p Ap) (wkT Bp) (wkTw Aw Bw) (₁ Γm M.▶ ₁ Am))

  ΣwkTy~' {Γw = Γw} {Aw = Aw} {Bw = Bw} Γm Am Bm  = 
    (M.wkT _ (₁ Am)(₁ Bm)) ,
    wkT~ Γw Γm Aw Am Bw Bm (wkTw Aw Bw)
    


  ^^~ Γw Γm {∙p} Δw Δm rewrite (₂ Δm) = trCon~' Γw Δw _ (₂ Γm)

  ^^~ Γw Γm {Δp ▶p Ap} (▶w Δw Aw) (.(₁ Δm Model1.▶t ₁ Am) , Δm , Am , refl) =
    (((₁ Γm M.^^ ₁ Δm) , (^^~ Γw Γm Δw Δm )) , Am , refl)

  Σ^^~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) )) →
    Σ _ (Con~' _ Δw )
  Σ^^~ Γw Γm Δw Δm = _ , ^^~ Γw Γm Δw Δm

  Σ^^wk~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
          {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
          {Ep}Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm) ))
          → Σ _ (Con~' (Γp ▶p Ep ^^ wkC Δp) (wkCw' Ew Δp Δw))

  Σ^^wk~ {Γp} Γw Γm {Δp} Δw Δm {Ep} Ew Em =
    (₁ Γm M.▶ ₁ Em M.^^ M.wkC (₁ Γm) (₁ Em) (₁ Δm)) ,
      ^^~ {Γp = Γp ▶p Ep} (▶w _ Ew)
      (((₁ Γm) M.▶ (₁ Em)) , Γm , Em , refl)
      {Δp  = wkC Δp} (wkCw' Ew Δp Δw)
      ((M.wkC (₁ Γm) (₁ Em) (₁ Δm)) , wkTelescope~ _ Γm _ Δm Ew Em)

  ΣliftT~' :  ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Ep}Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm) ))
    {Ap} Aw (Am : Σ _ (Ty~' (Γp ^^ Δp) Ap Aw (₁ Γm M.^^ ₁ Δm)))
    → Σ _ (Ty~' (Γp ▶p Ep ^^ wkC Δp) (liftT ∣ Δp ∣ Ap)
        (liftTw Ew Δp Aw) (₁ Γm M.▶ ₁ Em M.^^ M.wkC (₁ Γm) (₁ Em) (₁ Δm) ))

  ΣliftT~' Γw Γm {Δp} Δw Δm Ew Em Aw Am =
    M.liftT (₁ Γm) (₁ Δm)(₁ Em) (₁ Am) , liftT~ _ Γm {Δp} _  Δm Ew Em  Aw (liftTw Ew Δp Aw) (₁ Am) (₂ Am)  

    

  liftV~ (Ym , Yr) {∙p} Δw (.(M.∙t Ym) , refl) Exw Exm Bm (V0w Γp Γw Ap Aw) wxw xm (Γm , Am , eq)
    = tr P (! eq ) Prefl Exm
     where
      P : (YBxm : Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x)) → Set α
      P YBxm = 
        (Exm' : Σ (M.Ty (₁ (₁ YBxm)))(Ty~' (Γp ▶p Ap) _ Exw (₁ (₁ YBxm)))) →
        Var~' (Γp ▶p Ap ▶p _) (liftT 0 (liftT 0 Ap)) 1 wxw
        ((₁ (₁ YBxm)) M.▶ ₁ Exm' M.^^ M.wkC (₁ (₁ YBxm)) (₁ Exm') (M.∙t (₁ (₁ YBxm))))
        (M.liftT (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)))
        (M.liftt (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)) (₂ YBxm))

      Prefl : P (((₁ Γm M.▶ ₁ Am) , M.wkT (₁ Γm) (₁ Am) (₁ Am)) , M.V0 (₁ Γm) (₁ Am))
      Prefl Exm' =
        v1~' Γw Aw Exw wxw Γm Am (wkT~ _ Γm Aw Am Aw Am (wkTw Aw Aw)  ) Exm' _ _ _
        refl
     
  liftV~ (Ym , Yr) {∙p} Δw (.(M.∙t Ym) , refl) Exw Exm Bm (VSw Γp Γw Ap Aw Bp Bw xp xw) wxw xm (Γm , Am , Bm' , xm' , eq)
   = tr P (! eq)  Prefl Exm
    where
      P : (YBxm : Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x)) → Set α
      P YBxm = 
        (Exm' : Σ (M.Ty (₁ (₁ YBxm)))(Ty~' (Γp ▶p Ap) _ Exw (₁ (₁ YBxm)))) →
        Var~' (Γp ▶p Ap ▶p _) (liftT 0 (liftT 0 Bp)) (S (S xp)) wxw
        ((₁ (₁ YBxm)) M.▶ ₁ Exm' M.^^ M.wkC (₁ (₁ YBxm)) (₁ Exm') (M.∙t (₁ (₁ YBxm))))
        (M.liftT (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)))
        (M.liftt (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)) (₂ YBxm))
      Prefl :  P
        (((₁ Γm M.▶ ₁ Am) , M.wkT (₁ Γm) (₁ Am) (₁ Bm')) ,
        M.wkt (₁ Γm) (₁ Am) (₁ Bm') (₁ xm'))
      Prefl Exm' =
          trVar~'
          (VSw (Γp ▶p Ap) Δw _ Exw _
            (wkTw Aw Bw)
            (S xp)
            (VSw Γp Γw Ap Aw Bp Bw xp xw))
          wxw _
          (ΣCon~'▶ {Γw = Γw} {Aw = Aw} Γm Am Δw ,
          Exm' ,
          ΣwkTy~' {Γw = Γw} {Aw = Aw} {Bw = Bw}
            Γm Am Bm' ,
          (M.wkt (₁ Γm) (₁ Am) (₁ Bm') (₁ xm') , Γm , (Am , (Bm' , (xm' , refl)))) ,
            refl)



{-
DEPRECATED
Here we need to know that at most one model type relates to a syntacitc type.

Indeed, I have the following hypotheses : (E = Ex)

    Γ ⊢ E ~ Γₘ ⊢ Eₘ
    Γ ^ Δ ~ ΓΔₘ
Γ ^ Δ ⊢ A ~ ΓΔₘ ⊢ Aₘ
Γ ⊢ Δ ▶ A ~ Γm ⊢ ΔAm from which we deduce the existece of Δₘ ~ Δ and Aₘ' such that Γ ^ Δ ⊢ A ~ Γₘ ^ Δₘ ⊢ Aₘ'
  (and you will see that we will need that Aₘ = Aₘ')

and also
Γₘ ^ ΔAₘ ⊢ xₘ : Bₘ

With the following equations:

Γₘ ^ ΔAₘ = ΓΔm ▶ Aₘ
Bₘ = ΓΔₘ ▶ Aₘ ⊢ wk Am
xₘ = v0

and we would like to show that

    Γ  ▶ E ^ wkΔ ▶ wk A ⊢ v0 : wkA ~ Γₘ ▶ Eₘ ^ wk ΔAₘ ⊢ xₘ


-}
  liftV~ {Γp} (Γm , Γr) {Δp ▶p Ap} (▶w Δw Aw) (.(₁ Δm M.▶t ₁ Am') , Δm , Am' , refl) {Exp} Exw Exm Bm (V0w .(Γp ^^ Δp) ΓΔw .Ap Aw') wxw xm (ΓΔm , Am , eq) rewrite prop-has-all-paths Δw ΓΔw
  -- with eqΓΔm
  -- ...  |  e
    =
    -- here we need that:
    -- (liftT (S ∣ Δp ∣) (liftT 0 Ap)) = liftT 0 Ap (lift |Δp| Ap)
    tr (λ Ap' →
      (wxw : Varw ((Γp ▶p _ ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Ap) Ap' 0) →
      Var~' ((Γp ▶p _ ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Ap) Ap' 0 wxw (Γm M.▶ ₁ Exm M.^^ M.wkC Γm (₁ Exm) (₁ Δm M.▶t ₁ Am'))
      (M.liftT Γm (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm) (M.liftt Γm (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm xm))
      (! (comm_liftT ∣ Δp ∣ Ap))
     ( 
      λ wxw →
      
      trVar~' {xp = from-nat 0} 
      (V0w (Γp ▶p _ ^^ wkC Δp) (wkCw' Exw Δp ΓΔw)
      (liftT ∣ Δp ∣ Ap) (liftTw Exw Δp Aw))
      wxw
      {!xm!}
      -- première composante:
      -- j'ai Γ ^ Δ ~ ΓΔₘ
      -- et Γ ⊢ E ~ Γₘ ⊢ Eₘ
      -- et je veux Γ ▶ E ^ Δ  ~  ??
      -- la solution est  ?? := Γₘ ▶ Eₘ ^ wk Δₘ
      -- TODO: faire un lemme séparé de ça
      (Σ^^wk~ _ (Γm , Γr) ΓΔw Δm Exw Exm
      ,
      -- TODO faire une def séparée
      ΣliftT~' _ (Γm , Γr) ΓΔw Δm Exw Exm Aw Am' , 
      -- ((M.liftT Γm (₁ Δm)(₁ Exm) (₁ Am'))
      --     , {!ΣliftT~ !}) ,
          -- liftT~ _ (Γm , Γr) _ Δm Exw Exm {Ap} Aw (liftTw Exw Δp Aw) (₁ Am') (₂ Am')  ) ,

      {-
      I have Γₘ ^ (Δₘ ▶ Aₘ') ⊢ Bₘ
      I know that
        Γₘ ^^ (Δₘ ▶ Aₘ') = ΓΔm ▶ Am
        Bm = wk_Am Am
        xm = V0
      and I want to show that:
        (Γₘ ▶ Eₘ) ^ (Δₘ ▶ Aₘ') ⊢ lift_Em Bm
        = ((Γₘ ▶ Eₘ) ^ Δₘ) ▶ Aₘ' ⊢ wk (lift_Em Bm)
      (and another equation for xm = V0)
      But to use the given equations, I need to know that ΓΔₘ = Γₘ ^^ Δₘ and Aₘ = Aₘ'
      which may be could be proven by using the fact they both relate to the same syntactic counterpart ?
      -}
      {!!}
      
    -- ( (M.liftT Γm (₁ Δm)(₁ Exm) (₁ Am')) , {!!}) ,
      -- {!pair=!}
      )
      )
      
      
      wxw
    where
      eqΓΔm : ΓΔm ≡ Σ^^~ _ (Γm , Γr) _ Δm
      eqΓΔm = prop-has-all-paths _ _
      P : (YBxm : Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x)) → Set α
      P YBxm = {!!}
             -- Var~' ((Γp ▶p .Exp ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Ap)
      --   (liftT (S ∣ Δp ∣) (liftT 0 Ap)) 0 wxw
      --   (Γm M.▶ ₁ Exm M.^^ M.wkC Γm (₁ Exm) (₁ ΔAm))
      --   (M.liftT Γm (₁ ΔAm) (₁ Exm) Bm) (M.liftt Γm (₁ ΔAm) (₁ Exm) Bm xm)

  liftV~ Γm {Δp ▶p Ap} Δw Δm Exw Exm Bm (VSw .(_ ^^ Δp) Γw .Ap Aw Bp Bw xp xw) wxw xm xr = {!!}





-- do I need such a general statment, can I do it only when A = El a ?
-- I don't think assuming A = El a makes the proof simpler anyway
-- Do I need to enforce that Γm is related ?
  subT~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) →
      ∀{Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
      {Bp} Bw (Bm : (Σ _ (Ty~' (Γp ▶p Ap) Bp Bw (₁ Γm M.▶ ₁ Am) )))
      {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
      (Bsw : Tyw Γp (subT up Bp) )
      → Ty~' Γp (subT up Bp) Bsw (₁ Γm)
        (M.subT (₁ Γm)(₁ Am) (₁ um)  (₁ Bm))
  subT~ = {!!}


  -- Con~path : ∀ Γp Γw (Γm : Σ _ (Con~' Γp Γw)) Γw' Γm' → Con~' Γp Γw' Γm' → ₁ Γm ≡ Γm'
  -- Con~path Γp Γw Γm Γw' Γm' Γr = {!!}

  Ty~path : ∀ {Γp}{Γw}(Γm : Σ _ (Con~' Γp Γw)) {Ap} Aw (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    Am' → Ty~' Γp Ap Aw (₁ Γm) Am' → ₁ Am ≡ Am'

  Ty~path Γm Aw Am Am' Ar' = fst= (prop-path (TyP _ _ Aw (₁ Γm)) Am (Am' , Ar'))

  ConTy~path : ∀ {Γp Γw} (Γm : Σ _ (Con~' Γp Γw)) Γw' Γm' (Γr' : Con~' Γp Γw' Γm')
    {Ap Aw} (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm))) -- Aw'
    Am'
    → Ty~' Γp Ap Aw Γm' Am' →   (₁ Γm , ₁ Am) ≡ (Γm' , Am')
  ConTy~path = {!!}

  -- ConTy~path' : ∀ {Γp Γw} (Γm : Σ _ (Con~' Γp Γw)) Γm' Γw' (Γr' : Con~' Γp Γw' Γm')
  --   {Ap Aw} (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm))) Aw Am'
  -- → Ty~' Γp Ap Aw' Γm' Am' →   (₁ Γm , ₁ Am) ≡ (Γm' , Am')
  -- ConTy~path' = {!!}

  Con~el : ∀ Γp Γw → (Σ _ (Con~' Γp Γw))
  Ty~el : ∀ Γp Γw Ap Aw (Γm : (Σ _ (Con~' Γp Γw)))→ (Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
  Tm~el : ∀ Γp Γw Ap Aw tp tw (Γm : (Σ _ (Con~' Γp Γw))) (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    → (Σ _ (Tm~' Γp Ap tp tw (₁ Γm) (₁ Am)))
  Var~el : ∀ Γp Γw Ap Aw xp xw (Γm : (Σ _ (Con~' Γp Γw))) (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    → (Σ _ (Var~' Γp Ap xp xw (₁ Γm) (₁ Am)))

  Con~el .∙p ∙w = _ , refl
  Con~el .(Γp ▶p Ap) (▶w {Γp} Γw {Ap} Aw) =
    _ , Con~el _ Γw , Ty~el _ Γw _ Aw (Con~el _ Γw) , refl

  Ty~el Γp Γw' .Up (Uw .Γp Γw) Γm  = _ , refl
  Ty~el Γp Γw' .(ΠΠp (Elp ap) Bp) (Πw  Γw {ap} Aw {Bp} Bw) Γm =
    _ ,
    (Tm~el Γp Γw' Up (Uw Γp Γw') ap Aw Γm (_ , refl)) ,
    (Ty~el  (Γp ▶p Elp ap) (▶w Γw'  (Elw Γw' Aw)) Bp Bw
      -- (_ , tr (λ x → Σ _ (Con~' Γp x)) (prop-path (ConwP Γp) Γw' Γw) Γm , {!!} ) ) ,
      (_ , Γm , (_ ,
      Tm~el Γp Γw' Up (Uw Γp Γw') ap Aw Γm (_ , refl) , refl) , refl) ) ,
    refl
  Ty~el Γp Γw' _ (Elw Γw aw) Γm =
    _ , Tm~el Γp Γw' Up (Uw Γp Γw) _ aw Γm (_ , refl)
     ,
    refl
    -- (tr (λ x → {!!}) {!!} Γm)

  Tm~el Γp Γw Ap Aw .(V _) (vw xw) Γm Am = Var~el _ Γw _ Aw _ xw Γm Am
  Tm~el Γp Γw .(l-subT 0 u Bp) Bsw .(app t u) (appw .Γp Γw' ap aw Bp Bw t tw u uw) Γm Am
      with (Tm~el Γp Γw Up (Uw Γp Γw) ap aw Γm (M.U (₁ Γm) , refl))
  ...       | am
      with (Tm~el Γp Γw (Elp ap) (Elw Γw' aw) u uw Γm
              (M.El (₁ Γm) (₁ am) , am , refl))
         |  Ty~el (Γp ▶p Elp ap) (▶w Γw (Elw Γw aw)) Bp Bw
              ((₁ Γm M.▶ M.El (₁ Γm) (₁ am)) , Γm , (M.El (₁ Γm) (₁ am) , am , refl) , refl)
  ...    | um | Bm
      with Tm~el Γp Γw (ΠΠp (Elp ap) Bp) (Πw Γw aw Bw) t tw Γm
              (M.ΠΠ (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ Bm) , am , Bm , refl)
  ...    | tm =

  -- inferred by the las tequality
   
      transport! (M.Tm (₁ Γm))
      (Ty~path Γm Bsw Am
       (M.subT (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ um) (₁ Bm))
       (subT~ Γw Γm (Elw Γw' aw)
        (M.El (₁ Γm) (₁ am) , am , refl) Bw Bm uw um Bsw))
      (M.app (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ Bm) (₁ (tm)) (₁ um))
    ,
   (am , Bm , tm , um
    ,
   (pair=
     -- (Ty~path Γm _ Am {!!} {!!})
     (Ty~path Γm Bsw Am
        (M.subT (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ um) (₁ Bm))
        (subT~ Γw Γm {Ap = Elp ap} (Elw Γw' aw) ((M.El (₁ Γm) (₁ am)) , am , refl ) Bw Bm uw um Bsw))
        (from-transp! (M.Tm (₁ Γm))
           (Ty~path Γm Bsw Am
            (M.subT (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ um) (₁ Bm))
            (subT~ Γw Γm {Ap = Elp ap} (Elw Γw' aw)
             (M.El (₁ Γm) (₁ am) , am , refl) Bw Bm uw um Bsw))
           {v =
            M.app (₁ Γm)
            (M.El (₁ Γm) (₁ am)) (₁ Bm) (₁ (tm)) (₁ um)}
           refl)))

  Var~el .(Γp ▶p Ap) wΓw .(liftT 0 Ap) wAw .0 (V0w Γp Γw Ap Aw) Γm Am
      with Con~el Γp Γw 
  ...  | Γm'  
      with Ty~el Γp Γw Ap Aw Γm'  
  ...  | Am' =
    -- inferred by the last hole
      -- transport! (λ x → M.Tm (₁ x) (₂ x))
      -- (ConTy~path Γm (▶w Γw Aw) (₁ Γm' M.▶ ₁ Am') (Γm' , Am' , refl) Am
      -- (M.wkT (₁ Γm') (₁ Am') (₁ Am')) (wkT~ Γw Γm' Aw Am' Aw Am' wAw))
      -- (M.V0 (₁ Γm') (₁ Am'))
      
      transport! (λ x → M.Tm (₁ x) (₂ x))
      (ConTy~path Γm (▶w Γw Aw) (₁ Γm' M.▶ ₁ Am') (Γm' , Am' , refl) {Aw = wAw} Am
      (M.wkT (₁ Γm') (₁ Am') (₁ Am')) (wkT~ Γw Γm' Aw Am' Aw Am' wAw))
      (M.V0 (₁ Γm') (₁ Am'))
      
       ,
      Γm' , Am' ,
      pair=
        (ConTy~path Γm (▶w Γw Aw) _ (Γm' , Am' , refl) {Aw = wAw} Am
         (M.wkT _ _ _) (wkT~ Γw Γm' Aw Am' Aw Am' wAw))
         (from-transp! {A = Σ _ M.Ty}(λ x → M.Tm (₁ x) (₂ x))
         (ConTy~path Γm (▶w  Γw  Aw) _
         (Γm' , Am' , refl)
         -- is it really necessary to have wkTw Aw Aw? Can't I use wAw ?
         {Aw = wAw}
         Am
         -- (wkTw Aw Aw)
         -- wAw
         (M.wkT _ _ _)
         ((wkT~ Γw Γm' Aw Am' Aw Am' wAw
         )))
         {v = M.V0 (₁ Γm') (₁ Am')}
         refl
         )
      
        
      -- (from-transp _ _ refl)
  Var~el .(Γp ▶p Ap) wΓw .(liftT 0 Bp) wAw .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Γm Am 
      with (Con~el Γp Γw)
  ...  | Γm' 
      with (Ty~el Γp Γw Ap Aw Γm') | (Ty~el Γp Γw Bp Bw Γm')
  ...  | Am' | Bm'
      with (Var~el Γp Γw Bp Bw xp xw Γm' Bm')
  ...  | xm = 
      
     -- inferred from the last equality
     
-- this value was inferred from the last equalities
     transport! (λ x → M.Tm (₁ x) (₂ x))
      (ConTy~path Γm (▶w Γw Aw)
      (₁ Γm' M.▶ ₁ Am')
      (Γm' , Am' , refl)
      {Aw = wAw} Am
      (M.wkT (₁ Γm') (₁ Am') (₁ Bm'))
      (wkT~ Γw Γm' Aw Am' Bw Bm' wAw))
      (M.wkt (₁ Γm') (₁ Am') (₁ Bm') (₁ xm)) 
      ,
     Γm' , (Am' , (Bm' , (xm ,
     pair=
        (ConTy~path Γm (▶w Γw Aw) _
          (Γm' , (Am' , refl)) {Aw = wAw} Am
          -- or wkTw .. .. ?
          -- wAw
          (M.wkT _ _ _)
          (wkT~ Γw Γm' Aw Am' Bw Bm' wAw))
        (
        (from-transp! {A = Σ _ M.Ty}(λ x → M.Tm (₁ x) (₂ x))
          (ConTy~path Γm (▶w Γw Aw) _
            (Γm' , (Am' , refl)) {Aw = wAw} Am
              -- or wkTw .. .. ?
              -- wAw
              (M.wkT _ _ _)
            (wkT~ Γw Γm' Aw Am' Bw Bm' wAw))
        {v = (M.wkt (₁ Γm') (₁ Am') (₁ Bm') (₁ xm))} 
        )
        refl
        )
     )))



{-

{-


{-
  Con~   ∙           γ = γ ≡ M.∙
  Con~   (Γ ▶ A)     γ = ∃₂ λ γ₀ α → Con~ Γ γ₀ × Ty~ A γ₀ α × (γ ≡ γ₀ M.▶ α)
  Ty~    (U Γ)       γ α = Con~ Γ γ × (α ≡ M.U γ)
  Ty~    (ΠΠ Γ A B)   γ α = Con~ Γ γ × ∃₂ λ α₀ α₁ → Ty~ A γ α₀ × Ty~ B (γ M.▶ α₀) α₁ × (α ≡ M.ΠΠ γ α₀ α₁)

  -- Semantic values with the same presyntactic structure are equal
  Γ~≡ : (Γ : Con) → ∀ γ γ' → Con~ Γ γ  → Con~ Γ γ' → γ ≡ γ'
  A~≡ : (A : Ty)  → ∀ γ α α' → Ty~ A γ α → Ty~ A γ α' → α ≡ α'
  Γ~≡   ∙           γ γ' ~γ ~γ' = ~γ ◾ ~γ' ⁻¹
  Γ~≡   (Γ ▶ A)     _ _ (γ , α , ~γ , ~α , refl) (γ' , α' , ~γ' , ~α' , refl) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                 | refl = ap (γ' M.▶_) (A~≡ A γ α α' ~α ~α')
  A~≡   (U Γ)       γ α α' (_ , ~α) (_ , ~α') = ~α ◾ ~α' ⁻¹
  A~≡   (ΠΠ Γ A B)   γ _ _ (~γ  , α₀  , α₁  , ~α₀  , ~α₁  , refl)
                          (~γ' , α₀' , α₁' , ~α₀' , ~α₁' , refl) with A~≡ A γ α₀ α₀' ~α₀ ~α₀'
  ...                 | refl = ap (M.ΠΠ γ α₀') (A~≡ B (γ M.▶ α₀') α₁ α₁' ~α₁ ~α₁')

  -- ... which equality is refl in the degenerate case
  Γ~refl : (Γ : Con) → ∀ γ ~γ → Γ~≡ Γ γ γ ~γ ~γ ≡ refl
  A~refl : (A : Ty)  → ∀ γ α ~α → A~≡ A γ α α ~α ~α ≡ refl
  Γ~refl   ∙           γ refl = refl
  Γ~refl   (Γ ▶ A)     _ (γ , α , ~γ , ~α , refl)
                         rewrite Γ~refl Γ γ ~γ | A~refl A γ α ~α = refl
  A~refl   (U Γ)       γ _ (~γ , refl) = refl
  A~refl   (ΠΠ Γ A B)   γ _ (~γ , α₀ , α₁ , ~α₀ , ~α₁ , refl)
                         rewrite A~refl A γ α₀ ~α₀ | A~refl B (γ M.▶ α₀) α₁ ~α₁ = refl

  -- Interpretation of the well-formed presyntax in M.
  -- We have redundant ~ witnesses, but we must always return the topmost ones,
  -- which is the canonical choice, in order to avoid UIP for recursion.
  ⟦Con⟧ : (Γ : Con) → Conw Γ → ∃ λ γ → Con~ Γ γ
  ⟦Ty⟧  : (A : Ty) → ∀ Γ → Tyw A Γ → ∃₂ λ γ α → Con~ Γ γ × Ty~ A γ α
  ⟦Con⟧   ∙           _ = M.∙ , refl
  ⟦Con⟧   (Γ ▶ A)     (Γw , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                   | refl = (γ M.▶ α) , (γ , α , ~γ , ~α , refl)
  ⟦Ty⟧ (U Γ)     _ (Γw , refl) with ⟦Con⟧ Γ Γw
  ...                   | (γ , ~γ) = γ , M.U γ , ~γ , ~γ , refl
  ⟦Ty⟧ (ΠΠ Γ A B) Δ (Γw , Aw , Bw , refl) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ...                   | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ...                   | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
  ...                   | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
  ...                   | refl with A~≡ A γ'' α α' ~α ~α'
  ...                   | refl = γ , M.ΠΠ γ α β , ~γ , (~γ , α , β , ~α , ~β , refl)

  -- Recursion
  Conᴿ : Syn.Con → M.Con
  Conᴿ (Γ , Γw) = proj₁ (⟦Con⟧ Γ Γw)

  Tyᴿ : ∀ {Γ} → Syn.Ty Γ → M.Ty (Conᴿ Γ)
  Tyᴿ {Γ , Γw} (A , Aw) with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | γ , ~γ | γ' , α , ~γ' , ~α with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl = α

  ▶ᴿ : ∀ {Γ A} → Conᴿ (Γ Syn.▶ A) ≡ Conᴿ Γ M.▶ Tyᴿ A
  ▶ᴿ {Γ , Γw}{A , Aw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl = refl

  Uᴿ : ∀ {Γ} → Tyᴿ (Syn.U Γ) ≡ M.U (Conᴿ Γ)
  Uᴿ {Γ , Γw} with ⟦Con⟧ Γ Γw
  ... | γ , ~γ rewrite Γ~refl Γ γ ~γ = refl

  ΠΠᴿ : ∀ {Γ A B} → Tyᴿ (Syn.ΠΠ Γ A B) ≡ M.ΠΠ (Conᴿ Γ) (Tyᴿ A) (tr M.Ty (▶ᴿ {Γ}{A}) (Tyᴿ B))
  ΠΠᴿ {Γ , Γw}{A , Aw}{B , Bw} with ⟦Con⟧ Γ Γw | ⟦Ty⟧ A Γ Aw
  ... | (γ , ~γ) | (γ' , α , ~γ' , ~α) with Γ~≡ Γ γ γ' ~γ ~γ'
  ... | refl with ⟦Ty⟧ B (Γ ▶ A) Bw
  ... | (_ , β , (γ'' , α' , ~γ'' , ~α' , refl) , ~β) with Γ~≡ Γ γ γ'' ~γ ~γ''
  ... | refl with A~≡ A γ'' α α' ~α ~α'
  ... | refl rewrite Γ~refl Γ γ'' ~γ = refl

  ConTyRec : ConTyᴿ ConTySyn M
  ConTyRec = record
    { Con = Conᴿ
    ; Ty  = Tyᴿ
    ; •   = refl
    ; ▶   = λ {Γ}{A} → ▶ᴿ {Γ}{A}
    ; U   = λ {Γ} → Uᴿ {Γ}
    ; ΠΠ   = λ {Γ}{A}{B} → ΠΠᴿ {Γ}{A}{B}
    }
-}


--
-}
-}
