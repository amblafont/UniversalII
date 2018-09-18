{-# OPTIONS --allow-unsolved-metas #-}

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
 
module Syntax where

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
   
   HoTT.transport (λ x → Tmw _ x _) ?
   (appw _ (wkCw' Aw Δp Γw) _ (lifttw Aw Δp aw) _ (liftTw Aw (Δp ▶p Elp ap) Bw)
   (liftt ∣ Δp ∣ t) (lifttw Aw Δp tw) (liftt ∣ Δp ∣ u) (lifttw Aw Δp uw)
   )
   

-- liftVw Aw ∙p xw = VSw _ {!!} _ Aw _ {!!} _ xw
liftVw {Ap = Bp} Bw ∙p (V0w Γp Γw Ap Aw) = VSw (Γp ▶p Ap) (▶w Γw Aw) Bp Bw (wkT Ap)
   (liftTw Aw ∙p Aw) 0 (V0w Γp Γw Ap Aw)
liftVw Aw ∙p (VSw Γp Γw Ap Aw' Bp Bw xp xw) =
  VSw _ (▶w Γw Aw') _ Aw _ (liftTw Aw' ∙p Bw) _ (VSw Γp Γw Ap Aw' Bp Bw xp xw)

liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (V0w .(_ ^^ Δp) Γw .Bp Aw) =
  HoTT.transport (λ x → Varw (((Γp ▶p T) ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Bp) x 0) ?
     (V0w ((Γp ▶p T) ^^ wkC Δp) (wkCw' Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Aw))
liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (VSw .(_ ^^ Δp) Γw .Bp Bw Ap Aw xp xw) =
  HoTT.transport (λ x → Varw _ x _)  ?
   (VSw ((Γp ▶p T) ^^ wkC Δp) (wkCw' Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Bw)
   _ (liftTw Tw Δp Aw) _ (liftVw Tw Δp xw))
   

wkTw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap){Bp}(Bw : Tyw Γp Bp) → Tyw (Γp ▶p Ap) (wkT Bp)
wkTw Aw Bw = liftTw Aw ∙p Bw 

{-

Lemmas about commutations of lift
TODO: demander à Theo

-}
comm_liftV : ∀ p q → liftV (S p) (liftV 0 q) ≡ liftV 0 (liftV p q)
comm_liftV p q = ?

comm_liftT : ∀ p q → liftT (S p) (liftT 0 q) ≡ liftT 0 (liftT p q)
comm_liftT p q = ?


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

instance
  ConwP : (Γp : Conp) → is-prop (Conw Γp)
  TywP : (Γp : Conp)(Ap : Typ)  → is-prop (Tyw Γp Ap)
  TmwP : (Γp : Conp)(Ap : Typ)(tp : Tmp)  → is-prop (Tmw Γp Ap tp)
  VarwP : (Γp : Conp)(Ap : Typ)(xp : ℕ)  → is-prop (Varw Γp Ap xp)

  ConwP = ?
  TywP = ?
  TmwP = ?
  VarwP = ?


