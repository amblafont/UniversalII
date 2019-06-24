{-
Non-inductive parameters, and infinitary parameters, makes functional extensionality necessary.
This file should work without K,


Plan of the file
- Definition of the (untyped) syntax
- Lemmas about equalities enjoyed by the syntax
- Well typed judgements
- Preservation of typing with respect to some operations on the syntax
- Proof that these jdugements are hProp.
- Some other lemmas and complements about full substitutions

Note:
 au lieu d'avoir la syntaxe well scoped (c'est à dire indexée par un entier qui indique la taille maximale
 de variables), j'ai ajouté une constante de terme erreur que je renvoie quand la substitution est mal
 typée. Tout semble bien marcher, mais par contre pour montrer que la substitution identité préserve
 la syntaxe, je ne sais pas comment faire..


Definition of well -typed syntax. The well typed judgements are quite paranoid, but this
is necessary to be able to define the functional relation with the postulated model,
in the case of variables (there I need an induction hypothesis on both the context and the types involved).

Some suffix helpers:
- T for types
- t for terms
- V for variables
- Tel for telescopes
- w for well typed judgements

Some prefix helpers:
- lift : weakening from Γ , Δ to Γ , E , wk Δ
- sub : telescope substitution of a single variable from Γ , E , Δ to Γ ,  Δ [ _ ]

(Full) Substitutions are list of terms.

Maybe I could remove the ad-hoc telescope substitution sub*,  and use full substitutions
instead . However, I don't think I can avoid lifts before definig substitution, because
how would I define the substituion on Π A B, since B is in an extended context ?

[keep σ] takes a substitution Γ ⊢ σ : Δ to Γ , A[σ] ⊢ keep σ : Δ , A
It corresponds to _^_ in the model


List of somme lemmas :

Interaction between weakening/telescope substitutions:

  lift-liftT : liftT (S p) (liftT 0 q) ≡ liftT 0 (liftT p q)
  liftn[n]T 0 : subT u (wkT A) ≡ A
  lift-subT : liftT p (subT u B) ≡ subT (liftt p u)(liftT (S p) B)
  l-subT-subT : l-subT p z (subT u B) ≡ subT (l-subt p z u)(l-subT (S p) z B)

Interaction with full substitution between these and full substitutions:

  wk=wkS :  (A [ (wkS σ) ] ) ≡ wk (A [ σ ])
  wk[,] : ((wk A ) [ t ∷ σ ]) ≡ (A [ σ ])
  [0↦][] : (sub z A [ σ ])   ≡ sub (z [ σ ]t) (A [ keep σ ])


Then, preservation of typing by weakening/telescope and full substituions.

Finally, proof that these well typed judgements are hProp

Complements lemmas and definitions:
 -  identity substitution, composition of substitutions, etc..
 for example:
[<>]T : ((Γ ▶p E) ⊢ A) z → (A [ < ∣ Γ ∣  ⊢ z > ]T) ≡ subT  z A

-}

open import Level
-- open import HoTT renaming ( _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂) hiding (_∘_)
open import Hott renaming ( _∙_ to _◾_ ;  transport to tr ; fst to ₁ ; snd to ₂ ; λ= to funext) hiding (_∘_ ; _↦_)
open import monlib
open import Data.Nat renaming (suc to S)

module Syntax  {i : _} where

-- Presyntax
--------------------------------------------------------------------------------




infixl 6 _▶p_

data Tmp : Set (lsucc i)
data Tmp where
  V : ℕ → Tmp
  -- I need also to give the types so that the typing judgment is hprop
  app : Tmp → Tmp → Tmp
  -- this may be a parameterized application, or an infinitary parameterized one
  appNI : {T : Set i} → Tmp → T → Tmp
  -- code for arrow of infinitary parameters
  ΠInf : {T : Set i} → (T → Tmp) → Tmp
  -- this is to flag when a substitituion resutled in an error
  err : Tmp


data Typ  : Set  (lsucc i)
data Typ where
  Up  : Typ
  Elp : Tmp → Typ
  ΠΠp  : Tmp → Typ → Typ
  ΠNI : {T : Set i} → (T → Typ) → Typ
-- data Varp : Set

data Conp : Set (lsucc i)
data Conp where
  ∙p   : Conp
  _▶p_ : Conp → Typ → Conp





∣_∣ : Conp → ℕ
∣ ∙p ∣ = 0
∣ Γ ▶p x ∣ = S ∣ Γ ∣
-- data Varp where
--   v0 : Conp → Typ → Varp
--   vS : Conp → Typ → Varp → Typ → Varp

-- first integer : we don't touch variables below
liftV : ℕ → ℕ → ℕ
-- x if x < n and S x otherwise
liftV 0 x = S x
liftV (S n) 0 = 0
liftV (S n) (S x) = S (liftV n x)


liftt : ℕ → Tmp → Tmp
liftt n (V x) = V (liftV n x)
liftt n (app t u) = app (liftt n t)(liftt n u)
liftt n (appNI t u) = appNI (liftt n t) u
liftt n (ΠInf B) = ΠInf (λ a → liftt n (B a))
liftt n err = err

liftT : ℕ → Typ → Typ
liftT p Up = Up
liftT p (Elp x) = Elp (liftt p x)
-- Γ , Δ ⊢ A
-- Γ , C , wkTel Δ ⊢ w_Δ A
-- Γ , Δ , A ⊢ B
-- Γ , C , wkTel Δ , wk_Δ A ⊢ w_Δ+1 B
liftT p (ΠΠp A B) = ΠΠp (liftt p A) (liftT (1 + p) B)
liftT p (ΠNI {A} B) = ΠNI λ a → liftT p (B a)

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
--   then Γ , subTel t p ⊢ l-subT p t A

infixl 7 _[_↦_]V
infixl 7 _[_↦_]t
infixl 7 _[_↦_]T
 -- infixl 5 _,s_
 -- infix  6 _∘_
 -- infixl 8 _[_]t

_[_↦_]V : (x : ℕ)(p : ℕ)(l : Tmp) → Tmp
-- l-subV : (p : ℕ)(l : Tmp) (x : ℕ) → Tmp


-- don't touch if it is below p
0 [ 0 ↦ l ]V = l

S x [ 0 ↦ l ]V = V x
0  [ (S p) ↦ l ]V = V 0
-- Γ , C , p+1 ⊢ x+1   (and Γ ⊢ t : C)
-- so Γ , C , p ⊢  x   (and Γ ⊢ t : C)
-- so Γ , p ⊢ l-sub p t x
-- so Γ , p+1 ⊢ wk (l-sub p t x)

-- prenons l'exemple x = 0 et p = 2. On veut que wk (l-sub p t x) = 1
-- but, l-sub 2 t 0 = V 0

S x [ S p ↦ l ]V = wkt (x [ p ↦ l ]V)

_[_↦_]t : (t : Tmp)(p : ℕ)(l : Tmp) → Tmp

V x [ p ↦ l ]t  = x [ p ↦ l ]V
(app t u) [ p ↦ l ]t = app (t [ p ↦ l ]t)(u [ p ↦ l ]t)
(appNI t u)[ p ↦ l ]t = appNI (t [ p ↦ l ]t) u
(ΠInf B)[ p ↦ l ]t = ΠInf (λ a →  (B a) [ p ↦ l ]t )
err [ p ↦ l ]t = err

_[_↦_]T : (T : Typ)(x : ℕ) (l : Tmp) → Typ

Up [ p ↦ l ]T = Up
(Elp x) [ p ↦ l ]T  = Elp ( x [ p ↦ l ]t )
-- Γ , C , p,  A ⊢ B and Γ ⊢ t : C
-- then Γ , p , A ⊢ l-sub p+1 t B
(ΠΠp A B) [ p ↦ l ]T = ΠΠp (A [ p ↦ l ]t ) ( B [ (1 + p) ↦ l ]T )
(ΠNI B) [ p ↦ l ]T  = ΠNI  (λ a → (B a) [ p ↦ l ]T )

subTel : (l : Tmp) (Δ : Conp) → Conp

subTel l ∙p = ∙p
subTel l (Δ ▶p A) = (subTel l Δ) ▶p (A [ ∣ Δ ∣ ↦ l ]T )

-- subT : (l : Tmp) (T : Typ) → Typ
-- subt : (l : Tmp) (t : Tmp) → Tmp

-- subT = l-subT 0
-- subt = l-subt 0
-- subV = l-subV 0

{-

Lemmas about commutations of lift

-}
-- auxiliary lemmas to proof lift-lift*
lift-liftV : ∀ n p q → liftV (S (n + p)) (liftV n q) ≡ liftV n (liftV (n + p) q)

lift-liftV 0 p 0 = refl
lift-liftV (S n) 0 0 = refl
lift-liftV (S n) (S p) 0 = refl
lift-liftV 0 p (S x) = refl
lift-liftV (S n) p (S x) rewrite lift-liftV n p x = refl

lift-liftt : ∀ n p q → liftt (S (n + p)) (liftt n q) ≡ liftt n (liftt (n + p) q)

lift-liftt n p (V x) rewrite lift-liftV n p x = refl
lift-liftt n p (app t u) rewrite lift-liftt n p t | lift-liftt n p u = refl
lift-liftt n p (appNI t u) rewrite lift-liftt n p t = refl
lift-liftt n p (ΠInf B)  = ap ΠInf (funext (λ a → lift-liftt n p (B a) ))
lift-liftt n p err = refl
-- lift-liftV p q = {!!}

lift-liftT : ∀ n p q → liftT (S (n + p)) (liftT n q) ≡ liftT n (liftT (n + p) q)

lift-liftT n p Up = refl
lift-liftT n p (Elp x) rewrite lift-liftt n p x = refl
lift-liftT n p (ΠΠp A B) rewrite lift-liftt n p A | lift-liftT (S n) p B = refl
lift-liftT n p (ΠNI B) = ap ΠNI (funext (λ a → lift-liftT n p (B a) ))
-- rewrite lift-liftT n p A | lift-liftT (S n) p B = refl

-- lift-liftT : ∀ p q → liftT (S p) (liftT 0 q) ≡ liftT 0 (liftT p q)
-- lift-liftT = lift-liftT 0


-- lift-liftt : ∀ p q → liftt (S p) (liftt 0 q) ≡ liftt 0 (liftt p q)
-- lift-liftt = lift-liftt 0




-- TODO: faire un schema
-- TODO généraliser à l-subT

-- auxiliary lemmas to prove liftn[n]T 0
liftn[n]V : ∀ n x z → (liftV n x) [ n ↦ z ]V  ≡ V x

liftn[n]V 0 0 z = refl
liftn[n]V (S n) 0 z = refl
liftn[n]V 0 (S x) z = refl
liftn[n]V (S n) (S x) z rewrite liftn[n]V n x z = refl


liftn[n]t : ∀ n t z → (liftt n t) [ n ↦ z ]t  ≡ t

liftn[n]t n (V x) z = liftn[n]V n x z
liftn[n]t n (app t u) z rewrite liftn[n]t n t z | liftn[n]t n u z = refl
liftn[n]t n (appNI t u) z rewrite liftn[n]t n t z = refl
liftn[n]t n (ΠInf B) z rewrite funext (λ a → liftn[n]t n (B a) z) = refl
liftn[n]t n err z = refl

liftn[n]T : ∀ n A z → (liftT n A) [ n ↦ z ]T  ≡ A

liftn[n]T n Up u = refl
liftn[n]T n (Elp x) z rewrite liftn[n]t n x z = refl
liftn[n]T n (ΠΠp A B) u rewrite liftn[n]t n A u | liftn[n]T (S n) B u = refl
liftn[n]T n (ΠNI B) u rewrite  (funext (λ a → liftn[n]T n (B a) u)) = refl

-- liftn[n]T 0 : ∀ A u → (wkT A) [ 0 ↦ u ]T ≡ A
-- liftn[n]T 0 = liftn[n]T 0

-- liftn[n]t 0 : ∀ t u → (wkt t) [ 0 ↦ u ]t ≡ t
-- liftn[n]t 0 = liftn[n]t 0


-- auxiliary lemmas to prove lift-subT
lift+[↦]V : ∀ n p u x → liftt (n + p) (x [ n ↦ u ]V) ≡ (liftV (S (n + p)) x) [ n ↦ (liftt p u) ]V

lift+[↦]V 0 p u (S x) = refl
lift+[↦]V (S n) p u (S x) rewrite lift-liftt 0 (n + p) (x [ n ↦ u ]V) | lift+[↦]V n p u x = refl
lift+[↦]V 0 p u 0 = refl
lift+[↦]V (S n) p u 0 = refl

-- note : wk[↦]T and lift-subT are particular cases of a more general one
-- note lift-subT and lift[+]T are not the same case because subT is l-subT 0


lift+[↦]t : ∀ n p u t → liftt (n + p) (t [ n ↦ u ]t ) ≡ (liftt (S (n + p)) t) [ n ↦ (liftt p u) ]t

lift+[↦]t n p u (V x) = lift+[↦]V n p u x
lift+[↦]t n p z (app t u)
  rewrite lift+[↦]t n p z t
       |  lift+[↦]t n p z u
   = refl
lift+[↦]t n p z (appNI t u) rewrite lift+[↦]t n p z t = refl
lift+[↦]t n p z (ΠInf B) rewrite funext (λ a → lift+[↦]t n p z (B a)) = refl
lift+[↦]t n p u err = refl


lift+[↦]T : ∀ n p u B → liftT (n + p) (B [ n ↦ u ]T ) ≡ (liftT (S (n + p)) B) [ n ↦ (liftt p u) ]T

lift+[↦]T n p u Up = refl
lift+[↦]T n p u (Elp x) rewrite lift+[↦]t n p u x = refl
lift+[↦]T n p u (ΠΠp A B) rewrite lift+[↦]t n p u A | lift+[↦]T (S n) p u B = refl
lift+[↦]T n p u (ΠNI B) rewrite funext (λ a → lift+[↦]T n p u (B a)) = refl


-- lift-subT : ∀ p u B → liftT p (B [ 0 ↦ u ]T ) ≡ (liftT (S p) B) [ 0 ↦ (liftt p u) ]T
-- lift-subT = lift+[↦]T 0

-- auxiliary lemmas to prove wk[↦]T / wk[↦]t
lift[+]V : ∀ Δ u n x → (liftV n x) [ (S (n + Δ)) ↦ u ]V  ≡ liftt n (x [ (n + Δ) ↦ u ]V)

lift[+]V Δ u 0 0 = refl
lift[+]V Δ u (S n) 0 = refl
lift[+]V Δ u 0 (S x) = refl
lift[+]V Δ u (S n) (S x) rewrite lift[+]V Δ u n x = ! (lift-liftt 0 n (x [ n + Δ ↦ u ]V))

lift[+]t : ∀ Δ u n t → (liftt n t) [ (S (n + Δ)) ↦ u ]t ≡ liftt n (t [ (n + Δ) ↦ u ]t )

lift[+]t Δ u n (V x) = lift[+]V Δ u n x
lift[+]t Δ u n (app a b) rewrite lift[+]t Δ u n a | lift[+]t Δ u n b = refl
lift[+]t Δ u n (appNI a b) rewrite lift[+]t Δ u n a = refl
lift[+]t Δ u n (ΠInf B) rewrite funext (λ a → lift[+]t Δ u n (B a)) = refl
lift[+]t Δ u n err = refl

lift[+]T : ∀ Δ u n B → (liftT n B) [ (S (n + Δ)) ↦ u ]T ≡ liftT n ( B [ (n + Δ) ↦ u ]T)

lift[+]T Δ u n Up = refl
lift[+]T Δ u n (Elp x) rewrite lift[+]t Δ u n x = refl
lift[+]T Δ u n (ΠΠp A B)
  rewrite
    lift[+]t Δ u n A | lift[+]T Δ u (S n) B
  = refl
lift[+]T Δ u n (ΠNI B)
  rewrite funext (λ a →  lift[+]T Δ u n (B a))
  = refl



-- u : A
-- A ,  Δ  ⊢  B
-- donc A , Δ , E ⊢ wk B et ensuite Δ , E ⊢ (wk B)[u]
-- mais on peut aussi faire l'inverse: Δ ⊢ B[u] et Δ , E ⊢ wk (B[u]), et ça doit donner la même chose
wk[↦]T : ∀ Δ u B →  (wkT B) [ (S Δ) ↦ u ]T ≡ wkT ( B [ Δ ↦ u ]T)
wk[↦]T Δ u = lift[+]T Δ u 0

wk[↦]t : ∀ Δ u t →  (wkt t) [ (S Δ) ↦ u ]t ≡ wkt (t [ Δ ↦ u ]t)
wk[↦]t Δ u = lift[+]t Δ u 0

[↦][↦]V : ∀ n p z u x →  (x [ n ↦ u ]V) [ (n + p) ↦ z ]t  ≡ (x [ (S (n + p)) ↦ z ]V) [ n ↦ (u [ p ↦ z ]t) ]t

[↦][↦]V 0 p z u 0 = refl
[↦][↦]V (S n) p z u 0 = refl
[↦][↦]V 0 p z u (S x) rewrite liftn[n]t 0 (x [ p ↦ z ]V) (u [ p ↦ z ]t) = refl
[↦][↦]V (S n) p z u (S x) rewrite wk[↦]t (n + p) z (x [ n ↦ u ]V)
  | wk[↦]t n (u [ p ↦ z ]t) (x [ S (n + p) ↦ z ]V)
  | [↦][↦]V n p z u x
  =
  refl


[↦][↦]t : ∀ n p z u t →  ( t [ n ↦ u ]t) [ (n + p) ↦ z ]t ≡ ( t [ (S (n + p)) ↦ z ]t) [ n ↦ ( u [ p ↦ z ]t) ]t

[↦][↦]t n p z w (V x) = [↦][↦]V n p z w x
[↦][↦]t n p z w (app t u)
  rewrite [↦][↦]t n p z w t | [↦][↦]t n p z w u
  = refl
[↦][↦]t n p z w (appNI t u) rewrite [↦][↦]t n p z w t = refl
[↦][↦]t n p z w (ΠInf B) rewrite funext (λ a → [↦][↦]t n p z w (B a)) = refl

[↦][↦]t n p z w err = refl

[↦][↦]T : ∀ n p z u B →  ( B [ n ↦ u ]T) [ (n + p) ↦ z ]T ≡ ( B [ (S (n + p)) ↦ z ]T) [ n ↦ ( u [ p ↦ z ]t) ]T

[↦][↦]T n p z u Up = refl
[↦][↦]T n p z u (Elp x) rewrite [↦][↦]t n p z u x = refl
[↦][↦]T n p z u (ΠΠp A B) rewrite [↦][↦]t n p z u A | [↦][↦]T (S n) p z u B = refl
[↦][↦]T n p z u (ΠNI B) rewrite funext (λ a → [↦][↦]T n p z u (B a)) = refl


-- l-subT-subT : ∀ p z u B →  (B [ 0 ↦ u ]T) [ p ↦ z ]T ≡ ( B [ (S p) ↦ z ]T) [ 0 ↦ ( u [ p ↦ z ]t) ]T
-- l-subT-subT = [↦][↦]T 0



-- A substitution is merely a list of terms
Subp = List Tmp

-- Γ ⊢ σ : Δ
-- Γ , A ⊢ wkS σ : Δ
wkS : Subp → Subp
wkS = map wkt


-- Γ ⊢ σ : Δ
-- Γ , A[σ] ⊢ keep σ : Δ,A
keep : Subp → Subp
keep σ = (V 0) ∷ (wkS σ)

_[_]V : ℕ → Subp → Tmp
n [ s ]V = olookup s n err

_[_]t : Tmp → Subp → Tmp
V x [ s ]t = x [ s ]V
app t u [ s ]t = app (t [ s ]t) (u [ s ]t)
appNI t u [ s ]t = appNI (t [ s ]t) u
ΠInf B [ s ]t = ΠInf  (λ a → (B a) [ s ]t)
err [ s ]t = err

_[_]T : Typ → Subp → Typ
Up [ s ]T = Up
Elp x [ s ]T = Elp (x [ s ]t)
ΠΠp A B [ s ]T = ΠΠp (A [ s ]t) (B [ keep s ]T)
ΠNI B [ s ]T = ΠNI  (λ a → (B a) [ s ]T)


-- lift-liftt-ₛV : ∀ n σ x

{-
Δ , Δ' ⊢ x : A avec ∣ Δ' ∣ = n
Γ  ⊢ σ : Δ
Γ , B ⊢ wkS σ : Δ
Γ , B , Δ'[wk σ] ⊢ keep^n . wkS σ : Δ, Δ'

Γ , B , Δ'[σ] ⊢ x [keep^n . wk σ] : _
and Γ , B , Δ'[σ] ⊢ lift_Δ' (x[keep^n σ])
-}
-- cas general de [wkS]T
[keep∘wk]V : ∀ n σp xp → (xp [ iter n keep (wkS σp) ]V ) ≡  (liftt n (xp [ iter n keep σp ]V))

-- [wkS]V n σp xp = ?

[keep∘wk]V 0 l xp = olookup-map (liftt 0) xp err l
-- [wkS]V 0 (x ∷ σp) (S xp) = {!olookup-map (liftt 0) xp err σp!}

-- x[(wkS (keep^n nil))] = liftt (S n) (x[(wkS (keep^n nil)))])
-- or on sait que l.h.s = liftt 0 (x[keep^n nil])
{-
Γ , A , Δ [] ⊢ keep^n+1 (wkS nil) : Δ_n+1
Δ_n+1 ⊢ S xp : _

Γ, Δ[] ⊢ keep^n+1 nil : Δ_n+1
Δ

olookup (map (liftt 0) (iter n (λ σ → V 0 ∷ map (liftt 0) σ) nil)) xp err

liftt (S n)
(olookup (map (liftt 0) (iter n (λ σ → V 0 ∷ map (liftt 0) σ) nil)) xp err)

  il faut faire commuter olookup et liftt
  et alors le r.h.s devient:

(olookup (map (liftt (S n) . liftt 0) (iter n (λ σ → V 0 ∷ map (liftt 0) σ) nil)) xp err)

et par lift-liftt, c'est

(olookup (map (liftt 0 . liftt n) (iter n (λ σ → V 0 ∷ map (liftt 0) σ) nil)) xp err)

-}
[keep∘wk]V (S n) l (S xp)
  rewrite olookup-map (liftt 0) xp err (iter n keep l)
  | olookup-map (liftt 0) xp err (iter n keep (wkS l))
  =
  ap (liftt 0) ([keep∘wk]V n l xp) ◾ ! (lift-liftt 0 n _)
[keep∘wk]V (S n) σp 0 = refl
-- [wkS]V n l 0 = {!j!}

-- [wkS]V n (x ∷ σp) (S xp) = {!!}


[keep∘wk]t : ∀ n σp tp → (tp [ iter n keep (wkS σp) ]t ) ≡ liftt n (tp [ iter n keep σp ]t)
[keep∘wk]t n σ (V x) = [keep∘wk]V n σ x
[keep∘wk]t n σ (app t u) rewrite [keep∘wk]t n σ t | [keep∘wk]t n σ u = refl
[keep∘wk]t n σ (appNI t u) rewrite [keep∘wk]t n σ t = refl
[keep∘wk]t n σ (ΠInf B) rewrite funext (λ a → [keep∘wk]t n σ (B a)) = refl
[keep∘wk]t n σ err = refl

-- [keep∘wk]T : ∀ σp Ap → (Ap [ (wkS σp) ]T ) ≡ wkT (Ap [ σp ]T)
-- cas general de [wkS]T
[keep∘wk]T : ∀ n σp Ap → (Ap [ iter n keep (wkS σp) ]T ) ≡ liftT n (Ap [ iter n keep σp ]T)
[keep∘wk]T n σp Up = refl
[keep∘wk]T n σp (Elp x) = ap Elp ([keep∘wk]t n σp x)
[keep∘wk]T n σp (ΠΠp Ap Bp) rewrite [keep∘wk]t n σp Ap
  | [keep∘wk]T (S n) σp Bp
  = refl
[keep∘wk]T n σp (ΠNI Bp) rewrite
   funext (λ a → [keep∘wk]T n σp (Bp a))
  = refl

-- needed to prove wkSw (weakening preserve well typed substitution)
[wkS]T : ∀ σp Ap → (Ap [ (wkS σp) ]T ) ≡ wkT (Ap [ σp ]T)
[wkS]T = [keep∘wk]T 0

[wkS]t : ∀ σp tp → (tp [ (wkS σp) ]t ) ≡ wkt (tp [ σp ]t)
[wkS]t = [keep∘wk]t 0

[wkS]V : ∀ σp xp → (xp [ (wkS σp) ]V ) ≡ wkt (xp [ σp ]V)
[wkS]V = [keep∘wk]V 0


-- \wk_n[\keep^n\circ \cons]
-- cas général de wk[,]T
wk[keep∘::]V : ∀ n xp σp tp → (liftV n xp [ iter n keep (tp ∷ σp) ]V) ≡ (xp [ iter n keep σp ]V)

wk[keep∘::]V 0 x σ z = refl
wk[keep∘::]V (S n) 0 σ z = refl
wk[keep∘::]V (S n) (S x) σ z rewrite olookup-map (liftt 0) (liftV n x) err (iter n keep (z ∷ σ))
  | wk[keep∘::]V n x σ z = ! (olookup-map (liftt 0) x err (iter n keep ( σ)))

wk[keep∘::]t : ∀ n up σp tp → (liftt n up [ iter n keep (tp ∷ σp) ]t) ≡ (up [ iter n keep σp ]t)

wk[keep∘::]t n (V x) σp tp = wk[keep∘::]V  n x σp tp
wk[keep∘::]t n (app tp up) σp zp rewrite wk[keep∘::]t n tp σp zp | wk[keep∘::]t n up σp zp = refl
wk[keep∘::]t n (appNI tp up) σp zp rewrite wk[keep∘::]t n tp σp zp = refl
wk[keep∘::]t n (ΠInf B) σp zp rewrite funext (λ  a →   wk[keep∘::]t n (B a) σp zp) = refl
wk[keep∘::]t n err σp zp = refl

wk[keep∘::]T : ∀ n Ap σp tp → (liftT n Ap [ iter n keep (tp ∷ σp) ]T) ≡ (Ap [ iter n keep σp ]T)

wk[keep∘::]T n Up σp' tp = refl
wk[keep∘::]T n (Elp x) σp' tp rewrite wk[keep∘::]t n x σp' tp  = refl
wk[keep∘::]T n (ΠΠp Ap Bp) σp' tp rewrite wk[keep∘::]t n Ap σp' tp
  = ap (ΠΠp _) ( wk[keep∘::]T (S n) Bp σp' tp )
wk[keep∘::]T n (ΠNI Bp) σp' tp
  = ap ΠNI  (funext (λ a → wk[keep∘::]T n (Bp a) σp' tp ))

-- cas particuler: needed to prove that substittion on variables presreve typing : Varw[]
wk[,]T : ∀ Ap tp σp  → ((wkT Ap ) [ tp ∷ σp ]T) ≡ (Ap [ σp ]T)
-- wk[,]T Ap tp σp  = {!Ap!}
wk[,]T Ap tp σp = wk[keep∘::]T 0 Ap σp tp

wk[,]t : ∀ zp tp σp  → (wkt zp [ tp ∷ σp ]t) ≡ (zp [ σp ]t)
wk[,]t zp tp σp = wk[keep∘::]t 0 zp σp tp

wk[,]V : ∀ xp tp σp  → (S xp [ tp ∷ σp ]V) ≡ (xp [ σp ]V)
wk[,]V xp tp σp = wk[keep∘::]V 0 xp σp tp

-- cas général de [0↦][]T
{-

Γ ⊢ σ : Δ
Δ , E , Δ' ⊢ x
Δ ⊢ z : E

l.h.s.
Δ , Δ' ⊢ x[z]
Γ , Δ'[] ⊢ x[z][keep ^n σ]

Γ , E[] , Δ'[] ⊢ x[keep^n+1 σ]
Γ ⊢ z [σ] : E[]

Γ,Δ'[] ⊢ x[keep^n+1 σ][z[σ]]

-}
-- ici je bloque!
[↦][keep]V : ∀ n x z σ
  -- (r : n < length σ)
  →
  ((x [ n ↦ z ]V) [ iter n keep σ ]t) ≡ (x [ iter (S n) keep σ ]V) [ n ↦ (z [ σ ]t) ]t
[↦][keep]V 0 0 z σ = refl
-- [↦][keep]V 0 (S x) z nil  = refl
[↦][keep]V 0 (S x) z σ rewrite olookup-map (liftt 0) x err σ
  = ! (liftn[n]t 0 (x [ σ ]V) (z [ σ ]t))

  -- (liftn[n]t 0 (x [ σ ]V) (z [ σ ]t))
[↦][keep]V (S n) 0 z σ = refl
-- [↦][keep]V (S n) (S x) z σ = wk[,]t (l-subV n z x) (V 0) (wkS (iter n keep σ))
-- wk[,]t (l-subV n z x) (V 0) (wkS (iter n keep σ))
-- ◾ {![↦][keep]V n x z σ!}
-- [↦][keep]V (S n) (S O) z σ = {!!}
-- [↦][keep]V (S n) (S (S x)) z σ = {!!}

[↦][keep]V (S n) (S x) z σ rewrite olookup-map (liftt 0) x err (iter (S n) keep σ)
  | (wk[↦]t n (z [ σ ]t) (x [ iter (S n) keep σ ]V))
  | ! ( [↦][keep]V n x z σ)
  =
  wk[,]t ( x [ n ↦ z ]V ) (V 0) (wkS (iter n keep σ))
  ◾
  [wkS]t (iter n keep σ) ( x [ n ↦ z ]V )



[↦][keep]t : ∀ n t z σ → ( (t [ n ↦ z ]t) [ iter n keep σ ]t) ≡ (t [ iter (S n) keep σ ]t) [ n ↦ (z [ σ ]t) ]t
[↦][keep]t n (V x) z σ = [↦][keep]V n x z σ
[↦][keep]t n (app t u) z σ rewrite [↦][keep]t n t z σ | [↦][keep]t n u z σ = refl
[↦][keep]t n (appNI t u) z σ rewrite [↦][keep]t n t z σ = refl
[↦][keep]t n (ΠInf B) z σ rewrite (funext (λ a → [↦][keep]t n (B a) z σ)) = refl
[↦][keep]t n err z σ = refl

[↦][keep]T : ∀ n A z σ → ( (A [ n ↦ z ]T) [ iter n keep σ ]T) ≡ (A [ iter (S n) keep σ ]T) [ n ↦ (z [ σ ]t) ]T
-- [↦][keep]T n A z σ = ?
[↦][keep]T n Up z σ = refl
[↦][keep]T n (Elp x) z σ rewrite [↦][keep]t n x z σ = refl
[↦][keep]T n (ΠΠp A B) z σ rewrite [↦][keep]t n A z σ = ap (ΠΠp _) ([↦][keep]T (S n) B z σ)
[↦][keep]T n (ΠNI B) z σ = ap ΠNI (funext (λ a → ([↦][keep]T n (B a) z σ)))

{-
ça ne va pas pour le σ !!!
Γ , F ⊢ σ : Δ

Δ , E ⊢ A
Δ , E ⊢ z : E
Δ ⊢ A [z]

Γ , F ⊢ A[z][σ]

Γ , F[σ] ⊢ z[σ] : F
-}
-- needed for Tmw[] : the substitution preserves the well typedness of applications
[0↦][]T : ∀ A z σ → ((A [ 0 ↦ z ]T) [ σ ]T) ≡ (A [ keep σ ]T) [ 0 ↦ z [ σ ]t ]T

[0↦][]T =  [↦][keep]T 0

-- wk[keep∘::]T Ap nil



-- Well-formedness predicates
--------------------------------------------------------------------------------

infix 3 _⊢
infix 3 _⊢_
infix 3 _⊢_∈_
infix 3 _⊢_⇒_
infix 3 _⊢_∈v_

-- It is easy to show that w is propositional, but we don't actually
-- need that proof here. Also, note that Tyw Γ A implies Conw Γ.
data _⊢ : (Γp : Conp) → Set (lsucc i)
data _⊢_  : Conp → (Ap : Typ)   → Set (lsucc i)
data _⊢_∈_ : Conp → Tmp → Typ → Set(lsucc i)
data _⊢_∈v_ : Conp → ℕ → Typ → Set(lsucc i)


-- some aliases
-- infixr 40 Conw
-- syntax Conw Γ =  Γ ⊢
-- \: (Γp : Conp) → Set (lsucc i)
--   Conw = _⊢
-- Conw = _⊢
-- Tyw = _⊢_
-- Tmw = λ Γ A t → Γ ⊢ t ∈ A
-- Varw = λ Γ A x → Γ ⊢ x ∈v A

data _⊢ where
  ∙w : ∙p ⊢
  ▶w : ∀ {Γp} (Γw : Γp ⊢){Ap}(Aw : Γp ⊢ Ap) → (Γp ▶p Ap) ⊢
data _⊢_ where
  Uw : {Γp : Conp}(Γw : Γp ⊢) → Γp ⊢ Up
  Πw : ∀ {Γp : Conp}(Γw : Γp ⊢){ap : Tmp}(Aw : Γp ⊢ ap ∈ Up){Bp : Typ}(Bw : (Γp ▶p Elp ap) ⊢ Bp)
    → Γp ⊢ (ΠΠp ap Bp)
  ΠNIw :
     ∀ {Γp : Conp}(Γw : Γp ⊢){T : Set i} {Bp : T → Typ}(Bw : ∀ t → Γp ⊢ (Bp t))
    → Γp ⊢ (ΠNI Bp)
  Elw : ∀ {Γp}(Γw : Γp ⊢){ap}(aw : Γp ⊢ ap ∈ Up) → Γp ⊢ (Elp ap)
data _⊢_∈_ where
  vw : ∀ {Γp} {Ap : Typ}{xp : ℕ}(xw : Γp ⊢ xp ∈v Ap) →
     Γp ⊢ V xp ∈ Ap
  appw : {Γp : Conp}(Γw : Γp ⊢){ap : Tmp}(aw : Γp ⊢ ap ∈ Up){Bp : Typ}
     (Bw : (Γp ▶p Elp ap ) ⊢ Bp)
     {t : Tmp}(tw : Γp ⊢ t ∈ (ΠΠp ap Bp))
     {u : Tmp}(tw : Γp ⊢ u ∈ (Elp ap))
     → Γp ⊢ app t u ∈ (Bp [ 0 ↦ u ]T)
  appNIw : ∀ {Γp : Conp}(Γw : Γp ⊢)
    {T : Set i} {Bp : T → Typ}(Bw : ∀ t → Γp ⊢ (Bp t))
     {t : Tmp}(tw : Γp ⊢ t ∈ (ΠNI Bp))
     (u : T)
     → Γp ⊢ (appNI t u) ∈ Bp u
  ΠInfw :
     ∀ {Γp : Conp}(Γw : Γp ⊢)
      {T : Set i} {Bp : T → Tmp}(Bw : ∀ t → Γp ⊢ (Bp t) ∈ Up)
      →  Γp ⊢ (ΠInf Bp) ∈ Up
  appInfw : ∀ {Γp : Conp}(Γw : Γp ⊢)
    {T : Set i} {Bp : T → Tmp}(Bw : ∀ t → Γp ⊢ Bp t ∈ Up)
     {t : Tmp}(tw : Γp ⊢ t ∈ (Elp (ΠInf Bp)))
     (u : T)
     → Γp ⊢ (appNI t u) ∈ (Elp (Bp u))

data _⊢_∈v_ where
  V0w : {Γp : Conp} (Γw : Γp ⊢) {Ap : Typ} (Aw : Γp ⊢ Ap) →  (Γp ▶p Ap) ⊢ 0 ∈v (wkT Ap)
  VSw : {Γp : Conp} (Γw : Γp ⊢) {Ap : Typ} (Aw : Γp ⊢ Ap)
     {Bp : Typ} (Bw : Γp ⊢ Bp){xp : ℕ}(xw : Γp ⊢ xp ∈v Bp )
     →  (Γp ▶p Ap) ⊢ (1 + xp) ∈v (wkT Bp)


data _⊢_⇒_ (Γ : Conp) : Subp → Conp → Set (lsucc i) where
  nilw : Γ ⊢ nil ⇒ ∙p
  ,sw : ∀ {Δp}
    (Δw : Δp ⊢)
    {σp}(σw :  Γ ⊢ σp ⇒ Δp){Ap}(Aw : Δp ⊢ Ap){tp}
     (tw : Γ ⊢ tp ∈ (Ap [ σp ]T)) →
     Γ ⊢ (tp ∷ σp) ⇒ (Δp ▶p Ap)




-- Concatenation of a context with a telescope (an untyped telescope is
-- the same as an untyped context, hence the type)
infixl 5 _^^_
_^^_ : Conp → Conp → Conp

Γ ^^ ∙p = Γ
Γ ^^ (Δ ▶p x) =  (Γ ^^ Δ) ▶p x

Telw : (Γ : Conp)(Δ : Conp) → Set (lsucc i)
Telw Γ Δ =  Γ ^^ Δ ⊢


wkTel : Conp → Conp
wkTel ∙p = ∙p
wkTel (Γ ▶p A) = wkTel Γ ▶p liftT ∣ Γ ∣ A


-- do we really need to show this ?
wkTelw : ∀ {Γp}{Ap}(Aw : Γp ⊢ Ap)Δp (Δw : (Γp ^^ Δp) ⊢) → ((Γp ▶p Ap) ^^ wkTel Δp) ⊢
liftTw : ∀ {Γp}{Ap}(Aw : Γp ⊢ Ap)Δp{Bp}(Bw : (Γp ^^ Δp) ⊢ Bp) → ((Γp ▶p Ap) ^^ wkTel Δp) ⊢ (liftT ∣ Δp ∣ Bp)
lifttw : ∀ {Γp}{Ap}(Aw : Γp ⊢ Ap)Δp{Bp}{tp}(tw : (Γp ^^ Δp) ⊢ tp ∈ Bp) →
  ((Γp ▶p Ap) ^^ wkTel Δp) ⊢  (liftt ∣ Δp ∣ tp) ∈ (liftT ∣ Δp ∣ Bp)
liftVw : ∀ {Γp}{Ap}(Aw : Γp ⊢ Ap)Δp{Bp}{xp}(xw : (Γp ^^ Δp) ⊢ xp ∈v Bp) →
   ((Γp ▶p Ap) ^^ wkTel Δp) ⊢ (liftV ∣ Δp ∣ xp) ∈v (liftT ∣ Δp ∣ Bp)

wkTelw  Aw ∙p Δw = ▶w Δw Aw
wkTelw Aw (Δp ▶p Bp) (▶w Δw Bw)  = ▶w (wkTelw Aw Δp Δw) (liftTw Aw Δp Bw)

liftTw Aw Δp (Uw Γw) = Uw (wkTelw Aw Δp Γw)
liftTw Aw Δp (Πw Γw {ap = ap} aw Bw) = Πw (wkTelw Aw Δp Γw) (lifttw Aw Δp aw ) (liftTw Aw (Δp ▶p Elp ap) Bw)
liftTw Aw Δp (ΠNIw Γw {T = T}{Bp = Bp} Bw) = ΠNIw (wkTelw Aw Δp Γw) {T} (λ a → liftTw Aw Δp (Bw a))
   -- (liftTw Aw {!!} {!!})
liftTw Aw Δp (Elw Γw {ap = ap} aw) = Elw (wkTelw Aw Δp Γw) (lifttw Aw Δp aw)


lifttw Aw Δp (vw xw) = vw (liftVw Aw Δp xw)
lifttw Aw Δp (appw  Γw {ap} aw {Bp} Bw {t} tw {u} uw) =
       tr (λ x → _ ⊢ _ ∈ x) (! (lift+[↦]T 0 ∣ Δp ∣ u Bp ))
   (appw  (wkTelw Aw Δp Γw)  (lifttw Aw Δp aw)  (liftTw Aw (Δp ▶p Elp ap) Bw)
   {liftt ∣ Δp ∣ t} (lifttw Aw Δp tw) {liftt ∣ Δp ∣ u} (lifttw Aw Δp uw)
   )

lifttw Aw Δp (appNIw {.(_ ^^ Δp)} Γw {T} {Bp} Bw {t} tw u) =
   appNIw (wkTelw Aw Δp Γw) (λ a →  liftTw Aw Δp (Bw a)) (lifttw Aw Δp tw) u
lifttw Aw Δp (appInfw  Γw {T} {Bp} Bw {t} tw u) =
    appInfw (wkTelw Aw Δp Γw) (λ a →  lifttw Aw Δp (Bw a)) (lifttw Aw Δp tw) u
lifttw Aw Δp (ΠInfw Γw {T = T}{Bp = Bp} Bw) =  ΠInfw (wkTelw Aw Δp Γw) {T} (λ a → lifttw Aw Δp (Bw a))

-- liftVw Aw ∙p xw = VSw _ {!!} _ Aw _ {!!} _ xw
liftVw {Ap = Bp} Bw ∙p (V0w {Γp} Γw {Ap} Aw) = VSw {Γp ▶p Ap} (▶w Γw Aw) {Bp} Bw {wkT Ap}
   (liftTw Aw ∙p Aw) {0} (V0w {Γp} Γw {Ap} Aw)
liftVw Aw ∙p (VSw {Γp} Γw {Ap} Aw' {Bp} Bw {xp} xw) =
  VSw  (▶w Γw Aw') Aw  (liftTw Aw' ∙p Bw)  (VSw {Γp} Γw {Ap} Aw' {Bp} Bw {xp} xw)

liftVw {Γp = Γp}{Ap = T} Tw (Δp ▶p Bp) (V0w  Γw  Aw) =
  tr (λ x →  ((Γp ▶p T) ^^ wkTel Δp) ▶p liftT ∣ Δp ∣ Bp ⊢ 0 ∈v x) (! (lift-liftT 0 ∣ Δp ∣ Bp))
     (V0w {(Γp ▶p T) ^^ wkTel Δp} (wkTelw Tw Δp Γw) {liftT ∣ Δp ∣ Bp} (liftTw Tw Δp Aw))
liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (VSw  Γw  Bw {Ap} Aw {xp} xw) =
  tr (λ x →  _ ⊢ _ ∈v x)  (! (lift-liftT 0 ∣ Δp ∣ Ap))
   (VSw {(Γp ▶p T) ^^ wkTel Δp} (wkTelw Tw Δp Γw) {liftT ∣ Δp ∣ Bp} (liftTw Tw Δp Bw)
    (liftTw Tw Δp Aw)  (liftVw Tw Δp xw))


wkTw : ∀ {Γp}{Ap}(Aw : Γp ⊢ Ap){Bp}(Bw : Γp ⊢ Bp) → (Γp ▶p Ap) ⊢ (wkT Bp)
wkTw Aw Bw = liftTw Aw ∙p Bw

wktw : ∀ {Γp}{Bp}(Bw : Γp ⊢ Bp){Ap}{tp}(tw : Γp ⊢ tp ∈ Ap) →  (Γp ▶p Bp) ⊢ (wkt tp) ∈ (wkT Ap)
wktw Aw tw = lifttw Aw ∙p tw



-- needed for keepw : keep preserve typing of substitutions
wkSw : ∀ {Γp}{Δp}{σp}(σw :  Γp ⊢ σp ⇒ Δp)
  {Ap}(Aw : Γp ⊢ Ap) → (Γp ▶p Ap) ⊢ (wkS σp) ⇒ Δp
wkSw nilw Aw = nilw
wkSw (,sw Δw σw Aw tw) Bw  = ,sw Δw (wkSw σw Bw) Aw (transport! (λ A → _ ⊢ _ ∈ A) ([wkS]T _ _) (wktw Bw tw ))



-- Tmw[] : ∀ {Γp}{tp}
Varw[] : ∀ {Γp}{xp}{Ap}(xw : Γp ⊢ xp ∈v Ap)
  {Δp}{σp}(σw :  Δp ⊢ σp ⇒ Γp) →
  Δp ⊢ (xp [ σp ]V ) ∈ (Ap [ σp ]T)
-- Varw[] {Γp}{xp}{Ap} xw {Δp}{σp}σw = {!!}
Varw[] {.∙p} {xp} {Ap} () {Δp} {.nil} nilw
Varw[] {.(Γp ▶p Ap)} {.0} {.(liftT 0 Ap)} (V0w {Γp} Γw {Ap} Aw₁) {Δp} {(tp ∷ σp)} (,sw Δw σw Aw tw)
  -- rewrite wk[,]T Ap tp σp
  =  transport! (λ A → _ ⊢ _ ∈ A) (wk[,]T Ap tp σp) tw
Varw[] {.(Γp ▶p Ap)} {.(S xp)} {.(liftT 0 Bp)} (VSw {Γp} Γw {Ap} Aw₁ {Bp} Bw {xp} xw) {Δp} {(tp ∷ σp)} (,sw Δw σw Aw tw)
  rewrite wk[,]T Bp tp σp
  =  Varw[] xw σw

-- I don't know if it is good pratique to do that
Sub-Con2w : ∀{Γ}{Δ}{σ}(σw :  Γ ⊢ σ ⇒ Δ) → Δ ⊢
Sub-Con2w nilw = ∙w
Sub-Con2w (,sw Δw σw Aw tw) = ▶w Δw Aw



Tmw[] : ∀ {Γp}{tp}{Ap}(tw : Γp ⊢ tp ∈ Ap )
  {Δp}(Δw : Δp ⊢){σp}(σw :  Δp ⊢ σp ⇒ Γp) →
  Δp ⊢  (tp [ σp ]t ) ∈ (Ap [ σp ]T)

Tyw[] : ∀ {Γp}{Ap}(Aw : Γp ⊢ Ap) {Δp}(Δw : Δp ⊢){σp}(σw :  Δp ⊢ σp ⇒ Γp) → Δp ⊢ (Ap [ σp ]T)

-- needed for the Π case of preservation of typing by the substitution. (Tyw[])
-- Δw is needed for Elw
keepw : ∀ {Γp}(Γw : Γp ⊢){Δp}(Δw : Δp ⊢){σp}(σw :  Γp ⊢ σp ⇒ Δp) {Ap}(Aw : Δp ⊢ Ap ∈ Up ) → (Γp ▶p (Elp Ap [ σp ]T )) ⊢ (keep σp) ⇒ (Δp ▶p Elp Ap)


keepw {Γp}Γw {Δp}Δw{σp}σw {Ap}Aw  = ,sw (Sub-Con2w σw) (wkSw σw ( Elw Γw (Tmw[] Aw Γw σw) )) (Elw Δw Aw)
-- I need to know that Γ is well typed.
  (vw (transport! (λ x → (Γp ▶p (Elp Ap [ σp ]T)) ⊢ 0 ∈v x) ([wkS]T σp (Elp Ap) )
    (V0w {Γp} Γw {Elp Ap [ σp ]T} (Elw Γw (Tmw[]  Aw Γw σw)))))


-- Tyw[] {Γp}{Ap} Aw {Δp}{σp}σw = {!!}
Tyw[] {Γp} {.Up} (Uw Γw) {Δp} Δw {σp} σw = Uw  Δw
Tyw[] {Γp} {.(ΠΠp _ _)} (Πw Γw Aw Bw) {Δp} Δw {σp} σw = Πw Δw (Tmw[] Aw Δw σw )
  (Tyw[] Bw {Δp ▶p _}
  (▶w Δw (Elw Δw (Tmw[] Aw Δw σw )))
    (keepw Δw Γw σw Aw))
Tyw[] {Γp}  (ΠNIw Γw Bw) {Δp} Δw {σp} σw = ΠNIw Δw (λ a → Tyw[] (Bw a) Δw σw)
Tyw[] {Γp} {.(Elp _)} (Elw Γw aw) {Δp} Δw {σp} σw = Elw Δw (Tmw[] aw Δw σw )

-- Tmw[] {Γp}{xp}{Ap} tw {Δp}{σp}σw = {!!}
Tmw[] {Γp} {.(V _)} {Ap} (vw xw) {Δp} Δw {σp} σw = Varw[] xw σw
Tmw[] {Γp} {.(app t u)}  (appw {Γp} Γw {ap} aw {Bp} Bw {t} tw {u} uw) {Δp} Δw {σp} σw
   rewrite [0↦][]T Bp u σp
   =
  appw {Δp} Δw {ap [ σp ]t} (Tmw[] aw Δw σw) {Bp [ keep σp ]T}
    (Tyw[] Bw (▶w Δw (Elw Δw (Tmw[] aw Δw σw))) (keepw Δw Γw σw aw))
    {t [ σp ]t} (Tmw[] tw Δw σw) {u [ σp ]t} (Tmw[] uw Δw σw)
Tmw[] {Γp} (appNIw Γw Bw tw u) {Δp} Δw {σp} σw =
  appNIw Δw (λ a → Tyw[] (Bw a) Δw σw) (Tmw[] tw Δw σw) u
Tmw[] {Γp} (appInfw Γw Bw tw u) {Δp} Δw {σp} σw =
  appInfw Δw (λ a → Tmw[] (Bw a) Δw σw) (Tmw[] tw Δw σw) u
Tmw[] {Γp}  (ΠInfw Γw Bw) {Δp} Δw {σp} σw = ΠInfw Δw (λ a → Tmw[] (Bw a) Δw σw)


{-

I have met a pb in two cases: application case and weakening of a variable
In both cases, I need to show that two syntactic types are equal, and I have no clue..

Maybe if I show that a term has a unique type, it would be enough ?

-}
uniqueTypet : {Γp : Conp} {Ap : Typ}{ t : Tmp} (tw : Γp ⊢ t ∈ Ap )
   {Ap' : Typ} (tw' : Γp ⊢ t ∈ Ap' ) → Ap ≡ Ap'

uniqueTypeV : {Γp : Conp} {Ap : Typ}{ x : _} (xw : Γp ⊢ x ∈v Ap )
   {Ap' : Typ} (xw' : Γp ⊢ x ∈v Ap' ) → Ap ≡ Ap'

-- uniqueTypet {Γp} {Ap} {tp} tw {Ap'} tw' = {!tw!}
uniqueTypet {Γp} {Ap} {.(V _)} (vw xw) {Ap'} (vw xw₁) = uniqueTypeV xw xw₁
-- uniqueTypet {Γp₁} {.(l-subT 0 u Bp)} {.(app t u)} (appw Γp₁ Γw ap₁ tw Bp Bw t tw₁ u tw₂) {Ap'} tw' = {!!}
uniqueTypet {Γp₁}
  (appw {Γp₁} Γw {ap₁} tw {Bp} Bw {t} tw₁ {u} tw₂)  (appw Γw₁ {ap₂} tw' {Bp₁} Bw₁  tw''  tw''')
  with uniqueTypet tw₁ tw''
...  | refl = refl

-- uniqueTypet {Γp} {.(_ u)} {.(appNI _ u)} (appNIw Γw Bw tw u) {.(_ u)} (appNIw Γw₁ Bw₁ tw' .u) = {!!}
uniqueTypet {Γp₁}
  (appNIw Γw Bw tw u)  (appNIw Γw₁ Bw₁ tw'' .u)
  with uniqueTypet tw tw''
...  | refl = refl

-- This is absurd because ΠNI can't equal Elp
uniqueTypet {Γp} {_} {.(appNI _ u)} (appNIw Γw {Bp = Bp} Bw tw u) {_} (appInfw Γw₁  {Bp = Bp'} Bw₁ tw' .u)
  with Bp | Bp' | uniqueTypet tw tw'
  -- absurd-eq : ΠNI .Bp₁ ≡ Elp (ΠInf .Bp)
-- ...  | Bp2 | Bp2' | absurd-eq = {!!}
uniqueTypet {Γp} {.(Bp u)} {.(appNI _ u)} (appNIw Γw {Bp = Bp} Bw tw u) {.(Elp (Bp' u))} (appInfw Γw₁ {Bp = Bp'} Bw₁ tw' .u) | Bp2 | Bp2' | ()


-- uniqueTypet {Γp₁}
--   (appNIw Γw Bw tw u)  (appNIw Γw₁ Bw₁ tw'' .u)
--   with uniqueTypet tw tw''
-- ...  | refl = refl
-- uniqueTypet {Γp} {.Up} {.(ΠInf _)} (ΠInfw Γw Bw) {Ap'} tw' = {!NI!}
uniqueTypet {Γp} {.Up} {.(ΠInf _)} (ΠInfw Γw Bw) {.Up} (ΠInfw Γw' Bw') = refl

-- This is absurd because ΠNI can't equal Elp
uniqueTypet {Γp} {_} {.(appNI _ u)} (appInfw Γw {Bp = Bp} Bw tw u) {_} (appNIw Γw₁ {Bp = Bp'} Bw₁ tw' .u)
  with Bp | Bp' | uniqueTypet tw tw'
  -- absurd-eq : ΠNI .Bp₁ ≡ Elp (ΠInf .Bp)
uniqueTypet {Γp} {.(Elp (Bp u))} {.(appNI _ u)} (appInfw Γw {Bp = Bp} Bw tw u) {.(Bp' u)} (appNIw Γw₁ {Bp = Bp'} Bw₁ tw' .u) | Bp2 | Bp2' | ()
-- ...  | absurd-eq = {!!}

uniqueTypet {Γp} {_} {(appNI _ _)} (appInfw Γw {Bp = Bp} Bw tw u) {_} (appInfw Γw₁ {Bp = Bp'} Bw₁ tw' .u)
  with Bp | Bp' | uniqueTypet tw tw'
uniqueTypet {Γp} {.(Elp (Bp _))} {appNI _ _} (appInfw Γw {Bp = Bp} Bw tw _) {.(Elp (Bp' _))} (appInfw Γw₁ {Bp = Bp'} Bw₁ tw' _) | Bp2 | .Bp2 | refl = refl
  -- = ap Elp {!uniqueTypet tw tw'!}

-- uniqueTypet {Γp₁} {.(l-subT (FromNat.read ℕ-reader _) u Bp₁)} {.(app t u)} (appw Γp₁ Γw ap₁ tw .Bp₁ Bw t tw₁ u tw₂) {.(l-subT (FromNat.read ℕ-reader _) u Bp₁)} (appw .Γp₁ Γw₁ .ap₁ tw' Bp₁ Bw₁ .t tw'' .u tw''') | refl = refl

uniqueTypeV {.(Γp ▶p Ap)} {.(liftT 0 Ap)} {.0} (V0w {Γp} Γw {Ap} Aw) {.(liftT 0 Ap)} (V0w  Γw₁  Aw₁) = refl
uniqueTypeV {.(Γp ▶p Ap)} {.(liftT 0 Bp)} {.(S xp)} (VSw {Γp} Γw {Ap} Aw {Bp} Bw {xp} xw) {.(liftT 0 Bp₁)} (VSw {Γp} Γw₁ Aw₁ {Bp₁} Bw₁ xw') = ap (liftT 0) (uniqueTypeV xw xw')


Conw= : (Γp : Conp) → has-all-paths (Γp ⊢)
Tyw= : (Γp : Conp)(Ap : Typ)  → has-all-paths (Γp ⊢ Ap)
Tmw= : (Γp : Conp)(Ap : Typ)(tp : Tmp)  → has-all-paths (Γp ⊢ tp ∈ Ap )
Varw= : (Γp : Conp)(Ap : Typ)(xp : ℕ)  → has-all-paths (Γp ⊢ xp ∈v Ap )

Conw= .∙p ∙w ∙w = refl
Conw= .(_ ▶p _) (▶w Γw Aw) (▶w Γw' Aw')
  rewrite Conw= _ Γw Γw' | Tyw= _ _ Aw Aw'
  = refl

Tyw= Γp .Up (Uw Γw) (Uw Γw') rewrite Conw= _ Γw Γw' = refl
Tyw= Γp .(ΠΠp _ _) (Πw Γw Aw Bw) (Πw Γw' Aw' Bw')
  rewrite Conw= _ Γw Γw' | Tmw= _ _ _ Aw Aw' |  Tyw= _ _ Bw Bw'
  = refl
Tyw= Γp  _ (ΠNIw Γw Bw) (ΠNIw Γw' Bw')
  rewrite Conw= _ Γw Γw' | funext (λ a →   Tyw= _ _ (Bw a) (Bw' a) )
  = refl
Tyw= Γp .(Elp _) (Elw Γw aw) (Elw Γw' aw')
  rewrite Conw= _ Γw Γw' | Tmw= _ _ _ aw aw'
  = refl



Tmw= Γp Ap .(V _) (vw xw) (vw xw') = ap vw (Varw= _ _ _ xw xw')
Tmw= Γp _ _ (appw  Γw {ap} aw {Bp} Bw {t} tw {u} uw) tw' =
  helper ( Bp [ 0 ↦ u ]T) refl tw'
  where
    helper : (Cp : Typ) (e :  Bp [ 0 ↦ u ]T ≡ Cp) (ttw  : Γp ⊢ (app t u) ∈ Cp ) →
      appw {Γp} Γw {ap} aw {Bp} Bw {t} tw {u} uw == ttw
        [ (λ D → _ ⊢ (app t u) ∈ D) ↓ e ]
   -- Aïe ! COmment je fais pour montrer que Bp = Bp', et ap = ap' ?
   -- remarquons que t a le type ΠΠp ( ap') Bp' et le type ΠΠ (Elp ap') Bp
    helper
       _ e (appw Γw' {ap'} aw' {Bp'} Bw'  tw' uw')

       with uniqueTypet tw' tw | e
    ...  | refl | refl with Conw= _ Γw Γw' | Tyw= _ _ Bw Bw' | Tmw= _ _ _ uw uw' | Tmw= _ _ _ aw aw'
             | Tmw= _ _ _ tw tw'
    ...     | refl | refl | refl | refl | refl = refl

Tmw= Γp _ _ (appNIw Γw {Bp = Bp}Bw {t = t}tw u) tw' =
  helper (Bp u) refl tw'
  where
    helper : (Cp : Typ) (e : Bp u ≡ Cp) (ttw  : Γp ⊢ (appNI t u) ∈ Cp ) →
      appNIw Γw Bw tw u == ttw
        [ (λ D → _ ⊢  (appNI t u) ∈ D ) ↓ e ]

   -- Aïe ! COmment je fais pour montrer que Bp = Bp', et ap = ap' ?
   -- remarquons que t a le type ΠΠp ( ap') Bp' et le type ΠΠ (Elp ap') Bp
    helper _ e (appNIw  Γw' {Bp =  Bp'} Bw' tw' .u)
      with uniqueTypet tw' tw | e
    ...  | refl | refl with Conw= _ Γw Γw' | funext (λ a → Tyw= _ _ (Bw a) (Bw' a))
             | Tmw= _ _ _ tw tw'
    ...     | refl | refl | refl = refl

    -- absurde
    helper _ e (appInfw  Γw' {Bp =  Bp'} Bw' tw' .u)
      with uniqueTypet tw' tw
    ...   | ()

Tmw= Γp .(Elp _) .(appNI _ u) (appInfw Γw {Bp = Bp} Bw {t = t} tw u) tw' =
  helper (Elp (Bp u)) refl tw'
  where
    helper : (Cp : Typ) (e : Elp (Bp u) ≡ Cp) (ttw  : Γp ⊢ (appNI t u) ∈ Cp ) →
      appInfw Γw Bw tw u == ttw
        [ (λ D → _ ⊢ (appNI t u) ∈ D ) ↓ e ]

   -- Aïe ! COmment je fais pour montrer que Bp = Bp', et ap = ap' ?
   -- remarquons que t a le type ΠΠp ( ap') Bp' et le type ΠΠ (Elp ap') Bp
    helper _ e (appInfw  Γw' {Bp =  Bp'} Bw' tw' .u)
      with uniqueTypet tw' tw | e
    ...  | refl | refl with Conw= _ Γw Γw' | funext (λ a → Tmw= _ _ _ (Bw a) (Bw' a))
             | Tmw= _ _ _ tw tw'
    ...     | refl | refl | refl = refl

    -- absurde
    helper _ e (appNIw  Γw' {Bp =  Bp'} Bw' tw' .u)
      with uniqueTypet tw' tw
    ...   | ()

Tmw= Γp .Up .(ΠInf _) (ΠInfw Γw Bw) (ΠInfw Γw' Bw')
  rewrite Conw= _ Γw Γw' | funext (λ a →   Tmw= _ _ _ (Bw a) (Bw' a) )
  = refl





Varw= .(Γp ▶p Ap) .(liftT 0 Ap) .0 (V0w {Γp} Γw {Ap} Aw) (V0w Γw' Aw')
  rewrite Conw= _ Γw Γw' | Tyw= _ _ Aw Aw'
  = refl

Varw= .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw {Γp} Γw {Ap} Aw {Bp} Bw {xp} xw) xw' = helper _ refl xw'
  where
  -- Aïe ! COmment je fais pour montrer que Bp = Bp' ?
  -- remarquons que xp a le type Bp et le type Bp'
    helper :  (Cp : Typ) (e : liftT 0 Bp ≡ Cp) (xxw : (Γp ▶p Ap) ⊢ (S xp) ∈v Cp ) →
      VSw {Γp} Γw {Ap} Aw {Bp} Bw {xp} xw == xxw [ (λ D →  (Γp ▶p Ap) ⊢ S xp ∈v D ) ↓ e ]
    helper .(liftT 0 Bp') e (VSw Γw' Aw' {Bp'} Bw' xw')
      with uniqueTypeV xw' xw
    ... | refl with Varw= _ _ _ xw xw' | Tyw= _ _ Aw Aw' | Tyw= _ _ Bw Bw'
       | Conw= _ Γw Γw'
    ...  | refl | refl | refl | refl with e
    ...  | refl = refl


ConwP : (Γp : Conp) → is-prop (Γp ⊢)
TywP : (Γp : Conp)(Ap : Typ)  → is-prop (Γp ⊢ Ap)
TmwP : (Γp : Conp)(Ap : Typ)(tp : Tmp)  → is-prop (Γp ⊢ tp ∈ Ap )
VarwP : (Γp : Conp)(Ap : Typ)(xp : ℕ)  → is-prop (Γp ⊢ xp ∈v Ap )

ConwP Γp = all-paths-is-prop (Conw= Γp)
TywP Γp Ap = all-paths-is-prop (Tyw= Γp Ap)
TmwP Γp Ap tp = all-paths-is-prop (Tmw= Γp Ap tp)
VarwP Γp Ap xp  = all-paths-is-prop (Varw= Γp Ap xp)

-- in the last version of agda, instance arguments must be implicit
instance
  i-ConwP : {Γp : Conp} → is-prop (Γp ⊢)
  i-TywP : {Γp : Conp}{Ap : Typ}  → is-prop (Γp ⊢ Ap)
  i-TmwP : {Γp : Conp}{Ap : Typ}{tp : Tmp}  → is-prop (Γp ⊢ tp ∈ Ap )
  i-VarwP : {Γp : Conp}{Ap : Typ}{xp : ℕ}  → is-prop (Γp ⊢ xp ∈v Ap )

  i-ConwP = ConwP _
  i-TywP = TywP _ _
  i-TmwP = TmwP _ _ _
  i-VarwP = VarwP _ _ _

Subw= : (Γp : Conp)(Δp : Conp)(s : Subp)  → has-all-paths ( Γp ⊢ s ⇒ Δp)
-- Subw= Γ Δ s sw1 sw2 = {!!}
Subw= Γ .∙p .nil nilw nilw = refl
Subw= Γ .(_ ▶p _) .(_ ∷ _) (,sw Δw sw Aw tw) (,sw Δw' sw' Aw' tw') =
  ap4 (λ a b c → ,sw a b c)
  (prop-has-all-paths _ _)
  (Subw= Γ _ _ sw sw')
  (prop-has-all-paths _ _)
  (prop-has-all-paths _ _)

SubwP : (Γp : Conp) (Δp : Conp)(s : Subp) → is-prop ( Γp ⊢ s ⇒ Δp)
-- SubwP Γ Δ s = {!!}
SubwP Γ Δ s = all-paths-is-prop (Subw= Γ Δ s)

instance
  i-SubwP : {Γp : Conp} {Δp : Conp}{s : Subp} → is-prop ( Γp ⊢ s ⇒ Δp)
  -- SubwP Γ Δ s = {!!}
  i-SubwP = SubwP _ _ _


wkV-keep : ∀ s x →  (S x [ keep s ]V) ≡ wkt (x [ s ]V)
wkV-keep s x = wk[,]V x (V 0) (wkS s) ◾ [wkS]V s x

wkt-keep : ∀ s t →  (wkt t [ keep s ]t) ≡ wkt (t [ s ]t)
wkt-keep s t = wk[,]t t (V 0) (wkS s) ◾ [wkS]t s t

infix  6 _∘p_
-- s2: Γ → Δ et s1 : Δ → Y
-- alors s1 ∘ s2 : Γ → Y
_∘p_ : Subp → Subp → Subp
s1 ∘p s2 = map (_[ s2 ]t) s1

-- needed for keep∘
wkS∘ : ∀ s1 s2 → wkS (s1 ∘p s2) ≡ ((wkS s1) ∘p (keep s2))
wkS∘ s1 s2 = map-∘  wkt (_[ s2 ]t)s1 ◾
  pw-map=  (λ x → ! (wkt-keep s2 x) ) _  ◾ ! (map-∘  (_[ keep s2 ]t) wkt s1)


-- for the Π case of [∘]T
keep∘ : ∀ s1 s2 → (keep (s1 ∘p s2)) ≡ (keep s1 ∘p keep s2)
keep∘ s1 s2 rewrite wkS∘ s1 s2 = refl

-- needed for the _[_]T case of setmodelCOmponents
[∘]V : ∀ x s1 s2 → (x [ s1 ∘p s2 ]V) ≡ (x [ s1 ]V [ s2 ]t)
[∘]V x s1 s2 = olookup-map (_[ s2 ]t) x err s1

[∘]t : ∀ t s1 s2 → (t [ s1 ∘p s2 ]t) ≡ (t [ s1 ]t [ s2 ]t)

[∘]t (V x) s1 s2 = [∘]V x s1 s2
[∘]t (app t u) s1 s2 rewrite [∘]t t s1 s2 | [∘]t u s1 s2 = refl
[∘]t (appNI t u) s1 s2 rewrite [∘]t t s1 s2  = refl
[∘]t (ΠInf B) s1 s2 rewrite
    keep∘ s1 s2
    = ap ΠInf (funext (λ a → [∘]t (B a) s1 s2))
[∘]t err s1 s2 = refl


[∘]T : ∀ A s1 s2 → (A [ s1 ∘p s2 ]T) ≡ (A [ s1 ]T [ s2 ]T)
-- [∘]T A s1 s2 = {!!}
[∘]T Up s1 s2 = refl
[∘]T (Elp x) s1 s2 = ap Elp ([∘]t x s1 s2)
[∘]T (ΠΠp A B) s1 s2
  rewrite [∘]t A s1 s2
  | keep∘ s1 s2
  | [∘]T B (keep s1) (keep s2)
  =
  -- ap (ΠΠp _) ( {!keep∘ _ _!} ◾)
   refl
[∘]T (ΠNI B) s1 s2
  rewrite
    keep∘ s1 s2
  -- | [∘]T B (keep s1) (keep s2)
  =
   ap ΠNI (funext (λ a → [∘]T (B a) s1 s2))

--- needed for the ᶜ case of Sub in SetModelComponentsACDS
∘w : ∀ {Γ} {Δ σ} (σw :  Δ ⊢ σ ⇒ Γ)
   {Y}(Yw : Y ⊢) {δ} (δw :  Y ⊢ δ ⇒ Δ) →
   Y ⊢  (σ ∘p δ) ⇒ Γ
   -- ∘w σw δw = {!δw!}
∘w nilw Yw σw = nilw
∘w (,sw Δw δw Aw tw) Yw σw  =
  ,sw Δw ( ∘w δw Yw σw ) Aw (tr (λ A → _ ⊢ _ ∈ A) (! ([∘]T _ _ _)) (Tmw[] tw Yw σw))


idp :  ℕ → Subp
idp n = iter n keep nil

[idp]V : ∀ {Γ}{A}{x}(xw : Γ ⊢ x ∈v A) → (x [ idp ∣ Γ ∣ ]V) ≡ V x
[idp]V (V0w {Γp} Γw {Ap} Aw) = refl
[idp]V (VSw {Γp} Γw {Ap} Aw {Bp} Bw {xp} xw) =
  [wkS]V (idp ∣ Γp ∣) xp ◾ ap wkt ([idp]V xw)

[idp]t : ∀ {Γ}{A}{t}(tw : Γ ⊢  t ∈ A) → (t [ idp ∣ Γ ∣ ]t) ≡ t
[idp]t (vw xw) = [idp]V xw
[idp]t (appw  Γw  aw Bw tw uw) = ap2 app ([idp]t tw) ([idp]t uw)
[idp]t (appNIw  Γw Bw tw u) = ap (λ z → appNI z u) ([idp]t tw)
[idp]t (appInfw  Γw Bw tw u) = ap (λ z → appNI z u) ([idp]t tw)
[idp]t (ΠInfw Γw Bw) = ap ΠInf (funext (λ a → [idp]t (Bw a)))
-- ap2 app ([idp]t tw) ([idp]t uw)

[idp]T : ∀ {Γ}{A}(Aw : Γ ⊢ A) → (A [ idp ∣ Γ ∣ ]T) ≡ A
[idp]T (Uw  Γw) = refl
-- heureusement qu'on peut faire la récurrence sur Bw
[idp]T (Πw Γw Aw Bw) rewrite [idp]t Aw = ap (ΠΠp _) ([idp]T Bw)
[idp]T (ΠNIw Γw Bw) = ap ΠNI (funext (λ a → [idp]T (Bw a)))
-- ap (ΠΠp _) ([idp]T Bw)
[idp]T (Elw Γw aw) = ap Elp ([idp]t aw)

idpw : ∀ {Γ} (Γw : Γ ⊢) → Γ ⊢ (idp ∣ Γ ∣) ⇒ Γ
idpw {.∙p} ∙w = nilw
idpw {(Γ ▶p A)} (▶w Γw Aw) = ,sw Γw (wkSw (idpw Γw) Aw) Aw
   (transport! (λ B → (Γ ▶p A) ⊢ _ ∈ B)
  ([wkS]T (idp ∣ Γ ∣) A ◾ ap wkT ([idp]T Aw))
  (vw (V0w Γw Aw)))

-- idr : ∀ {Γ Δ : Conp}{σ}(σw : Subw Γ Δ σ) → (σ ∘p idp ∣ Γ ∣) ≡ σ
-- idr nilw = refl
-- idr (,sw σw Aw tw) = ap2 _∷_ ([idp]t tw) (idr σw)

wk∘, : ∀ σ t δ → ((wkS σ) ∘p (t ∷ δ)) ≡ (σ ∘p δ)
wk∘, σ t δ rewrite map-∘ (_[ t ∷ δ ]t) wkt σ =
  pw-map= (λ x → wk[,]t x t δ ) σ
  -- pw-map= (λ x → {![wkS]t!}) σ

idl : ∀ {Γ Δ : Conp}{σ}(σw :  Γ ⊢ σ ⇒ Δ) → (idp ∣ Δ ∣ ∘p σ) ≡ σ
-- idl {Γ}{Δ}{σ}σw = {!!}
idl nilw = refl
idl {Δ = (Δ ▶p A)}{σ = tp ∷ σp}(,sw Δw σw Aw tw) =
  ap (_ ∷_) (wk∘, (idp ∣ Δ ∣ ) tp σp ◾ idl σw)

idr : ∀ {Γ : Conp}{Δ}{σ}(σw :  Γ ⊢ σ ⇒ Δ) → (σ ∘p idp ∣ Γ ∣ ) ≡ σ
-- idr {Γ}Γw{Δ}{σ}σw = ?
idr {Γ} {.∙p} {.nil} nilw = refl
idr {Γ} {.(_ ▶p _)} {.(_ ∷ _)} (,sw Δw σw Aw tw) = ap2 _∷_ ([idp]t tw) (idr σw)
-- idr {.∙p} ∙w {Δ} {σ} σw = {!!}
-- idr {.(_ ▶p _)} (▶w Γw Aw) {Δ} {σ} σw = {!!}

ass : ∀ {σ δ ν} → ((σ ∘p δ) ∘p ν) ≡ (σ ∘p (δ ∘p ν))
ass {σ}{δ}{ν} =
-- pw-map= (λ a → ( [∘]t a δ ν)) σ
   (map-∘ (_[ ν ]t)(_[ δ ]t) σ ) ◾ pw-map= (λ a → ! ([∘]t a δ ν)) σ
--



-- needed for the app case ModelCwfInhabit: subT z T = T [ <z> ]T
<_⊢_> : ∀ n t → Subp
< Γ ⊢ t > = t ∷ (idp Γ)

<>w : ∀{Γ}(Γw :  Γ ⊢){A}(Aw : Γ ⊢ A){t} → Γ ⊢ t ∈ A → Γ ⊢ < ∣ Γ ∣ ⊢ t > ⇒ (Γ ▶p A)
<>w {Γ}Γw{A}Aw{t}tw = ,sw Γw (idpw Γw) Aw (transport! (λ A₁ → Γ ⊢ t ∈ A₁) ([idp]T Aw) tw)

-- Γ , E , Δ ⊢ x : A
-- Γ ⊢ z : E
-- actally, only the size of contexts matters
[<>]V-n : ∀ {Γ}{E}{Δ}{A} {x} (xw :  ((Γ ▶p E) ^^ Δ) ⊢ x ∈v A)  z →
  (x [ iter ∣ Δ ∣ keep <   ∣ Γ ∣ ⊢ z > ]V) ≡ x [ ∣ Δ ∣ ↦ z ]V

-- [<>]V-n n {Γ} {A} {x} xw z = {!n!}

-- [<>]V-n {Γ} {E}{Δ}{A} {x} xw z = {!xw!}
[<>]V-n {Γp} {Ap} {∙p} {.(liftT 0 Ap)} {.0} (V0w  Γw  Aw) z = refl
[<>]V-n {.Γp} {.Ap} {∙p} {.(liftT 0 Bp)} {.(S xp)} (VSw {Γp} Γw {Ap} Aw {Bp} Bw {xp} xw) z =
     wk[,]V xp z (idp (∣ Γp ∣))
    ◾ [idp]V xw

[<>]V-n {Γ} {E} {Δ ▶p B} {.(liftT 0 B)} {.0} (V0w  Γw Aw) z = refl
[<>]V-n {Γ} {E} {Δ ▶p B} {.(liftT 0 Bp)} {.(S xp)} (VSw  Γw Aw {Bp} Bw {xp} xw) z =
     wkV-keep
     (iter ∣ Δ ∣ keep < ∣ Γ ∣ ⊢ z >)
      xp
    ◾
    ap wkt ([<>]V-n xw z)



[<>]t-n : ∀ {Γ}{E}{Δ}{A} {t} (tw :  ((Γ ▶p E) ^^ Δ) ⊢ t ∈ A)  z →
  (t [ iter ∣ Δ ∣ keep <   ∣ Γ ∣ ⊢ z > ]t) ≡  t [ ∣ Δ ∣ ↦ z ]t
[<>]t-n {Γ} {E} {Δ} {A} {.(V _)} (vw xw) z = [<>]V-n xw z
[<>]t-n {Γ} {E} {Δ} {_} {.(app t u)} (appw  Γw  aw {Bp} Bw {t} tw {u} uw) z =
  ap2 app
    ([<>]t-n tw z)
    ([<>]t-n uw z)
[<>]t-n {Γ} {E} {Δ} (appNIw Γw Bw tw u) z = ap (λ z₁ → appNI z₁ u) ([<>]t-n tw z)
[<>]t-n {Γ} {E} {Δ} (appInfw Γw Bw tw u) z = ap (λ z₁ → appNI z₁ u) ([<>]t-n tw z)
[<>]t-n {Γ} {E} {Δ}  (ΠInfw Γw  Bw) z = ap ΠInf (funext (λ a → [<>]t-n (Bw a) z))

[<>]T-n : ∀ {Γ}{E}{Δ}{A}  (Aw : ((Γ ▶p E) ^^ Δ) ⊢ A)  z →
  (A [ iter ∣ Δ ∣ keep <   ∣ Γ ∣ ⊢ z > ]T) ≡  A [ ∣ Δ ∣ ↦ z ]T
[<>]T-n {Γ} {E} {Δ} {.Up} (Uw Γw) z = refl
[<>]T-n {Γ} {E} {Δ} {.(ΠΠp _ _)} (Πw Γw Aw Bw) z =
  ap2 ΠΠp ( ([<>]t-n Aw z)) ([<>]T-n {Δ = Δ ▶p _} Bw z)
[<>]T-n {Γ} {E} {Δ}  (ΠNIw Γw  Bw) z = ap ΠNI (funext (λ a → [<>]T-n (Bw a) z))
[<>]T-n {Γ} {E} {Δ} {.(Elp _)} (Elw Γw aw) z = ap Elp ([<>]t-n aw z)

-- useful for RelationCwfInhabit : the app case
[<>]T : ∀ {Γ E A} (Aw : (Γ ▶p E) ⊢ A) z →
  (A [ < ∣ Γ ∣  ⊢ z > ]T) ≡ A [ 0 ↦ z ]T
[<>]T {Γ}{E}{ A} Aw z = [<>]T-n {Γ}{E} {∙p} Aw z

-- strange that i did not use this before InitialMorphism (variable case):
wk : ∀ Γ → Subp
wk Γ = wkS (idp Γ )

wk=[wk]T : ∀{Γ}{A}(Aw : Γ ⊢ A) → wkT A ≡ A [ wk ∣ Γ ∣ ]T
wk=[wk]T {Γ}{A}Aw = ! (([wkS]T _ _) ◾ ap wkT  ([idp]T Aw))

wk=[wk]t : ∀{Γ}{A}{t}(tw : Γ ⊢  t ∈ A) → wkt t ≡ t [ wk ∣ Γ ∣ ]t
wk=[wk]t {Γ}{A}{t}tw = ! ([wkS]t (idp ∣ Γ ∣) t ◾ ap wkt  ([idp]t tw))



-- -}
