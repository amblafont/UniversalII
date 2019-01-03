{-
This file should work without K

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
  subT-wkT : subT u (wkT A) ≡ A 
  lift-subT : liftT p (subT u B) ≡ subT (liftt p u)(liftT (S p) B)
  l-subT-subT : l-subT p z (subT u B) ≡ subT (l-subt p z u)(l-subT (S p) z B)

Interaction with full substitution between these and full substitutions:

  wk=wkS :  (A [ (wkS σ) ] ) ≡ wk (A [ σ ])
  wk[,] : ((wk A ) [ t :: σ ]) ≡ (A [ σ ])
  sub[] : (sub z A [ σ ])   ≡ sub (z [ σ ]t) (A [ keep σ ])


Then, preservation of typing by weakening/telescope and full substituions.

Finally, proof that these well typed judgements are hProp 

Complements lemmas and definitions:
 -  identity substitution, composition of substitutions, etc..
 for example:
[<>]T : ((Γ ▶p E) ⊢ A) z → (A [ < ∣ Γ ∣  ⊢ z > ]T) ≡ subT  z A

-}

open import Level 
open import HoTT renaming ( _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
  hiding (_∘_)
open import monlib
 
module Syntax where

-- Presyntax
--------------------------------------------------------------------------------




infixl 6 _▶p_

data Tmp : Set
data Tmp where
  V : ℕ → Tmp
  -- I need also to give the types so that the typing judgment is hprop
  app : Tmp → Tmp → Tmp
  -- this is to flag when a substitituion resutled in an error
  err : Tmp


data Typ  : Set
data Typ where
  Up  : Typ
  Elp : Tmp → Typ
  ΠΠp  : Typ → Typ → Typ
-- data Varp : Set

data Conp : Set
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
liftV O x = S x
liftV (S n) O = 0
liftV (S n) (S x) = S (liftV n x)


liftt : ℕ → Tmp → Tmp
liftt n (V x) = V (liftV n x)
liftt n (app t u) = app (liftt n t)(liftt n u)
liftt n err = err

liftT : ℕ → Typ → Typ
liftT p Up = Up
liftT p (Elp x) = Elp (liftt p x)
-- Γ , Δ ⊢ A
-- Γ , C , wkTel Δ ⊢ w_Δ A
-- Γ , Δ , A ⊢ B
-- Γ , C , wkTel Δ , wk_Δ A ⊢ w_Δ+1 B
liftT p (ΠΠp A B) = ΠΠp (liftT p A) (liftT (1 + p) B)

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

l-subt : (p : ℕ)(l : Tmp) (t : Tmp) → Tmp

l-subt p l (V x) = (l-subV p l x)
l-subt p l (app t u) = app (l-subt p l t)(l-subt p l u)
l-subt p l err = err

l-subT : (p : ℕ)(l : Tmp) (T : Typ) → Typ

l-subT p l Up = Up
l-subT p l (Elp x) = Elp (l-subt p l x)
-- Γ , C , p,  A ⊢ B and Γ ⊢ t : C
-- then Γ , p , A ⊢ l-sub p+1 t B
l-subT p l (ΠΠp A B) = ΠΠp (l-subT p l A) (l-subT (1 + p) l B)

subTel : (l : Tmp) (Δ : Conp) → Conp

subTel l ∙p = ∙p
subTel l (Δ ▶p A) = (subTel l Δ) ▶p (l-subT ∣ Δ ∣ l A)

subT : (l : Tmp) (T : Typ) → Typ
subt : (l : Tmp) (t : Tmp) → Tmp
subV : (l : Tmp) (x : ℕ) → Tmp

subT = l-subT 0
subt = l-subt 0
subV = l-subV 0

{-

Lemmas about commutations of lift

-}
-- auxiliary lemmas to proof lift-lift*
n-lift-liftV : ∀ n p q → liftV (S (n + p)) (liftV n q) ≡ liftV n (liftV (n + p) q)

n-lift-liftV O p O = refl
n-lift-liftV (S n) O O = refl
n-lift-liftV (S n) (S p) O = refl
n-lift-liftV O p (S x) = refl
n-lift-liftV (S n) p (S x) rewrite n-lift-liftV n p x = refl

n-lift-liftt : ∀ n p q → liftt (S (n + p)) (liftt n q) ≡ liftt n (liftt (n + p) q)

n-lift-liftt n p (V x) rewrite n-lift-liftV n p x = refl
n-lift-liftt n p (app t u) rewrite n-lift-liftt n p t | n-lift-liftt n p u = refl
n-lift-liftt n p err = refl
-- lift-liftV p q = {!!}

n-lift-liftT : ∀ n p q → liftT (S (n + p)) (liftT n q) ≡ liftT n (liftT (n + p) q)

n-lift-liftT n p Up = refl
n-lift-liftT n p (Elp x) rewrite n-lift-liftt n p x = refl
n-lift-liftT n p (ΠΠp A B) rewrite n-lift-liftT n p A | n-lift-liftT (S n) p B = refl

lift-liftT : ∀ p q → liftT (S p) (liftT 0 q) ≡ liftT 0 (liftT p q)
lift-liftT = n-lift-liftT 0


lift-liftt : ∀ p q → liftt (S p) (liftt 0 q) ≡ liftt 0 (liftt p q)
lift-liftt = n-lift-liftt 0




-- TODO: faire un schema
-- TODO généraliser à l-subT

-- auxiliary lemmas to prove subT-wkT
n-subV-wkV : ∀ n x z → l-subV n z (liftV n x) ≡ V x 

n-subV-wkV O O z = refl
n-subV-wkV (S n) O z = refl
n-subV-wkV O (S x) z = refl
n-subV-wkV (S n) (S x) z rewrite n-subV-wkV n x z = refl

n-subt-wkt : ∀ n t z → l-subt n z (liftt n t) ≡ t 

n-subt-wkt n (V x) z = n-subV-wkV n x z
n-subt-wkt n (app t u) z rewrite n-subt-wkt n t z | n-subt-wkt n u z = refl
n-subt-wkt n err z = refl

n-subT-wkT : ∀ n A z → l-subT n z (liftT n A) ≡ A 

n-subT-wkT n Up u = refl
n-subT-wkT n (Elp x) z rewrite n-subt-wkt n x z = refl
n-subT-wkT n (ΠΠp A B) u rewrite n-subT-wkT n A u | n-subT-wkT (S n) B u = refl

subT-wkT : ∀ A u → subT u (wkT A) ≡ A 
subT-wkT = n-subT-wkT 0

subt-wkt : ∀ t u → subt u (wkt t) ≡ t 
subt-wkt = n-subt-wkt 0


-- auxiliary lemmas to prove lift-subT
lift-l-subV : ∀ n p u x → liftt (n + p) (l-subV n u x) ≡ l-subV n (liftt p u)(liftV (S (n + p)) x)

lift-l-subV O p u (S x) = refl
lift-l-subV (S n) p u (S x) rewrite lift-liftt (n + p) (l-subV n u x) | lift-l-subV n p u x = refl
lift-l-subV O p u O = refl
lift-l-subV (S n) p u O = refl

-- note : l-subT-wkT and lift-subT are particular cases of a more general one
-- note lift-subT and l-subT-liftT are not the same case because subT is l-subT 0


lift-l-subt : ∀ n p u t → liftt (n + p) (l-subt n u t) ≡ l-subt n (liftt p u)(liftt (S (n + p)) t)

lift-l-subt n p u (V x) = lift-l-subV n p u x
lift-l-subt n p z (app t u)
  rewrite lift-l-subt n p z t
       |  lift-l-subt n p z u
   = refl
lift-l-subt n p u err = refl


lift-l-subT : ∀ n p u B → liftT (n + p) (l-subT n u B) ≡ l-subT n (liftt p u)(liftT (S (n + p)) B)

lift-l-subT n p u Up = refl
lift-l-subT n p u (Elp x) rewrite lift-l-subt n p u x = refl
lift-l-subT n p u (ΠΠp A B) rewrite lift-l-subT n p u A | lift-l-subT (S n) p u B = refl


lift-subT : ∀ p u B → liftT p (subT u B) ≡ subT (liftt p u)(liftT (S p) B)
lift-subT = lift-l-subT 0

-- auxiliary lemmas to prove l-subT-wkT / l-subt-wkt
l-subV-liftV : ∀ Δ u n x → l-subV (S (n + Δ)) u (liftV n x) ≡ liftt n (l-subV (n + Δ) u x)

l-subV-liftV Δ u O O = refl
l-subV-liftV Δ u (S n) O = refl
l-subV-liftV Δ u O (S x) = refl
l-subV-liftV Δ u (S n) (S x) rewrite l-subV-liftV Δ u n x = ! (lift-liftt n (l-subV (n + Δ) u x))

l-subt-liftt : ∀ Δ u n t → l-subt (S (n + Δ)) u (liftt n t) ≡ liftt n (l-subt (n + Δ) u t)

l-subt-liftt Δ u n (V x) = l-subV-liftV Δ u n x
l-subt-liftt Δ u n (app a b) rewrite l-subt-liftt Δ u n a | l-subt-liftt Δ u n b = refl
l-subt-liftt Δ u n err = refl

l-subT-liftT : ∀ Δ u n B → l-subT (S (n + Δ)) u (liftT n B) ≡ liftT n (l-subT (n + Δ) u B)

l-subT-liftT Δ u n Up = refl
l-subT-liftT Δ u n (Elp x) rewrite l-subt-liftt Δ u n x = refl
l-subT-liftT Δ u n (ΠΠp A B)
  rewrite
    l-subT-liftT Δ u n A
    | l-subT-liftT Δ u (S n) B
  = refl



-- u : A
-- A ,  Δ  ⊢  B
-- donc A , Δ , E ⊢ wk B et ensuite Δ , E ⊢ (wk B)[u]
-- mais on peut aussi faire l'inverse: Δ ⊢ B[u] et Δ , E ⊢ wk (B[u]), et ça doit donner la même chose
l-subT-wkT : ∀ Δ u B → l-subT (S Δ) u (wkT B) ≡ wkT (l-subT Δ u B)
l-subT-wkT Δ u = l-subT-liftT Δ u 0

l-subt-wkt : ∀ Δ u t → l-subt (S Δ) u (wkt t) ≡ wkt (l-subt Δ u t)
l-subt-wkt Δ u = l-subt-liftt Δ u 0

l-subV-l-subV : ∀ n p z u x → l-subt (n + p) z (l-subV n u x) ≡ l-subt n (l-subt p z u)(l-subV (S (n + p)) z x)

l-subV-l-subV O p z u O = refl
l-subV-l-subV (S n) p z u O = refl
l-subV-l-subV O p z u (S x) rewrite n-subt-wkt 0 (l-subV p z x) (l-subt p z u) = refl
l-subV-l-subV (S n) p z u (S x) rewrite l-subt-wkt (n + p) z (l-subV n u x)
  | l-subt-wkt n (l-subt p z u) (l-subV (S (n + p)) z x)
  | l-subV-l-subV n p z u x
  =
  refl


l-subt-l-subt : ∀ n p z u t → l-subt (n + p) z (l-subt n u t) ≡ l-subt n (l-subt p z u)(l-subt (S (n + p)) z t)

l-subt-l-subt n p z w (V x) = l-subV-l-subV n p z w x
l-subt-l-subt n p z w (app t u)
  rewrite l-subt-l-subt n p z w t
  | l-subt-l-subt n p z w u
  = refl
l-subt-l-subt n p z w err = refl

l-subT-l-subT : ∀ n p z u B → l-subT (n + p) z (l-subT n u B) ≡ l-subT n (l-subt p z u)(l-subT (S (n + p)) z B)

l-subT-l-subT n p z u Up = refl
l-subT-l-subT n p z u (Elp x) rewrite l-subt-l-subt n p z u x = refl
l-subT-l-subT n p z u (ΠΠp A B) rewrite l-subT-l-subT n p z u A | l-subT-l-subT (S n) p z u B = refl


l-subT-subT : ∀ p z u B → l-subT p z (subT u B) ≡ subT (l-subt p z u)(l-subT (S p) z B)
l-subT-subT = l-subT-l-subT 0



-- A substitution is merely a list of terms
Subp = List Tmp

-- Γ ⊢ σ : Δ
-- Γ , A ⊢ wkS σ : Δ
wkS : Subp → Subp
wkS = map wkt


-- Γ ⊢ σ : Δ
-- Γ , A[σ] ⊢ keep σ : Δ,A
keep : Subp → Subp
keep σ = (V 0) :: (wkS σ)

_[_]V : ℕ → Subp → Tmp
n [ s ]V = olookup s n err

_[_]t : Tmp → Subp → Tmp
V x [ s ]t = x [ s ]V
app t u [ s ]t = app (t [ s ]t) (u [ s ]t)
err [ s ]t = err

_[_]T : Typ → Subp → Typ
Up [ s ]T = Up
Elp x [ s ]T = Elp (x [ s ]t)
ΠΠp A B [ s ]T = ΠΠp (A [ s ]T) (B [ keep s ]T)


-- lift-liftt-ₛV : ∀ n σ x

{-
Δ , Δ' ⊢ x : A avec ∣ Δ' ∣ = n
Γ  ⊢ σ : Δ
Γ , B ⊢ wkS σ : Δ
Γ , B , Δ'[wk σ] ⊢ keep^n . wkS σ : Δ, Δ'

Γ , B , Δ'[σ] ⊢ x [keep^n . wk σ] : _
and Γ , B , Δ'[σ] ⊢ lift_Δ' (x[keep^n σ])
-}
-- cas general de wkT=wkS
liftV=wkS : ∀ n σp xp → (xp [ iter n keep (wkS σp) ]V ) ≡  (liftt n (xp [ iter n keep σp ]V))

-- wkV=wkS n σp xp = ?

liftV=wkS O l xp = olookup-map (liftt 0) xp err l
-- wkV=wkS O (x :: σp) (S xp) = {!olookup-map (liftt 0) xp err σp!}

-- x[(wkS (keep^n nil))] = liftt (S n) (x[(wkS (keep^n nil)))])
-- or on sait que l.h.s = liftt 0 (x[keep^n nil])
{-
Γ , A , Δ [] ⊢ keep^n+1 (wkS nil) : Δ_n+1
Δ_n+1 ⊢ S xp : _

Γ, Δ[] ⊢ keep^n+1 nil : Δ_n+1
Δ

olookup (map (liftt 0) (iter n (λ σ → V 0 :: map (liftt 0) σ) nil)) xp err

liftt (S n)
(olookup (map (liftt 0) (iter n (λ σ → V 0 :: map (liftt 0) σ) nil)) xp err)

  il faut faire commuter olookup et liftt
  et alors le r.h.s devient:

(olookup (map (liftt (S n) . liftt 0) (iter n (λ σ → V 0 :: map (liftt 0) σ) nil)) xp err)

et par lift-liftt, c'est

(olookup (map (liftt 0 . liftt n) (iter n (λ σ → V 0 :: map (liftt 0) σ) nil)) xp err)

-}
liftV=wkS (S n) l (S xp)
  rewrite olookup-map (liftt 0) xp err (iter n keep l)
  | olookup-map (liftt 0) xp err (iter n keep (wkS l))
  =
  ap (liftt 0) (liftV=wkS n l xp) ◾ ! (lift-liftt n _)
liftV=wkS (S n) σp O = refl
-- wkV=wkS n l 0 = {!j!}

-- wkV=wkS n (x :: σp) (S xp) = {!!}


liftt=wkS : ∀ n σp tp → (tp [ iter n keep (wkS σp) ]t ) ≡ liftt n (tp [ iter n keep σp ]t)
liftt=wkS n σ (V x) = liftV=wkS n σ x
liftt=wkS n σ (app t u) rewrite liftt=wkS n σ t | liftt=wkS n σ u = refl
liftt=wkS n σ err = refl

-- liftT=wkS : ∀ σp Ap → (Ap [ (wkS σp) ]T ) ≡ wkT (Ap [ σp ]T)
-- cas general de wkT=wkS
liftT=wkS : ∀ n σp Ap → (Ap [ iter n keep (wkS σp) ]T ) ≡ liftT n (Ap [ iter n keep σp ]T)
liftT=wkS n σp Up = refl
liftT=wkS n σp (Elp x) = ap Elp (liftt=wkS n σp x)
liftT=wkS n σp (ΠΠp Ap Bp) rewrite liftT=wkS n σp Ap
  | liftT=wkS (S n) σp Bp
  = refl

-- needed to prove wkSw (weakening preserve well typed substitution)
wkT=wkS : ∀ σp Ap → (Ap [ (wkS σp) ]T ) ≡ wkT (Ap [ σp ]T)
wkT=wkS = liftT=wkS 0

wkt=wkS : ∀ σp tp → (tp [ (wkS σp) ]t ) ≡ wkt (tp [ σp ]t)
wkt=wkS = liftt=wkS 0

wkV=wkS : ∀ σp xp → (xp [ (wkS σp) ]V ) ≡ wkt (xp [ σp ]V)
wkV=wkS = liftV=wkS 0


-- cas général de wk[,]T
liftₛV : ∀ n xp σp tp → (liftV n xp [ iter n keep (tp :: σp) ]V) ≡ (xp [ iter n keep σp ]V)

liftₛV O x σ z = refl
liftₛV (S n) O σ z = refl
liftₛV (S n) (S x) σ z rewrite olookup-map (liftt 0) (liftV n x) err (iter n keep (z :: σ))
  | liftₛV n x σ z = ! (olookup-map (liftt 0) x err (iter n keep ( σ)))

liftₛt : ∀ n up σp tp → (liftt n up [ iter n keep (tp :: σp) ]t) ≡ (up [ iter n keep σp ]t)

liftₛt n (V x) σp tp = liftₛV  n x σp tp
liftₛt n (app tp up) σp zp rewrite liftₛt n tp σp zp | liftₛt n up σp zp = refl
liftₛt n err σp zp = refl

liftₛT : ∀ n Ap σp tp → (liftT n Ap [ iter n keep (tp :: σp) ]T) ≡ (Ap [ iter n keep σp ]T)

liftₛT n Up σp' tp = refl
liftₛT n (Elp x) σp' tp rewrite liftₛt n x σp' tp  = refl
liftₛT n (ΠΠp Ap Bp) σp' tp rewrite liftₛT n Ap σp' tp 
  =
  ap (ΠΠp _) ( liftₛT (S n) Bp σp' tp )

-- cas particuler: needed to prove that substittion on variables presreve typing : Varw[]
wk[,]T : ∀ Ap tp σp  → ((wkT Ap ) [ tp :: σp ]T) ≡ (Ap [ σp ]T)
-- wk[,]T Ap tp σp  = {!Ap!}
wk[,]T Ap tp σp = liftₛT 0 Ap σp tp

wk[,]t : ∀ zp tp σp  → (wkt zp [ tp :: σp ]t) ≡ (zp [ σp ]t)
wk[,]t zp tp σp = liftₛt 0 zp σp tp

wk[,]V : ∀ xp tp σp  → (S xp [ tp :: σp ]V) ≡ (xp [ σp ]V)
wk[,]V xp tp σp = liftₛV 0 xp σp tp

-- cas général de sub[]T
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
l-sub[]V : ∀ n x z σ
  -- (r : n < length σ)
  →
  (l-subV n z x [ iter n keep σ ]t) ≡ l-subt n (z [ σ ]t) (x [ iter (S n) keep σ ]V)
l-sub[]V O O z σ = refl
-- l-sub[]V O (S x) z nil  = refl
l-sub[]V O (S x) z σ rewrite olookup-map (liftt 0) x err σ
  = ! (subt-wkt (x [ σ ]V) (z [ σ ]t))

  -- (subt-wkt (x [ σ ]V) (z [ σ ]t))
l-sub[]V (S n) O z σ = refl
-- l-sub[]V (S n) (S x) z σ = wk[,]t (l-subV n z x) (V 0) (wkS (iter n keep σ))
-- wk[,]t (l-subV n z x) (V 0) (wkS (iter n keep σ))
-- ◾ {!l-sub[]V n x z σ!}
-- l-sub[]V (S n) (S O) z σ = {!!}
-- l-sub[]V (S n) (S (S x)) z σ = {!!}

l-sub[]V (S n) (S x) z σ rewrite olookup-map (liftt 0) x err (iter (S n) keep σ)
  | (l-subt-wkt n (z [ σ ]t) (x [ iter (S n) keep σ ]V))
  | ! ( l-sub[]V n x z σ)
  =
  wk[,]t (l-subV n z x) (V 0) (wkS (iter n keep σ))
  ◾
  wkt=wkS (iter n keep σ) (l-subV n z x)
  


l-sub[]t : ∀ n t z σ → (l-subt n z t [ iter n keep σ ]t) ≡ l-subt n (z [ σ ]t) (t [ iter (S n) keep σ ]t)
l-sub[]t n (V x) z σ = l-sub[]V n x z σ
l-sub[]t n (app t u) z σ rewrite l-sub[]t n t z σ | l-sub[]t n u z σ = refl
l-sub[]t n err z σ = refl

l-sub[]T : ∀ n A z σ → (l-subT n z A [ iter n keep σ ]T) ≡ l-subT n (z [ σ ]t) (A [ iter (S n) keep σ ]T)
-- l-sub[]T n A z σ = ?
l-sub[]T n Up z σ = refl
l-sub[]T n (Elp x) z σ rewrite l-sub[]t n x z σ = refl
l-sub[]T n (ΠΠp A B) z σ rewrite l-sub[]T n A z σ = ap (ΠΠp _) (l-sub[]T (S n) B z σ)

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
sub[]T : ∀ A z σ → (subT z A [ σ ]T) ≡ subT (z [ σ ]t) (A [ keep σ ]T)

sub[]T = l-sub[]T 0 

-- liftₛT Ap nil


  
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
 
data Subw (Γ : Conp) : Conp → Subp → Set where
  nilw : Subw Γ ∙p nil
  ,sw : ∀ {Δp}
    (Δw : Conw Δp)
    {σp}(σw : Subw Γ Δp σp){Ap}(Aw : Tyw Δp Ap){tp}
     (tw : Tmw Γ (Ap [ σp ]T) tp) →
     Subw Γ (Δp ▶p Ap) (tp :: σp)




-- Concatenation of a context with a telescope (an untyped telescope is
-- the same as an untyped context, hence the type)
infixl 5 _^^_
_^^_ : Conp → Conp → Conp

Γ ^^ ∙p = Γ
Γ ^^ (Δ ▶p x) =  (Γ ^^ Δ) ▶p x

Telw : (Γ : Conp)(Δ : Conp) → Set
Telw Γ Δ = Conw (Γ ^^ Δ)


wkTel : Conp → Conp
wkTel ∙p = ∙p
wkTel (Γ ▶p A) = wkTel Γ ▶p liftT ∣ Γ ∣ A


-- do we really need to show this ?
wkTelw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp (Δw : Conw (Γp ^^ Δp)) → Conw ((Γp ▶p Ap) ^^ wkTel Δp)
liftTw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp{Bp}(Bw : Tyw (Γp ^^ Δp) Bp) → Tyw ((Γp ▶p Ap) ^^ wkTel Δp) (liftT ∣ Δp ∣ Bp)
lifttw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp{Bp}{tp}(tw : Tmw (Γp ^^ Δp) Bp tp) →
  Tmw ((Γp ▶p Ap) ^^ wkTel Δp) (liftT ∣ Δp ∣ Bp) (liftt ∣ Δp ∣ tp)
liftVw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap)Δp{Bp}{xp}(xw : Varw (Γp ^^ Δp) Bp xp) →
  Varw ((Γp ▶p Ap) ^^ wkTel Δp) (liftT ∣ Δp ∣ Bp) (liftV ∣ Δp ∣ xp)

wkTelw  Aw ∙p Δw = ▶w Δw Aw
wkTelw Aw (Δp ▶p Bp) (▶w Δw Bw)  = ▶w (wkTelw Aw Δp Δw) (liftTw Aw Δp Bw)

liftTw Aw Δp (Uw .(_ ^^ Δp) Γw) = Uw _ (wkTelw Aw Δp Γw)
liftTw Aw Δp (Πw Γw {ap = ap} aw Bw) = Πw (wkTelw Aw Δp Γw)
   (lifttw Aw Δp aw ) (liftTw Aw (Δp ▶p Elp ap) Bw)
   -- (liftTw Aw {!!} {!!})
liftTw Aw Δp (Elw Γw {ap = ap} aw) = Elw (wkTelw Aw Δp Γw) (lifttw Aw Δp aw)


lifttw Aw Δp (vw xw) = vw (liftVw Aw Δp xw)
lifttw Aw Δp (appw .(_ ^^ Δp) Γw ap aw Bp Bw t tw u uw) =
   
   HoTT.transport (λ x → Tmw _ x _) (! (lift-subT ∣ Δp ∣ u Bp ))
   (appw _ (wkTelw Aw Δp Γw) _ (lifttw Aw Δp aw) _ (liftTw Aw (Δp ▶p Elp ap) Bw)
   (liftt ∣ Δp ∣ t) (lifttw Aw Δp tw) (liftt ∣ Δp ∣ u) (lifttw Aw Δp uw)
   )
   

-- liftVw Aw ∙p xw = VSw _ {!!} _ Aw _ {!!} _ xw
liftVw {Ap = Bp} Bw ∙p (V0w Γp Γw Ap Aw) = VSw (Γp ▶p Ap) (▶w Γw Aw) Bp Bw (wkT Ap)
   (liftTw Aw ∙p Aw) 0 (V0w Γp Γw Ap Aw)
liftVw Aw ∙p (VSw Γp Γw Ap Aw' Bp Bw xp xw) =
  VSw _ (▶w Γw Aw') _ Aw _ (liftTw Aw' ∙p Bw) _ (VSw Γp Γw Ap Aw' Bp Bw xp xw)

liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (V0w .(_ ^^ Δp) Γw .Bp Aw) =
  HoTT.transport (λ x → Varw (((Γp ▶p T) ^^ wkTel Δp) ▶p liftT ∣ Δp ∣ Bp) x 0) (! (lift-liftT ∣ Δp ∣ Bp))
     (V0w ((Γp ▶p T) ^^ wkTel Δp) (wkTelw Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Aw))
liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (VSw .(_ ^^ Δp) Γw .Bp Bw Ap Aw xp xw) =
  HoTT.transport (λ x → Varw _ x _)  (! (lift-liftT ∣ Δp ∣ Ap))
   (VSw ((Γp ▶p T) ^^ wkTel Δp) (wkTelw Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Bw)
   _ (liftTw Tw Δp Aw) _ (liftVw Tw Δp xw))
   

wkTw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap){Bp}(Bw : Tyw Γp Bp) → Tyw (Γp ▶p Ap) (wkT Bp)
wkTw Aw Bw = liftTw Aw ∙p Bw 

wktw : ∀ {Γp}{Bp}(Bw : Tyw Γp Bp){Ap}{tp}(tw : Tmw Γp Ap tp) → Tmw (Γp ▶p Bp) (wkT Ap) (wkt tp)
wktw Aw tw = lifttw Aw ∙p tw

subTelw : ∀ {Γp Ap Δp up}(uw : Tmw Γp Ap up)(Δw : Conw (Γp ▶p Ap ^^ Δp)) → Conw (Γp ^^ (subTel up Δp ))
subTw : ∀ {Γp Ap Δp up Bp }(uw : Tmw Γp Ap up)(Bw : Tyw (Γp ▶p Ap ^^ Δp) Bp )
  → Tyw (Γp ^^ (subTel up Δp )) (l-subT ∣ Δp ∣ up Bp ) 
subtw : ∀ {Γp Ap Δp up Bp tp}(uw : Tmw Γp Ap up)(tw : Tmw (Γp ▶p Ap ^^ Δp) Bp tp)
  → Tmw (Γp ^^ (subTel up Δp )) (l-subT ∣ Δp ∣ up Bp ) (l-subt ∣ Δp ∣ up tp )

subVw : ∀ {Γp Ap Δp up Bp xp}(uw : Tmw Γp Ap up)(xw : Varw (Γp ▶p Ap ^^ Δp) Bp xp)
  → Tmw (Γp ^^ (subTel up Δp )) (l-subT ∣ Δp ∣ up Bp ) (l-subV ∣ Δp ∣ up xp )

subTelw {Γp} {Ap} {∙p} {up} uw (▶w Δw Aw) = Δw
subTelw {Γp} {Ap} {Δp ▶p Bp} {up} uw (▶w Δw Bw) = ▶w (subTelw uw Δw) (subTw uw Bw)



subTw {Γp} {Ep} {Δp} {zp} {.Up} zw (Uw .(Γp ▶p Ep ^^ Δp) Γw) = Uw (Γp ^^ subTel zp Δp) (subTelw zw Γw)
subTw {Γp} {Ep} {Δp} {zp} {.(ΠΠp (Elp _) _)} zw (Πw Γw Aw Bw) =
  Πw (subTelw zw Γw) (subtw {Δp = Δp} zw Aw) (subTw zw Bw )
subTw {Γp} {Ep} {Δp} {zp} {.(Elp _)} zw (Elw Γw aw) = Elw (subTelw zw Γw) (subtw zw aw)

subtw {Γp} {Ep} {Δp} {zp} {tp} zw (vw xw) = subVw zw xw
subtw {Γp} {Ep} {Δp} {zp} {.(l-subT 0 u Bp)} zw (appw .(Γp ▶p Ep ^^ Δp) Γw ap₁ tw Bp Bw t tw₁ u tw₂)
  rewrite l-subT-subT ∣ Δp ∣ zp u Bp
  = appw (Γp ^^ subTel zp Δp) (subTelw zw Γw) (l-subt ∣ Δp ∣ zp ap₁)
    (subtw zw tw) (l-subT (S ∣ Δp ∣) zp Bp)
    (subTw zw Bw)
    (l-subt ∣ Δp ∣ zp t)
    (subtw zw tw₁)
    (l-subt ∣ Δp ∣ zp u)
    (subtw zw tw₂)

-- subVw {Γp} {Ap} {Δp} {up} {Bp} {xp} uw xw = {!!}
subVw {Γp₁} {Ap₁} {∙p} {up} {.(liftT 0 Ap₁)} {.0} uw (V0w Γp₁ Γw Ap₁ Aw)
  rewrite subT-wkT Ap₁ up = uw 
subVw {Γp} {Ap} {∙p} {up} {.(liftT 0 Bp)} {.(S xp)} uw (VSw Γp Γw Ap Aw Bp Bw xp xw)
  rewrite subT-wkT Bp up = vw xw

subVw {Γp} {Ap} {Δp ▶p Cp} {up} {.(liftT 0 Cp)} {.0} uw (V0w .(Γp ▶p Ap ^^ Δp) Γw .Cp Aw)
 rewrite l-subT-wkT ∣ Δp ∣ up Cp
  = vw (V0w (Γp ^^ subTel up Δp) (subTelw uw Γw) (l-subT ∣ Δp ∣ up Cp)
    (subTw uw Aw))

subVw {Γp} {Ap} {Δp ▶p Cp} {up} {.(liftT 0 Bp)} {.(S xp)} uw (VSw .(Γp ▶p Ap ^^ Δp) Γw .Cp Aw Bp Bw xp xw)
  rewrite l-subT-wkT ∣ Δp ∣ up Bp =
  lifttw {Γp ^^ subTel up Δp} {l-subT ∣ Δp ∣ up Cp} (subTw uw Aw) ∙p
    {l-subT ∣ Δp ∣ up Bp} {l-subV ∣ Δp ∣ up xp} ( subVw uw xw)







-- needed for keepw : keep preserve typing of substitutions
wkSw : ∀ {Γp}{Δp}{σp}(σw : Subw Γp Δp σp)
  {Ap}(Aw : Tyw Γp Ap) → Subw (Γp ▶p Ap) Δp (wkS σp)
wkSw nilw Aw = nilw
wkSw (,sw Δw σw Aw tw) Bw  = ,sw Δw (wkSw σw Bw) Aw (transport! (λ A → Tmw _ A _) (wkT=wkS _ _) (wktw Bw tw ))

  


-- Tmw[] : ∀ {Γp}{tp}
Varw[] : ∀ {Γp}{xp}{Ap}(xw : Varw Γp Ap xp)
  {Δp}{σp}(σw : Subw Δp Γp σp) →
  Tmw Δp (Ap [ σp ]T) (xp [ σp ]V )
-- Varw[] {Γp}{xp}{Ap} xw {Δp}{σp}σw = {!!}
Varw[] {.∙p} {xp} {Ap} () {Δp} {.nil} nilw
Varw[] {.(Γp ▶p Ap)} {.0} {.(liftT 0 Ap)} (V0w Γp Γw Ap Aw₁) {Δp} {(tp :: σp)} (,sw Δw σw Aw tw)
  -- rewrite wk[,]T Ap tp σp
  =  transport! (λ A → Tmw _ A _) (wk[,]T Ap tp σp) tw 
Varw[] {.(Γp ▶p Ap)} {.(S xp)} {.(liftT 0 Bp)} (VSw Γp Γw Ap Aw₁ Bp Bw xp xw) {Δp} {(tp :: σp)} (,sw Δw σw Aw tw)
  rewrite wk[,]T Bp tp σp
  =  Varw[] xw σw 


Tmw[] : ∀ {Γp}{tp}{Ap}(tw : Tmw Γp Ap tp)
  {Δp}(Δw : Conw Δp){σp}(σw : Subw Δp Γp σp) →
  Tmw Δp (Ap [ σp ]T) (tp [ σp ]t )


Tyw[] : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap) {Δp}(Δw : Conw Δp){σp}(σw : Subw Δp Γp σp) → Tyw Δp (Ap [ σp ]T) 

-- I don't know if it is good pratique to do that
Sub-Con2w : ∀{Γ}{Δ}{σ}(σw : Subw Γ Δ σ) → Conw Δ
Sub-Con2w nilw = ∙w
Sub-Con2w (,sw Δw σw Aw tw) = ▶w Δw Aw

-- needed for the Π case of preservation of typing by the substitution. (Tyw[])
keepw : ∀ {Γp}(Γw : Conw Γp){Δp}{σp}(σw : Subw Γp Δp σp) {Ap}(Aw : Tyw Δp Ap) → Subw (Γp ▶p (Ap [ σp ]T )) (Δp ▶p Ap) (keep σp)
keepw {Γp}Γw {Δp}{σp}σw {Ap}Aw  = ,sw (Sub-Con2w σw) (wkSw σw (Tyw[] Aw Γw σw)) Aw
-- I need to know that Γ is well typed.
  (vw (transport! (λ x → Varw (Γp ▶p (Ap [ σp ]T)) x 0) (wkT=wkS σp Ap )
    (V0w Γp Γw (Ap [ σp ]T) (Tyw[]  Aw Γw σw))))


-- Tyw[] {Γp}{Ap} Aw {Δp}{σp}σw = {!!}
Tyw[] {Γp} {.Up} (Uw Γp Γw) {Δp} Δw {σp} σw = Uw Δp Δw
Tyw[] {Γp} {.(ΠΠp (Elp _) _)} (Πw Γw Aw Bw) {Δp} Δw {σp} σw = Πw Δw (Tmw[] Aw Δw σw )
  (Tyw[] Bw {Δp ▶p _}
  (▶w Δw (Elw Δw (Tmw[] Aw Δw σw )))
    (keepw Δw σw (Elw Γw Aw)))
Tyw[] {Γp} {.(Elp _)} (Elw Γw aw) {Δp} Δw {σp} σw = Elw Δw (Tmw[] aw Δw σw )

-- Tmw[] {Γp}{xp}{Ap} tw {Δp}{σp}σw = {!!}
Tmw[] {Γp} {.(V _)} {Ap} (vw xw) {Δp} Δw {σp} σw = Varw[] xw σw
Tmw[] {Γp} {.(app t u)} {.(l-subT 0 u Bp)} (appw Γp Γw ap aw Bp Bw t tw u uw) {Δp} Δw {σp} σw
   rewrite sub[]T Bp u σp
   =
  appw Δp Δw (ap [ σp ]t) (Tmw[] aw Δw σw) (Bp [ keep σp ]T)
    (Tyw[] Bw (▶w Δw (Elw Δw (Tmw[] aw Δw σw))) (keepw Δw σw (Elw Γw aw)))
    (t [ σp ]t) (Tmw[] tw Δw σw) (u [ σp ]t) (Tmw[] uw Δw σw)


{-

I have met a pb in two cases: application case and weakening of a variable
In both cases, I need to show that two syntactic types are equal, and I have no clue..

Maybe if I show that a term has a unique type, it would be enough ?

-}
uniqueTypet : {Γp : Conp} {Ap : Typ}{ t : Tmp} (tw : Tmw Γp Ap t)
   {Ap' : Typ} (tw' : Tmw Γp Ap' t) → Ap ≡ Ap'

uniqueTypeV : {Γp : Conp} {Ap : Typ}{ x : _} (xw : Varw Γp Ap x)
   {Ap' : Typ} (xw' : Varw Γp Ap' x) → Ap ≡ Ap'

uniqueTypet {Γp} {Ap} {.(V _)} (vw xw) {Ap'} (vw xw₁) = uniqueTypeV xw xw₁
uniqueTypet {Γp₁} {.(l-subT 0 u Bp)} {.(app t u)}
  (appw Γp₁ Γw ap₁ tw Bp Bw t tw₁ u tw₂) {.(l-subT 0 u Bp₁)} (appw .Γp₁ Γw₁ ap₂ tw' Bp₁ Bw₁ .t tw'' .u tw''')
  with uniqueTypet tw₁ tw''
...  | refl = refl
-- uniqueTypet {Γp₁} {.(l-subT (FromNat.read ℕ-reader _) u Bp₁)} {.(app t u)} (appw Γp₁ Γw ap₁ tw .Bp₁ Bw t tw₁ u tw₂) {.(l-subT (FromNat.read ℕ-reader _) u Bp₁)} (appw .Γp₁ Γw₁ .ap₁ tw' Bp₁ Bw₁ .t tw'' .u tw''') | refl = refl

uniqueTypeV {.(Γp ▶p Ap)} {.(liftT 0 Ap)} {.0} (V0w Γp Γw Ap Aw) {.(liftT 0 Ap)} (V0w .Γp Γw₁ .Ap Aw₁) = refl
uniqueTypeV {.(Γp ▶p Ap)} {.(liftT 0 Bp)} {.(S xp)} (VSw Γp Γw Ap Aw Bp Bw xp xw) {.(liftT 0 Bp₁)} (VSw .Γp Γw₁ .Ap Aw₁ Bp₁ Bw₁ .xp xw') = ap (liftT 0) (uniqueTypeV xw xw')

Conw= : (Γp : Conp) → has-all-paths (Conw Γp)
Tyw= : (Γp : Conp)(Ap : Typ)  → has-all-paths (Tyw Γp Ap)
Tmw= : (Γp : Conp)(Ap : Typ)(tp : Tmp)  → has-all-paths (Tmw Γp Ap tp)
Varw= : (Γp : Conp)(Ap : Typ)(xp : ℕ)  → has-all-paths (Varw Γp Ap xp)

Conw= .∙p ∙w ∙w = refl
Conw= .(_ ▶p _) (▶w Γw Aw) (▶w Γw' Aw')
  rewrite Conw= _ Γw Γw' | Tyw= _ _ Aw Aw'
  = refl

Tyw= Γp .Up (Uw .Γp Γw) (Uw .Γp Γw') rewrite Conw= _ Γw Γw' = refl
Tyw= Γp .(ΠΠp (Elp _) _) (Πw Γw Aw Bw) (Πw Γw' Aw' Bw')
  rewrite Conw= _ Γw Γw' | Tmw= _ _ _ Aw Aw' |  Tyw= _ _ Bw Bw'
  = refl
Tyw= Γp .(Elp _) (Elw Γw aw) (Elw Γw' aw')
  rewrite Conw= _ Γw Γw' | Tmw= _ _ _ aw aw'
  = refl



Tmw= Γp Ap .(V _) (vw xw) (vw xw') = ap vw (Varw= _ _ _ xw xw')
Tmw= Γp .(l-subT 0 u Bp) .(app t u) (appw .Γp Γw ap aw Bp Bw t tw u uw) tw' =
  helper (l-subT 0 u Bp) refl tw'
  where
    helper : (Cp : Typ) (e : l-subT 0 u Bp ≡ Cp) (ttw  : Tmw Γp Cp (app t u)) →
      appw Γp Γw ap aw Bp Bw t tw u uw == ttw 
        [ (λ D → Tmw _  D (app t u)) ↓ e ]

   -- Aïe ! COmment je fais pour montrer que Bp = Bp', et ap = ap' ?
   -- remarquons que t a le type ΠΠp (Elp ap') Bp' et le type ΠΠ (Elp ap') Bp
    helper
       .(l-subT 0 u Bp') e (appw .Γp Γw' ap' aw' Bp' Bw' .t tw' .u uw')
      
       with uniqueTypet tw' tw | e 
    ...  | refl | refl with Conw= _ Γw Γw' | Tyw= _ _ Bw Bw' | Tmw= _ _ _ uw uw' | Tmw= _ _ _ aw aw' 
             | Tmw= _ _ _ tw tw'
    ...     | refl | refl | refl | refl | refl = refl

Varw= .(Γp ▶p Ap) .(liftT 0 Ap) .0 (V0w Γp Γw Ap Aw) (V0w .Γp Γw' .Ap Aw')
  rewrite Conw= _ Γw Γw' | Tyw= _ _ Aw Aw'
  = refl

Varw= .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) xw' = helper _ refl xw' 
  where
  -- Aïe ! COmment je fais pour montrer que Bp = Bp' ?
  -- remarquons que xp a le type Bp et le type Bp'
    helper :  (Cp : Typ) (e : liftT 0 Bp ≡ Cp) (xxw : Varw (Γp ▶p Ap) Cp (S xp)) →
      VSw Γp Γw Ap Aw Bp Bw xp xw == xxw [ (λ D → Varw (Γp ▶p Ap) D (S xp)) ↓ e ]
    helper .(liftT 0 Bp') e (VSw .Γp Γw' .Ap Aw' Bp' Bw' .xp xw')
      with uniqueTypeV xw' xw
    ... | refl with Varw= _ _ _ xw xw' | Tyw= _ _ Aw Aw' | Tyw= _ _ Bw Bw'
       | Conw= _ Γw Γw'
    ...  | refl | refl | refl | refl with e
    ...  | refl = refl

instance
  ConwP : (Γp : Conp) → is-prop (Conw Γp)
  TywP : (Γp : Conp)(Ap : Typ)  → is-prop (Tyw Γp Ap)
  TmwP : (Γp : Conp)(Ap : Typ)(tp : Tmp)  → is-prop (Tmw Γp Ap tp)
  VarwP : (Γp : Conp)(Ap : Typ)(xp : ℕ)  → is-prop (Varw Γp Ap xp)

  ConwP Γp = all-paths-is-prop (Conw= Γp)
  TywP Γp Ap = all-paths-is-prop (Tyw= Γp Ap)
  TmwP Γp Ap tp = all-paths-is-prop (Tmw= Γp Ap tp)
  VarwP Γp Ap xp  = all-paths-is-prop (Varw= Γp Ap xp)

Subw= : (Γp : Conp)(Δp : Conp)(s : Subp)  → has-all-paths (Subw Γp Δp s)
-- Subw= Γ Δ s sw1 sw2 = {!!}
Subw= Γ .∙p .nil nilw nilw = refl
Subw= Γ .(_ ▶p _) .(_ :: _) (,sw Δw sw Aw tw) (,sw Δw' sw' Aw' tw') =
  ap4 (λ a b c → ,sw a b c)
  (prop-has-all-paths _ _)
  (Subw= Γ _ _ sw sw')
  (prop-has-all-paths _ _)
  (prop-has-all-paths _ _)

instance
  SubwP : (Γp : Conp) (Δp : Conp)(s : Subp) → is-prop (Subw Γp Δp s)
  -- SubwP Γ Δ s = {!!}
  SubwP Γ Δ s = all-paths-is-prop (Subw= Γ Δ s)


wkV-keep : ∀ s x →  (S x [ keep s ]V) ≡ wkt (x [ s ]V)
wkV-keep s x = wk[,]V x (V 0) (wkS s) ◾ wkV=wkS s x

wkt-keep : ∀ s t →  (wkt t [ keep s ]t) ≡ wkt (t [ s ]t)
wkt-keep s t = wk[,]t t (V 0) (wkS s) ◾ wkt=wkS s t

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
[∘]t err s1 s2 = refl


[∘]T : ∀ A s1 s2 → (A [ s1 ∘p s2 ]T) ≡ (A [ s1 ]T [ s2 ]T)  
-- [∘]T A s1 s2 = {!!}
[∘]T Up s1 s2 = refl
[∘]T (Elp x) s1 s2 = ap Elp ([∘]t x s1 s2)
[∘]T (ΠΠp A B) s1 s2
  rewrite [∘]T A s1 s2
  | keep∘ s1 s2
  | [∘]T B (keep s1) (keep s2)
  =
  -- ap (ΠΠp _) ( {!keep∘ _ _!} ◾)
   refl

--- needed for the ᶜ case of Sub in SetModelComponentsACDS
∘w : ∀ {Γ} {Δ σ} (σw : Subw Δ Γ σ)
   {Y}(Yw : Conw Y) {δ} (δw : Subw Y Δ δ) →
   Subw Y Γ (σ ∘p δ)
   -- ∘w σw δw = {!δw!}
∘w nilw Yw σw = nilw
∘w (,sw Δw δw Aw tw) Yw σw  = 
  ,sw Δw ( ∘w δw Yw σw ) Aw (tr (λ A → Tmw _ A _) (! ([∘]T _ _ _)) (Tmw[] tw Yw σw))


idp :  ℕ → Subp
idp n = iter n keep nil

[idp]V : ∀ {Γ}{A}{x}(xw : Varw Γ A x) → (x [ idp ∣ Γ ∣ ]V) ≡ V x
[idp]V (V0w Γp Γw Ap Aw) = refl
[idp]V (VSw Γp Γw Ap Aw Bp Bw xp xw) = 
  wkV=wkS (idp ∣ Γp ∣) xp ◾ ap wkt ([idp]V xw)

[idp]t : ∀ {Γ}{A}{t}(tw : Tmw Γ A t) → (t [ idp ∣ Γ ∣ ]t) ≡ t
[idp]t (vw xw) = [idp]V xw
[idp]t (appw Γp Γw ap aw Bp Bw t tw u uw) =
  ap2 app ([idp]t tw) ([idp]t uw)

[idp]T : ∀ {Γ}{A}(Aw : Tyw Γ A) → (A [ idp ∣ Γ ∣ ]T) ≡ A
[idp]T (Uw Γp Γw) = refl
-- heureusement qu'on peut faire la récurrence sur Bw
[idp]T (Πw Γw Aw Bw) rewrite [idp]t Aw = ap (ΠΠp _) ([idp]T Bw)
[idp]T (Elw Γw aw) = ap Elp ([idp]t aw)

idpw : ∀ {Γ} (Γw : Conw Γ) → Subw Γ Γ (idp ∣ Γ ∣)
idpw {.∙p} ∙w = nilw
idpw {(Γ ▶p A)} (▶w Γw Aw) = ,sw Γw (wkSw (idpw Γw) Aw) Aw
   (transport! (λ B → Tmw (Γ ▶p A) B _)
  (wkT=wkS (idp ∣ Γ ∣) A ◾ ap wkT ([idp]T Aw)) 
  (vw (V0w Γ Γw A Aw)))

-- idr : ∀ {Γ Δ : Conp}{σ}(σw : Subw Γ Δ σ) → (σ ∘p idp ∣ Γ ∣) ≡ σ
-- idr nilw = refl
-- idr (,sw σw Aw tw) = ap2 _::_ ([idp]t tw) (idr σw)

wk∘, : ∀ σ t δ → ((wkS σ) ∘p (t :: δ)) ≡ (σ ∘p δ)
wk∘, σ t δ rewrite map-∘ (_[ t :: δ ]t) wkt σ =
  pw-map= (λ x → wk[,]t x t δ ) σ
  -- pw-map= (λ x → {!wkt=wkS!}) σ

idl : ∀ {Γ Δ : Conp}{σ}(σw : Subw Γ Δ σ) → (idp ∣ Δ ∣ ∘p σ) ≡ σ
idl nilw = refl
idl {Δ = (Δ ▶p A)}{σ = tp :: σp}(,sw Δw σw Aw tw) =
  ap (_ ::_)
-- (wkS σ) ∘ (t :: δ) = (σ ∘ δ)
  (wk∘, (idp ∣ Δ ∣ ) tp σp ◾ idl σw)

  
-- needed for the app case ModelCwfInhabit: subT z T = T [ <z> ]T
<_⊢_> : ∀ n t → Subp
< Γ ⊢ t > = t :: (idp Γ) 

<>w : ∀{Γ}(Γw : Conw Γ){A}(Aw : Tyw Γ A){t} → Tmw Γ A t → Subw Γ (Γ ▶p A) < ∣ Γ ∣ ⊢ t >
<>w {Γ}Γw{A}Aw{t}tw = ,sw Γw (idpw Γw) Aw (transport! (λ A₁ → Tmw Γ A₁ t) ([idp]T Aw) tw)

-- infixl 80 _-_
--TODO : voir si ça peut pas simplifier les prueuve de l-subₛ..
-- Γ , E , Δ ⊢ x : A
-- Γ ⊢ z : E
-- actally, only the size of contexts matters
[<>]V-n : ∀ {Γ}{E}{Δ}{A} {x} (xw : Varw ((Γ ▶p E) ^^ Δ) A x)  z →
  (x [ iter ∣ Δ ∣ keep <   ∣ Γ ∣ ⊢ z > ]V) ≡ l-subV ∣ Δ ∣ z x
  -- (x [ iter ∣ Δ ∣ keep <  (ℕ-pred ∣ Γ ∣) ⊢ z > ]V) ≡ l-subV ∣ Δ ∣ z x
-- [<>]V-n n {Γ} {A} {x} xw z = {!n!}

-- [<>]V-n {Γ} {E}{Δ}{A} {x} xw z = {!xw!}
[<>]V-n {.Γp} {.Ap} {∙p} {.(liftT 0 Ap)} {.0} (V0w Γp Γw Ap Aw) z = refl
[<>]V-n {.Γp} {.Ap} {∙p} {.(liftT 0 Bp)} {.(S xp)} (VSw Γp Γw Ap Aw Bp Bw xp xw) z =
     wk[,]V xp z (idp (∣ Γp ∣)) 
    ◾ [idp]V xw
  
[<>]V-n {Γ} {E} {Δ ▶p B} {.(liftT 0 B)} {.0} (V0w .(Γ ▶p E ^^ Δ) Γw .B Aw) z = refl
[<>]V-n {Γ} {E} {Δ ▶p B} {.(liftT 0 Bp)} {.(S xp)} (VSw .(Γ ▶p E ^^ Δ) Γw .B Aw Bp Bw xp xw) z =
     wkV-keep
     (iter ∣ Δ ∣ keep < ∣ Γ ∣ ⊢ z >)
      xp
    ◾
    ap wkt ([<>]V-n xw z)
  


[<>]t-n : ∀ {Γ}{E}{Δ}{A} {t} (tw : Tmw ((Γ ▶p E) ^^ Δ) A t)  z →
  (t [ iter ∣ Δ ∣ keep <   ∣ Γ ∣ ⊢ z > ]t) ≡ l-subt ∣ Δ ∣ z t
[<>]t-n {Γ} {E} {Δ} {A} {.(V _)} (vw xw) z = [<>]V-n xw z
[<>]t-n {Γ} {E} {Δ} {.(l-subT 0 u Bp)} {.(app t u)} (appw .(Γ ▶p E ^^ Δ) Γw ap aw Bp Bw t tw u uw) z =
  ap2 app
    ([<>]t-n tw z)
    ([<>]t-n uw z)

[<>]T-n : ∀ {Γ}{E}{Δ}{A}  (Aw : Tyw ((Γ ▶p E) ^^ Δ) A)  z →
  (A [ iter ∣ Δ ∣ keep <   ∣ Γ ∣ ⊢ z > ]T) ≡ l-subT ∣ Δ ∣ z A
[<>]T-n {Γ} {E} {Δ} {.Up} (Uw .(Γ ▶p E ^^ Δ) Γw) z = refl
[<>]T-n {Γ} {E} {Δ} {.(ΠΠp (Elp _) _)} (Πw Γw Aw Bw) z =
  ap2 ΠΠp (ap Elp ([<>]t-n Aw z)) ([<>]T-n {Δ = Δ ▶p _} Bw z)
[<>]T-n {Γ} {E} {Δ} {.(Elp _)} (Elw Γw aw) z = ap Elp ([<>]t-n aw z)

-- useful for RelationCwfInhabit : the app case
[<>]T : ∀ {Γ E A} (Aw : Tyw (Γ ▶p E) A) z →
  (A [ < ∣ Γ ∣  ⊢ z > ]T) ≡ subT  z A
[<>]T {Γ}{E}{ A} Aw z = [<>]T-n {Γ}{E} {∙p} Aw z
{- old stuff -}

-- la substitution sur les types requiert dans le cas du Π de pouvoir affaiblir les substitutions
-- le lemme de substitution sur les variables requiert
-- - wk[,]T : ∀ Ap tp σp  → ((wkT Ap ) [ tp :: σp ]T) ≡ (Ap [ σp ]T)
--    Note: dans metacoq, ou chez Théo, la substitution sur les types (par exemple) est définie
--            comme un fold_left de subT.
--            du coup le lemme précédent devient un corrolaire de subT (wkT Ap) = Ap.
--            Mais je préfère une version qui calcule sur les constructeurs de type
-- lequel requiert:
-- - liftₛT : ∀ Ap σp tp σp'  → (liftT (length σp) Ap [ σp ++ (tp :: σp') ]T) ≡ (Ap [ σp ++ σp' ]T)


-- au lieu d'avoir la syntaxe well scoped (c'est à dire indexée par un entier qui indique la taille maximale
-- de variables), j'ai ajouté une constante de terme erreur que je renvoie quand la substitution est mal
-- typée. Tout semble bien marcher, mais par contre pour montrer que la substitution identité préserve
-- la syntaxe, je ne sais pas comment faire..


-- remarque: pour les nombreux lemmes de substitutions (susbtitutions étant listes de termes)
-- peut être que les preuves auraient été beaucoup plus simples en les faisant par récurrence
-- sur le jugment de typage.


{- 
-- weakening from Γ ^ Δ to Γ
-- the first argumet is the length of Γ
-- the seond argument is the length of Δ
liftₛ : ℕ → ℕ → Subp
liftₛ 0 p = nil
liftₛ (S n) p = V p :: (liftₛ n (S p))

-- liftₛ' : ℕ → ℕ → Subp → Subp
-- liftₛ' 0 p = nil
-- liftₛ' (S n) p = V p :: (liftₛ n (S p))

-- length of the context
wkₛ : ℕ → Subp
wkₛ n = liftₛ n 0
-}

-- -- the substitution from Γ , Δ to Γ , A , Δ
-- liftₛ : ℕ → ℕ → Subp
-- liftₛ Γ O = wkₛ Γ
-- liftₛ Γ (S Δ) = V 0 :: liftₛ Γ Δ
