
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
 
module Syntax where

-- Presyntax
--------------------------------------------------------------------------------


-- I can't find this in the HoTT library
-- TODO move to monlib.
olookup : ∀ {a} {A : Set a} (xs : List A) → ℕ → A → A
olookup nil n e = e
olookup (x :: xs) O e = x
olookup (x :: xs) (S n) e = olookup xs n e


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
  -- I need also to give the types so that the typing judgment is hprop
  app : Tmp → Tmp → Tmp
  -- this is to flag when a substitituion resutled in an error
  err : Tmp

Subp = List Tmp
keep : Subp → Subp
keep s = (V 0) :: s

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

∣_∣ : Conp → ℕ
∣ ∙p ∣ = 0
∣ Γ ▶p x ∣ = S ∣ Γ ∣
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
liftt n err = err

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
--   then Γ , subTel t p ⊢ l-subT p t A

subTel : (l : Tmp) (Δ : Conp) → Conp

l-subT : (p : ℕ)(l : Tmp) (T : Typ) → Typ
l-subt : (p : ℕ)(l : Tmp) (t : Tmp) → Tmp
l-subV : (p : ℕ)(l : Tmp) (x : ℕ) → Tmp

subTel l ∙p = ∙p
subTel l (Δ ▶p A) = (subTel l Δ) ▶p (l-subT ∣ Δ ∣ l A)

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

Lemmas about commutations of lift

-}
-- auxiliary lemmas to proof comm-lift*
n-comm-liftT : ∀ n p q → liftT (S (n + p)) (liftT n q) ≡ liftT n (liftT (n + p) q)
n-comm-liftt : ∀ n p q → liftt (S (n + p)) (liftt n q) ≡ liftt n (liftt (n + p) q)
n-comm-liftV : ∀ n p q → liftV (S (n + p)) (liftV n q) ≡ liftV n (liftV (n + p) q)

-- comm-liftV p q = {!!}
comm-liftt : ∀ p q → liftt (S p) (liftt 0 q) ≡ liftt 0 (liftt p q)
comm-liftt = n-comm-liftt 0

comm-liftT : ∀ p q → liftT (S p) (liftT 0 q) ≡ liftT 0 (liftT p q)
comm-liftT = n-comm-liftT 0


n-comm-liftT n p Up = refl
n-comm-liftT n p (Elp x) rewrite n-comm-liftt n p x = refl
n-comm-liftT n p (ΠΠp A B) rewrite n-comm-liftT n p A | n-comm-liftT (S n) p B = refl

n-comm-liftt n p (V x) rewrite n-comm-liftV n p x = refl
n-comm-liftt n p (app t u) rewrite n-comm-liftt n p t | n-comm-liftt n p u = refl

n-comm-liftV O p O = refl
n-comm-liftV (S n) O O = refl
n-comm-liftV (S n) (S p) O = refl
n-comm-liftV O p (S x) = refl
n-comm-liftV (S n) p (S x) rewrite n-comm-liftV n p x = refl


-- TODO: faire un schema
-- TODO généraliser à l-subT

-- auxiliary lemmas to prove subT-wkT
n-subT-wkT : ∀ n A z → l-subT n z (liftT n A) ≡ A 
n-subt-wkt : ∀ n t z → l-subt n z (liftt n t) ≡ t 
n-subV-wkV : ∀ n x z → l-subV n z (liftV n x) ≡ V x 

subT-wkT : ∀ A u → subT u (wkT A) ≡ A 
subT-wkT = n-subT-wkT 0

n-subT-wkT n Up u = refl
n-subT-wkT n (Elp x) z rewrite n-subt-wkt n x z = refl
n-subT-wkT n (ΠΠp A B) u rewrite n-subT-wkT n A u | n-subT-wkT (S n) B u = refl

n-subt-wkt n (V x) z = n-subV-wkV n x z
n-subt-wkt n (app t u) z
  rewrite n-subt-wkt n t z | n-subt-wkt n u z
  = refl

n-subV-wkV O O z = refl
n-subV-wkV (S n) O z = refl
n-subV-wkV O (S x) z = refl
n-subV-wkV (S n) (S x) z rewrite n-subV-wkV n x z = refl

-- auxiliary lemmas to prove lift-subT
lift-l-subT : ∀ n p u B → liftT (n + p) (l-subT n u B) ≡ l-subT n (liftt p u)(liftT (S (n + p)) B)
lift-l-subt : ∀ n p u t → liftt (n + p) (l-subt n u t) ≡ l-subt n (liftt p u)(liftt (S (n + p)) t)
lift-l-subV : ∀ n p u x → liftt (n + p) (l-subV n u x) ≡ l-subV n (liftt p u)(liftV (S (n + p)) x)

lift-subT : ∀ p u B → liftT p (subT u B) ≡ subT (liftt p u)(liftT (S p) B)
lift-subT = lift-l-subT 0
-- note : l-subT-wkT and lift-subT are particular cases of a more general one
-- note lift-subT and l-subT-liftT are not the same case because subT is l-subT 0

lift-l-subT n p u Up = refl
lift-l-subT n p u (Elp x) rewrite lift-l-subt n p u x = refl
lift-l-subT n p u (ΠΠp A B) rewrite lift-l-subT n p u A | lift-l-subT (S n) p u B = refl

lift-l-subt n p u (V x) = lift-l-subV n p u x
lift-l-subt n p z (app t u)
  rewrite lift-l-subt n p z t
       |  lift-l-subt n p z u
   = refl

lift-l-subV O p u O = refl
lift-l-subV (S n) p u O = refl

lift-l-subV O p u (S x) = refl
lift-l-subV (S n) p u (S x) rewrite comm-liftt (n + p) (l-subV n u x)
  | lift-l-subV n p u x
  = refl

-- auxiliary lemmas to prove l-subT-wkT / l-subt-wkt
l-subT-liftT : ∀ Δ u n B → l-subT (S (n + Δ)) u (liftT n B) ≡ liftT n (l-subT (n + Δ) u B)
l-subt-liftt : ∀ Δ u n t → l-subt (S (n + Δ)) u (liftt n t) ≡ liftt n (l-subt (n + Δ) u t)
l-subV-liftV : ∀ Δ u n x → l-subV (S (n + Δ)) u (liftV n x) ≡ liftt n (l-subV (n + Δ) u x)

l-subT-liftT Δ u n Up = refl
l-subT-liftT Δ u n (Elp x) rewrite l-subt-liftt Δ u n x = refl
l-subT-liftT Δ u n (ΠΠp A B)
  rewrite
    l-subT-liftT Δ u n A
    | l-subT-liftT Δ u (S n) B
  = refl

l-subt-liftt Δ u n (V x) = l-subV-liftV Δ u n x
l-subt-liftt Δ u n (app a b)
  rewrite l-subt-liftt Δ u n a
  | l-subt-liftt Δ u n b
   = refl

l-subV-liftV Δ u O O = refl
l-subV-liftV Δ u (S n) O = refl
l-subV-liftV Δ u O (S x) = refl
l-subV-liftV Δ u (S n) (S x) rewrite l-subV-liftV Δ u n x = ! (comm-liftt n (l-subV (n + Δ) u x))

-- u : A
-- A ,  Δ  ⊢  B
-- donc A , Δ , E ⊢ wk B et ensuite Δ , E ⊢ (wk B)[u]
-- mais on peut aussi faire l'inverse: Δ ⊢ B[u] et Δ , E ⊢ wk (B[u]), et ça doit donner la même chose
l-subT-wkT : ∀ Δ u B → l-subT (S Δ) u (wkT B) ≡ wkT (l-subT Δ u B)
l-subt-wkt : ∀ Δ u t → l-subt (S Δ) u (wkt t) ≡ wkt (l-subt Δ u t)

l-subT-wkT Δ u = l-subT-liftT Δ u 0
l-subt-wkt Δ u = l-subt-liftt Δ u 0

l-subT-l-subT : ∀ n p z u B → l-subT (n + p) z (l-subT n u B) ≡ l-subT n (l-subt p z u)(l-subT (S (n + p)) z B)
l-subt-l-subt : ∀ n p z u t → l-subt (n + p) z (l-subt n u t) ≡ l-subt n (l-subt p z u)(l-subt (S (n + p)) z t)
l-subV-l-subV : ∀ n p z u x → l-subt (n + p) z (l-subV n u x) ≡ l-subt n (l-subt p z u)(l-subV (S (n + p)) z x)

l-subT-subT : ∀ p z u B → l-subT p z (subT u B) ≡ subT (l-subt p z u)(l-subT (S p) z B)
l-subT-subT = l-subT-l-subT 0

l-subT-l-subT n p z u Up = refl
l-subT-l-subT n p z u (Elp x) rewrite l-subt-l-subt n p z u x = refl
l-subT-l-subT n p z u (ΠΠp A B) rewrite l-subT-l-subT n p z u A
  | l-subT-l-subT (S n) p z u B = refl

l-subt-l-subt n p z w (V x) = l-subV-l-subV n p z w x
l-subt-l-subt n p z w (app t u)
  rewrite l-subt-l-subt n p z w t
  | l-subt-l-subt n p z w u
  = refl

l-subV-l-subV O p z u O = refl
l-subV-l-subV (S n) p z u O = refl
l-subV-l-subV O p z u (S x) rewrite n-subt-wkt 0 (l-subV p z x) (l-subt p z u) = refl
l-subV-l-subV (S n) p z u (S x) rewrite l-subt-wkt (n + p) z (l-subV n u x)
  | l-subt-wkt n (l-subt p z u) (l-subV (S (n + p)) z x)
  | l-subV-l-subV n p z u x
   =
    refl

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

-- -- the substitution from Γ , Δ to Γ , A , Δ
-- liftₛ : ℕ → ℕ → Subp
-- liftₛ Γ O = wkₛ Γ
-- liftₛ Γ (S Δ) = V 0 :: liftₛ Γ Δ



  
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
  -- (Δw : Conw Δp)
    {σp}(σw : Subw Γ Δp σp){Ap}(Aw : Tyw Δp Ap){tp}
     (tw : Tmw Γ (Ap [ σp ]T) tp) →
     Subw Γ (Δp ▶p Ap) (tp :: σp)
  

wkT-wkₛ : ∀ {Γp} {Ap} (Aw : Tyw Γp Ap) → wkT Ap ≡ (Ap [ wkₛ ∣ Γp ∣ ]T)
wkt-wkₛ : ∀ {Γp} {Ap}{tp} (tw : Tmw Γp Ap tp) → wkt tp ≡ (tp [ wkₛ ∣ Γp ∣ ]t)

wkT-wkₛ (Uw Γp Γw) = refl
wkT-wkₛ (Πw Γw Aw Bw) rewrite wkt-wkₛ Aw | wkT-wkₛ Bw = {!refl!}
wkT-wkₛ (Elw Γw aw) rewrite wkt-wkₛ aw = refl

wkt-wkₛ tw = {!!}

-- Tmwₛ : ∀ {Γp}{tp}
Varwₛ : ∀ {Γp}{xp}{Ap}(xw : Varw Γp Ap xp)
  {Δp}{σp}(σw : Subw Δp Γp σp) →
  Tmw Δp (Ap [ σp ]T) (xp [ σp ]V )
-- Varwₛ {Γp}{xp}{Ap} xw {Δp}{σp}σw = {!!}
Varwₛ {.∙p} {xp} {Ap} () {Δp} {.nil} nilw
Varwₛ {.(Γp ▶p Ap)} {.0} {.(liftT 0 Ap)} (V0w Γp Γw Ap Aw₁) {Δp} {.(_ :: _)} (,sw σw Aw tw) = {!tw!}
Varwₛ {.(Γp ▶p Ap)} {.(S xp)} {.(liftT 0 Bp)} (VSw Γp Γw Ap Aw₁ Bp Bw xp xw) {Δp} {.(_ :: _)} (,sw σw Aw tw) =
  {!Varwₛ xw σw!}

-- wkTw is not enough : consider the Π case.
-- what we need : Γ , Δ ⊢ Bp, then Γ , A , wkC Δ ⊢ lift |Δ| Bp

-- liftC : ℕ → Conp → Conp
-- liftC p Δ = {!!}


infixl 5 _^^_
_^^_ : Conp → Conp → Conp

Γ ^^ ∙p = Γ
Γ ^^ (Δ ▶p x) =  (Γ ^^ Δ) ▶p x

liftTₛ= : ∀ {Γp} {Ap} (Aw : Tyw Γp Ap){Δp}{Bp} (Bw : Tyw (Γp ^^ Δp) Bp) →
  liftT ∣ Δp ∣ Bp ≡ (Bp [ liftₛ ∣ Γp ∣ ∣ Δp ∣ ]T)
lifttₛ= : ∀ {Γp} {Ap} (Aw : Tyw Γp Ap){Δp}{Bp}{tp} (tw : Tmw (Γp ^^ Δp) Bp tp) →
  liftt ∣ Δp ∣ tp ≡ (tp [ liftₛ ∣ Γp ∣ ∣ Δp ∣ ]t)
  -- pb: what if Γp = ∙ ??
liftVₛ= : ∀ {Γp} {Ap} (Aw : Tyw Γp Ap){Δp}{Bp}{xp} (xw : Varw (Γp ^^ Δp) Bp xp) →
  V (liftV ∣ Δp ∣ xp) ≡ (xp [ liftₛ ∣ Γp ∣ (S ∣ Δp ∣) ]V)

liftTₛ= {Γp} {Ep} Ew {Δp} {.Up} (Uw .(Γp ^^ Δp) Γw) = refl
liftTₛ= {Γp} {Ep} Ew {Δp} {.(ΠΠp (Elp _) _)} (Πw Γw Aw Bw)
  rewrite liftTₛ= Ew Bw | lifttₛ= Ew Aw
  = {!refl!}
liftTₛ= {Γp} {Ep} Ew {Δp} {.(Elp _)} (Elw Γw aw) = {!!}

lifttₛ= {Γp} {Ep} Ew {Δp}{Ap}{tp} tw = {!tw!}

liftVₛ= {Γp} {Ep} Ew {∙p} {Ap}{xp} xw = {!!}
-- liftVₛ= {.(Γp ▶p Ap)} {Ep} Ew {∙p} {.(liftT 0 Ap)} {.0} (V0w Γp Γw Ap Aw) = refl
-- liftVₛ= {.(Γp ▶p Ap)} {Ep} Ew {∙p} {.(liftT 0 Bp)} {.(S xp)} (VSw Γp Γw Ap Aw Bp Bw xp xw) =
--   {!liftVₛ= !}
liftVₛ= {Γp} {Ep} Ew {Δp ▶p x} {.(liftT 0 x)} {.0} (V0w .(Γp ^^ Δp) Γw .x Aw) = {!j!}
liftVₛ= {Γp} {Ep} Ew {Δp ▶p x} {.(liftT 0 Bp)} {.(S xp)} (VSw .(Γp ^^ Δp) Γw .x Aw Bp Bw xp xw) = {!!}

-- lifttₛ= {Γp} {Ep} Ew {Δp}{Ap}{tp} tw = {!tw!}

-- liftVₛ= {Γp} {Ep} Ew {Δp}{Ap}{xp} xw = {!!}

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
   
   HoTT.transport (λ x → Tmw _ x _) (! (lift-subT ∣ Δp ∣ u Bp ))
   (appw _ (wkCw' Aw Δp Γw) _ (lifttw Aw Δp aw) _ (liftTw Aw (Δp ▶p Elp ap) Bw)
   (liftt ∣ Δp ∣ t) (lifttw Aw Δp tw) (liftt ∣ Δp ∣ u) (lifttw Aw Δp uw)
   )
   

-- liftVw Aw ∙p xw = VSw _ {!!} _ Aw _ {!!} _ xw
liftVw {Ap = Bp} Bw ∙p (V0w Γp Γw Ap Aw) = VSw (Γp ▶p Ap) (▶w Γw Aw) Bp Bw (wkT Ap)
   (liftTw Aw ∙p Aw) 0 (V0w Γp Γw Ap Aw)
liftVw Aw ∙p (VSw Γp Γw Ap Aw' Bp Bw xp xw) =
  VSw _ (▶w Γw Aw') _ Aw _ (liftTw Aw' ∙p Bw) _ (VSw Γp Γw Ap Aw' Bp Bw xp xw)

liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (V0w .(_ ^^ Δp) Γw .Bp Aw) =
  HoTT.transport (λ x → Varw (((Γp ▶p T) ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Bp) x 0) (! (comm-liftT ∣ Δp ∣ Bp))
     (V0w ((Γp ▶p T) ^^ wkC Δp) (wkCw' Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Aw))
liftVw {Γp = Γp}{Ap = T}Tw (Δp ▶p Bp) (VSw .(_ ^^ Δp) Γw .Bp Bw Ap Aw xp xw) =
  HoTT.transport (λ x → Varw _ x _)  (! (comm-liftT ∣ Δp ∣ Ap))
   (VSw ((Γp ▶p T) ^^ wkC Δp) (wkCw' Tw Δp Γw) (liftT ∣ Δp ∣ Bp) (liftTw Tw Δp Bw)
   _ (liftTw Tw Δp Aw) _ (liftVw Tw Δp xw))
   

wkTw : ∀ {Γp}{Ap}(Aw : Tyw Γp Ap){Bp}(Bw : Tyw Γp Bp) → Tyw (Γp ▶p Ap) (wkT Bp)
wkTw Aw Bw = liftTw Aw ∙p Bw 

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


