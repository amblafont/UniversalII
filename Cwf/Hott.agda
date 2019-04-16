{-# OPTIONS  --rewriting  #-}
{-

Excerpt from the HoTT Lib

We don't use univalence and state uip instead (to prove that funext, here named λ=, is an equivalence)

-}
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_ ; refl to idp)

uip : ∀ {i} {A : Set i} {x y : A} (p q : x == y) → p == q
uip idp idp = idp

open import Level 


-- Base.agda
open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

open import Data.Nat renaming (suc to S)

Type : (i : ULevel) → Set (lsucc i)
Type i = Set i

Type₀ = Type lzero

{-
There is no built-in or standard way to coerce an ambiguous term to a given type
(like [u : A] in ML), the symbol [:] is reserved, and the Unicode [∶] is really
a bad idea.
So we’re using the symbol [_:>_], which has the advantage that it can micmic
Coq’s [u = v :> A].
-}

of-type : ∀ {i} (A : Type i) (u : A) → A
of-type A u = u

infix 40 of-type
syntax of-type A u =  u :> A

{- Paulin-Mohring J rule

At the time I’m writing this (July 2013), the identity type is somehow broken in
Agda dev, it behaves more or less as the Martin-Löf identity type instead of
behaving like the Paulin-Mohring identity type.
So here is the Paulin-Mohring J rule -}

J : ∀ {i j} {A : Type i} {a : A} (B : (a' : A) (p : a == a') → Type j) (d : B a idp)
  {a' : A} (p : a == a') → B a' p
J B d idp = d

{- Rewriting

This is a new pragma added to Agda to help create higher inductive types.
-}

infix 30 _↦_
postulate  -- HIT
  _↦_ : ∀ {i} {A : Type i} → A → A → Type i

{-# BUILTIN REWRITE _↦_ #-}

{- Dependent paths

The notion of dependent path is a very important notion.
If you have a dependent type [B] over [A], a path [p : x == y] in [A] and two
points [u : B x] and [v : B y], there is a type [u == v [ B ↓ p ]] of paths from
[u] to [v] lying over the path [p].
By definition, if [p] is a constant path, then [u == v [ B ↓ p ]] is just an
ordinary path in the fiber.
-}

PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
PathOver B idp u v = (u == v)

infix 30 PathOver
syntax PathOver B p u v =
  u == v [ B ↓ p ]

{- Ap, coe and transport

Given two fibrations over a type [A], a fiberwise map between the two fibrations
can be applied to any dependent path in the first fibration ([ap↓]).
As a special case, when [A] is [Unit], we find the familiar [ap] ([ap] is
defined in terms of [ap↓] because it shouldn’t change anything for the user
and this is helpful in some rare cases)
-}

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f idp = idp

ap↓ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (g : {a : A} → B a → C a) {x y : A} {p : x == y}
  {u : B x} {v : B y}
  → (u == v [ B ↓ p ] → g u == g v [ C ↓ p ])
ap↓ g {p = idp} p = ap g p



{-
[apd↓] is defined in lib.PathOver. Unlike [ap↓] and [ap], [apd] is not
definitionally a special case of [apd↓]
-}

apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f idp = idp


{-
An equality between types gives two maps back and forth
-}

coe : ∀ {i} {A B : Type i} (p : A == B) → A → B
coe idp x = x

coe! : ∀ {i} {A B : Type i} (p : A == B) → B → A
coe! idp x = x

{-
The operations of transport forward and backward are defined in terms of [ap]
and [coe], because this is more convenient in practice.
-}

transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B x → B y)
transport B p = coe (ap B p)

transport! : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B y → B x)
transport! B p = coe! (ap B p)

{- Π-types

Shorter notation for Π-types.
-}

Π : ∀ {i j} (A : Type i) (P : A → Type j) → Type (lmax i j)
Π A P = (x : A) → P x

{- Σ-types

Σ-types are defined as a record so that we have definitional η.
-}

infixr 60 _,_

record Σ {i j} (A : Type i) (B : A → Type j) : Type (lmax i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

pair= : ∀ {i j} {A : Type i} {B : A → Type j}
  {a a' : A} (p : a == a') {b : B a} {b' : B a'}
  (q : b == b' [ B ↓ p ])
  → (a , b) == (a' , b')
pair= idp q = ap (_ ,_) q

pair×= : ∀ {i j} {A : Type i} {B : Type j}
  {a a' : A} (p : a == a') {b b' : B} (q : b == b')
  → (a , b) == (a' , b')
pair×= idp q = pair= idp q

{- Equational reasoning

Equational reasoning is a way to write readable chains of equalities.
The idea is that you can write the following:

  t : a == e
  t = a =⟨ p ⟩
      b =⟨ q ⟩
      c =⟨ r ⟩
      d =⟨ s ⟩
      e ∎

where [p] is a path from [a] to [b], [q] is a path from [b] to [c], and so on.

You often have to apply some equality in some context, for instance [p] could be
[ap ctx thm] where [thm] is the interesting theorem used to prove that [a] is
equal to [b], and [ctx] is the context.
In such cases, you can use instead [thm |in-ctx ctx]. The advantage is that
[ctx] is usually boring whereas the first word of [thm] is the most interesting
part.

_=⟨_⟩ is not definitionally the same thing as concatenation of paths _∙_ because
we haven’t defined concatenation of paths yet, and also you probably shouldn’t
reason on paths constructed with equational reasoning.
If you do want to reason on paths constructed with equational reasoning, check
out lib.types.PathSeq instead.
-}

infixr 10 _=⟨_⟩_
infix  15 _=∎

_=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x == y → y == z → x == z
_ =⟨ idp ⟩ idp = idp

_=∎ : ∀ {i} {A : Type i} (x : A) → x == x
_ =∎ = idp

infixl 40 ap
syntax ap f p = p |in-ctx f


{- Various basic functions and function operations

The identity function on a type [A] is [idf A] and the constant function at some
point [b] is [cst b].

Composition of functions ([_∘_]) can handle dependent functions.
-}

idf : ∀ {i} (A : Type i) → (A → A)
idf A = λ x → x

infixr 80 _∘_

_∘_ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → (B a → Type k)}
  → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
g ∘ f = λ x → g (f x)

-- Application
infixr 0 _$_
_$_ : ∀ {i j} {A : Type i} {B : A → Type j} → (∀ x → B x) → (∀ x → B x)
f $ x = f x

uncurry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
  → (∀ x y → C x y) → (∀ s → C (fst s) (snd s))
uncurry f (x , y) = f x y

{- Truncation levels

The type of truncation levels is isomorphic to the type of natural numbers but
"starts at -2".
-}

data TLevel : Type₀ where
  ⟨-2⟩ : TLevel
  S : (n : TLevel) → TLevel

ℕ₋₂ = TLevel

⟨_⟩₋₂ : ℕ → ℕ₋₂
⟨ 0 ⟩₋₂ = ⟨-2⟩
⟨ S n ⟩₋₂ = S ⟨ n ⟩₋₂



-- PathGroupoid.agda
module _ {i} {A : Type i} where

  {- Concatenation of paths

  There are two different definitions of concatenation of paths, [_∙_] and [_∙'_],
  with different definitionnal behaviour. Maybe we should have only one but it’s
  sometimes useful to have both (in particular in lib.types.Paths).
  -}

  infixr 80 _∙_ _∙'_

  _∙_ : {x y z : A}
    → (x == y → y == z → x == z)
  idp ∙ q = q

  _∙'_ : {x y z : A}
    → (x == y → y == z → x == z)
  q ∙' idp = q

  ∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc idp _ _ = idp

  ∙-unit-r : {x y : A} (q : x == y) → q ∙ idp == q
  ∙-unit-r idp = idp

  {- Reversal of paths -}

  ! : {x y : A} → (x == y → y == x)
  ! idp = idp

  !-inv-l : {x y : A} (p : x == y) → (! p) ∙ p == idp
  !-inv-l idp = idp


  {- Horizontal compositions -}

  -- infixr 80 _∙2_ _∙'2_
  infixr 80 _∙2_ 

  _∙2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _∙2_ {p = idp} idp β = β

{-
Sometimes we need to restart a new section in order to have everything in the
previous one generalized.
-}
module _ {i} {A : Type i} where
  {- Whisker and horizontal composition for Eckmann-Hilton argument -}

  infixl 80 _∙ₗ_

  _∙ₗ_ : {x y z : A} {q q' : y == z} (p : x == y) (β : q == q')
    → p ∙ q == p ∙ q'
  _∙ₗ_ {q = q} {q' = q'} idp β = β


module _ {i} {A : Type i} where

  anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
    → (q ∙ p == r ∙ p → q == r)
  anti-whisker-right idp {q} {r} h =
    ! (∙-unit-r q) ∙ (h ∙ ∙-unit-r r)

  anti-whisker-left : {x y z : A} (p : x == y) {q r : y == z}
    → (p ∙ q == p ∙ r → q == r)
  anti-whisker-left idp h = h

{- Dependent stuff -}
module _ {i j} {A : Type i} {B : A → Type j} where
  {- Dependent concatenation -}

  -- infixr 80 _∙ᵈ_ _∙'ᵈ_ _◃_ _▹_ _!◃_ _▹!_
  infixr 80 _∙ᵈ_

  _∙ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙ p') ])
  _∙ᵈ_ {p = idp} {p' = idp} q r = q ∙ r





-- PathFunctor.agda (depends on PathGroupoid)

{- Nondependent stuff -}
module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-! : {x y : A} (p : x == y)
    → ap f (! p) == ! (ap f p)
  ap-! idp = idp

  ap-∙ : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙ q) == ap f p ∙ ap f q
  ap-∙ idp q = idp

{- Fuse and unfuse -}
∘-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap g (ap f p) == ap (g ∘ f) p
∘-ap f g idp = idp

ap-∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
ap-∘ f g idp = idp

ap-idf : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (idf A) p == p
ap-idf idp = idp

{- for functions with two arguments -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) where

  ap2 : {x y : A} {w z : B}
    → (x == y) → (w == z) → f x w == f y z
  ap2 idp idp = idp

module _ {i₀ i₁ i₂ i₃ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂} {A₃ : Type i₃}
  {B : Type j} (f : A₀ → A₁ → A₂ → A₃ → B) where

  ap4 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂} {x₃ y₃ : A₃}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → (x₃ == y₃) → f x₀ x₁ x₂ x₃ == f y₀ y₁ y₂ y₃
  ap4 idp idp idp idp = idp

-- NType.agda
module _ {i} where

  {- Definition of contractible types and truncation levels -}

  -- We define `has-level' as a record, so that it does not unfold when
  -- applied to (S n), in order for instance arguments to work correctly
  -- (idea by Dan Licata)
  record has-level (n : ℕ₋₂) (A : Type i) : Type i

  has-level-aux : ℕ₋₂ → (Type i → Type i)
  has-level-aux ⟨-2⟩ A = Σ A (λ x → ((y : A) → x == y))
  has-level-aux (S n) A = (x y : A) → has-level n (x == y)

  record has-level n A where
    -- Agda notices that the record is recursive, so we need to specify that we want eta-equality
    inductive
    eta-equality
    constructor has-level-in
    field
      has-level-apply : has-level-aux n A
  open has-level public

  instance
    has-level-apply-instance : {A : Type i} {n : ℕ₋₂} {x y : A} {{p : has-level (S n) A}} → has-level n (x == y)
    has-level-apply-instance {x = x} {y} {{p}} = has-level-apply p x y

  is-contr = has-level ⟨-2⟩
  is-prop = has-level (S ⟨-2⟩)
  is-set  = has-level (S (S ⟨-2⟩))

  contr-center : {A : Type i} (p : is-contr A) → A
  contr-center p = fst (has-level-apply p)

  contr-path : {A : Type i} (p : is-contr A) (y : A) → contr-center p == y
  contr-path p y = snd (has-level-apply p) y

  prop-path : {A : Type i} (p : is-prop A) (x y : A) → x == y
  prop-path p x y = contr-center (has-level-apply p x y)

  {- To be a mere proposition, it is sufficient that all points are equal -}

  has-all-paths : Type i → Type i
  has-all-paths A = (x y : A) → x == y

  abstract
    all-paths-is-prop : {A : Type i} → (has-all-paths A → is-prop A)
    all-paths-is-prop {A} c = has-level-in (λ x y → has-level-in (c x y , canon-path)) where

      canon-path : {x y : A} (p : x == y) → c x y == p
      canon-path {.y} {y} idp =
        c y y               =⟨ lemma (! (c y y)) ⟩
        (! (c y y)) ∙ c y y =⟨ !-inv-l (c y y) ⟩
        idp =∎  where

        lemma : {x y : A} (p : x == y) → c x y == p ∙ c y y
        lemma idp = idp

  {- Truncation levels are cumulative -}
  raise-level : {A : Type i} (n : ℕ₋₂)
    → (has-level n A → has-level (S n) A)
  raise-level ⟨-2⟩ q =
    all-paths-is-prop (λ x y → ! (contr-path q x) ∙ contr-path q y)
  raise-level (S n) q =
    has-level-in (λ x y → raise-level n (has-level-apply q x y))

  {- Relationships between levels -}

  module _ {A : Type i} where
    abstract
      prop-has-all-paths : {{_ : is-prop A}} → has-all-paths A
      prop-has-all-paths {{c}} x y = prop-path c x y

    {- The type of paths to a fixed point is contractible -}
    instance
      pathto-is-contr : (x : A) → is-contr (Σ A (λ t → t == x))
      pathto-is-contr x = has-level-in ((x , idp) , pathto-unique-path) where
        pathto-unique-path : {u : A} (pp : Σ A (λ t → t == u)) → (u , idp) == pp
        pathto-unique-path (u , idp) = idp


-- Function.agda

{- Homotopy fibers -}

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where
  {- Note that [is-inj] is not a mere proposition. -}
  is-inj : Type (lmax i j)
  is-inj = (a₁ a₂ : A) → f a₁ == f a₂ → a₁ == a₂



-- Equivalence.agda

{-
We use the half-adjoint definition of equivalences (but this fact should be
invisible to the user of the library). The constructor of the type of
equivalences is [equiv], it takes two maps and the two proofs that the composites
are equal: [equiv to from to-from from-to]

The type of equivalences between two types [A] and [B] can be written either
[A ≃ B] or [Equiv A B].

Given an equivalence [e] : [A ≃ B], you can extract the two maps as follows:
[–> e] : [A → B] and [<– e] : [B → A] (the dash is an en dash)
The proofs that the composites are the identities are [<–-inv-l] and [<–-inv-r].

The identity equivalence on [A] is [ide A], the composition of two equivalences
is [_∘e_] (function composition order) and the inverse of an equivalence is [_⁻¹]
-}

{- These lemmas are here because lib.Path is not available at this point.
   Otherwise they are just combinations of [↓-='-out] and [apd]. -}

private
  htpy-natural : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {f g : A → B}
    (p : ∀ x → (f x == g x)) (q : x == y) → ap f q ∙ p y == p x ∙ ap g q
  htpy-natural p idp = ! (∙-unit-r _)

  htpy-natural-app=idf : ∀ {i} {A : Type i} {f : A → A}
    (p : ∀ (x : A) → f x == x) → (∀ x → ap f (p x) == p (f x))
  htpy-natural-app=idf {f = f} p x = anti-whisker-right (p x) $
    htpy-natural p (p x) ∙ ap (p (f x) ∙_) (ap-idf (p x))

module _ {i} {j} {A : Type i} {B : Type j} where

  record is-equiv (f : A → B) : Type (lmax i j)
    where
    field
      g : B → A
      f-g : (b : B) → f (g b) == b
      g-f : (a : A) → g (f a) == a
      adj : (a : A) → ap f (g-f a) == f-g (f a)
    abstract
      adj' : (b : B) → ap g (f-g b) == g-f (g b)
      adj' b = anti-whisker-left (ap g (f-g (f (g b)))) $ ! $
        ap g (f-g (f (g b))) ∙ g-f (g b)
          =⟨ ! $ htpy-natural-app=idf f-g b |in-ctx (λ p → ap g p ∙ g-f (g b)) ⟩
        ap g (ap (f ∘ g) (f-g b)) ∙ g-f (g b)
          =⟨ ! $ ap-∘ g (f ∘ g) (f-g b) |in-ctx (λ p → p ∙ g-f (g b)) ⟩
        ap (g ∘ f ∘ g) (f-g b) ∙ g-f (g b)
          =⟨ htpy-natural (g-f ∘ g) (f-g b) ⟩
        g-f (g (f (g b))) ∙ ap g (f-g b)
          =⟨ ! $ htpy-natural-app=idf g-f (g b) |in-ctx (λ p → p ∙ ap g (f-g b)) ⟩
        ap (g ∘ f) (g-f (g b)) ∙ ap g (f-g b)
          =⟨ ap-∘ g f (g-f (g b)) |in-ctx (λ p → p ∙ ap g (f-g b)) ⟩
        ap g (ap f (g-f (g b))) ∙ ap g (f-g b)
          =⟨ adj (g b) |in-ctx (λ p → ap g p ∙ ap g (f-g b)) ⟩
        ap g (f-g (f (g b))) ∙ ap g (f-g b)
          =∎

  {-
  In order to prove that something is an equivalence, you have to give an inverse
  and a proof that it’s an inverse (you don’t need the adj part).
  [is-eq] is a very, very bad name.
  -}
  is-eq : (f : A → B)
    (g : B → A) (f-g : (b : B) → f (g b) == b)
    (g-f : (a : A) → g (f a) == a) → is-equiv f
  is-eq f g f-g g-f =
   record {g = g; f-g = f-g'; g-f = g-f; adj = adj} where
    abstract
     f-g' : (b : B) → f (g b) == b
     f-g' b = ! (ap (f ∘ g) (f-g b)) ∙ ap f (g-f (g b)) ∙ f-g b

     adj : (a : A) → ap f (g-f a) == f-g' (f a)
     adj a =
      ap f (g-f a)
        =⟨ ! (!-inv-l (ap (f ∘ g) (f-g (f a)))) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
      (! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f a)
        =⟨ ∙-assoc (! (ap (f ∘ g) (f-g (f a)))) (ap (f ∘ g) (f-g (f a))) _ ⟩
      ! (ap (f ∘ g) (f-g (f a))) ∙ ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
        =⟨ lemma |in-ctx (λ q → ! (ap (f ∘ g) (f-g (f a))) ∙ q) ⟩
      ! (ap (f ∘ g) (f-g (f a))) ∙ ap f (g-f (g (f a))) ∙ f-g (f a) =∎
      where
      lemma : ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
           == ap f (g-f (g (f a))) ∙ f-g (f a)
      lemma =
        ap (f ∘ g) (f-g (f a)) ∙ ap f (g-f a)
          =⟨ htpy-natural-app=idf f-g (f a) |in-ctx (λ q → q ∙ ap f (g-f a)) ⟩
        f-g (f (g (f a))) ∙ ap f (g-f a)
          =⟨ ! (ap-idf (ap f (g-f a))) |in-ctx (λ q → f-g (f (g (f a))) ∙ q) ⟩
        f-g (f (g (f a))) ∙ ap (idf B) (ap f (g-f a))
          =⟨ ! (htpy-natural f-g (ap f (g-f a))) ⟩
        ap (f ∘ g) (ap f (g-f a)) ∙ f-g (f a)
          =⟨ ap-∘ f g (ap f (g-f a)) |in-ctx (λ q → q ∙ f-g (f a)) ⟩
        ap f (ap g (ap f (g-f a))) ∙ f-g (f a)
          =⟨ ∘-ap g f (g-f a) ∙ htpy-natural-app=idf g-f a
             |in-ctx (λ q → ap f q ∙ f-g (f a)) ⟩
        ap f (g-f (g (f a))) ∙ f-g (f a) =∎

infix 30 _≃_

_≃_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A ≃ B = Σ (A → B) is-equiv

Equiv = _≃_

module _ {i} {j} {A : Type i} {B : Type j} where

  equiv : (f : A → B) (g : B → A) (f-g : (b : B) → f (g b) == b)
          (g-f : (a : A) → g (f a) == a) → A ≃ B
  equiv f g f-g g-f = (f , is-eq f g f-g g-f)

  –> : (e : A ≃ B) → (A → B)
  –> e = fst e

  <– : (e : A ≃ B) → (B → A)
  <– e = is-equiv.g (snd e)

  <–-inv-l : (e : A ≃ B) (a : A)
    → (<– e (–> e a) == a)
  <–-inv-l e a = is-equiv.g-f (snd e) a

  <–-inv-r : (e : A ≃ B) (b : B)
    → (–> e (<– e b) == b)
  <–-inv-r e b = is-equiv.f-g (snd e) b

  <–-inv-adj : (e : A ≃ B) (a : A)
    → ap (–> e) (<–-inv-l e a) == <–-inv-r e (–> e a)
  <–-inv-adj e a = is-equiv.adj (snd e) a

  -- Equivalences are "injective"
  –>-is-inj : (e : A ≃ B) → is-inj (–> e)
  –>-is-inj e x y p = ! (<–-inv-l e x) ∙ ap (<– e) p ∙ <–-inv-l e y

  equiv-is-inj : {f : A → B} → is-equiv f → is-inj f
  equiv-is-inj ise = –>-is-inj (_ , ise)

infixr 80 _∘e_
-- infixr 80 _∘ise_

_∘e_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → B ≃ C → A ≃ B → A ≃ C
e1 ∘e e2 = (–> e1 ∘ –> e2) , record {g = (<– e2 ∘ <– e1); M} where
  module M where
    f = –> e1 ∘ –> e2
    g = <– e2 ∘ <– e1
    abstract
      f-g : ∀ c → f (g c) == c
      f-g c = ap (–> e1) (<–-inv-r e2 (<– e1 c)) ∙ <–-inv-r e1 c
      g-f : ∀ a → g (f a) == a
      g-f a = ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a
      adj : ∀ a → ap f (g-f a) == f-g (f a)
      adj a =
        ap (–> e1 ∘ –> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a)
            =⟨ ap-∘ (–> e1) (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a) ⟩
        ap (–> e1) (ap (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-l e2 a))
            =⟨ ap-∙ (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a))) (<–-inv-l e2 a)  |in-ctx ap (–> e1) ⟩
        ap (–> e1) (ap (–> e2) (ap (<– e2) (<–-inv-l e1 (–> e2 a))) ∙ ap (–> e2) (<–-inv-l e2 a))
            =⟨ ! (ap-∘ (–> e2) (<– e2) (<–-inv-l e1 (–> e2 a))) ∙2 <–-inv-adj e2 a |in-ctx ap (–> e1) ⟩
        ap (–> e1) (ap (–> e2 ∘ <– e2) (<–-inv-l e1 (–> e2 a)) ∙ <–-inv-r e2 (–> e2 a))
            =⟨ htpy-natural (<–-inv-r e2) (<–-inv-l e1 (–> e2 a))    |in-ctx ap (–> e1) ⟩
        ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a)) ∙ ap (λ z → z) (<–-inv-l e1 (–> e2 a)))
            =⟨ <–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a)) ∙ₗ ap-idf (<–-inv-l e1 (–> e2 a)) |in-ctx ap (–> e1) ⟩
        ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a)) ∙ <–-inv-l e1 (–> e2 a))
            =⟨ ap-∙ (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) (<–-inv-l e1 (–> e2 a)) ⟩
        ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) ∙ ap (–> e1) (<–-inv-l e1 (–> e2 a))
            =⟨  ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) ∙ₗ (<–-inv-adj e1 (–> e2 a)) ⟩
        ap (–> e1) (<–-inv-r e2 (<– e1 ((–> e1 ∘ –> e2) a))) ∙ <–-inv-r e1 ((–> e1 ∘ –> e2) a)
            =∎


is-equiv-inverse : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (f-is-equiv : is-equiv f) → is-equiv (is-equiv.g f-is-equiv)
is-equiv-inverse {f = g} ise = record { g = _ ; M } where
  module M where
    f = is-equiv.g ise
    abstract
      f-g : ∀ b → f (g b) == b
      f-g = is-equiv.g-f ise
      g-f : ∀ a → g (f a) == a
      g-f = is-equiv.f-g ise
      adj : ∀ a → ap f (g-f a) == f-g (f a)
      adj = is-equiv.adj' ise

infix 120 _⁻¹
_⁻¹ : ∀ {i j} {A : Type i} {B : Type j} → (A ≃ B) → (B ≃ A)
(_ , ise) ⁻¹ = (is-equiv.g ise , is-equiv-inverse ise)


{- An equivalence induces an equivalence on the path spaces -}
module _ {i j} {A : Type i} {B : Type j} where

  private
    abstract
      left-inverse : (e : A ≃ B) {x y : A} (p : x == y)
        → –>-is-inj e _ _ (ap (–> e) p) == p
      left-inverse e idp = !-inv-l (<–-inv-l e _)

      right-inverse : (e : A ≃ B) {x y : A} (p : –> e x == –> e y)
        → ap (–> e) (–>-is-inj e _ _ p) == p
      right-inverse e {x} {y} p =
        ap f (! (g-f x) ∙ ap g p ∙ (g-f y))
          =⟨ ap-∙ f (! (g-f x)) (ap g p ∙ (g-f y)) ⟩
        ap f (! (g-f x)) ∙ ap f (ap g p ∙ (g-f y))
          =⟨ ap-∙ f (ap g p) (g-f y) |in-ctx (λ q →  ap f (! (g-f x)) ∙ q) ⟩
        ap f (! (g-f x)) ∙ ap f (ap g p) ∙ ap f (g-f y)
          =⟨ ∘-ap f g p |in-ctx (λ q → ap f (! (g-f x)) ∙ q ∙ ap f (g-f y)) ⟩
        ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ ap f (g-f y)
          =⟨ adj y |in-ctx (λ q →  ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ q) ⟩
        ap f (! (g-f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
          =⟨ ap-! f (g-f x) |in-ctx (λ q → q ∙ ap (f ∘ g) p ∙ (f-g (f y))) ⟩
        ! (ap f (g-f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
          =⟨ adj x |in-ctx (λ q →  ! q ∙ ap (f ∘ g) p ∙ (f-g (f y))) ⟩
        ! (f-g (f x)) ∙ ap (f ∘ g) p ∙ (f-g (f y))
          =⟨ htpy-natural f-g p |in-ctx (λ q →  ! (f-g (f x)) ∙ q) ⟩
        ! (f-g (f x)) ∙ (f-g (f x)) ∙ ap (idf B) p
          =⟨ ! (∙-assoc (! (f-g (f x))) (f-g (f x)) (ap (idf B) p))
             ∙ ap (λ q → q ∙ ap (idf B) p) (!-inv-l (f-g (f x))) ∙ ap-idf p ⟩
        p =∎
        where f : A → B
              f = fst e

              open is-equiv (snd e)

  ap-is-equiv : {f : A → B} → is-equiv f
    → (x y : A) → is-equiv (ap f :> (x == y → f x == f y))
  ap-is-equiv {f} e x y =
    is-eq (ap f) (equiv-is-inj e _ _) (right-inverse (_ , e)) (left-inverse (_ , e))

  ap-equiv : (e : A ≃ B) (x y : A) → (x == y) ≃ (–> e x == –> e y)
  ap-equiv e x y = _ , ap-is-equiv (snd e) x y

{- Equivalent types have the same truncation level -}
abstract
  equiv-preserves-level : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} (e : A ≃ B)
    {{_ : has-level n A}} → has-level n B
  equiv-preserves-level {n = ⟨-2⟩} e {{p}} =
    has-level-in (–> e (contr-center p) , (λ y → ap (–> e) (contr-path p _) ∙ <–-inv-r e y))
  equiv-preserves-level {n = S n} e {{c}} = has-level-in (λ x y →
    equiv-preserves-level (ap-equiv (e ⁻¹) x y ⁻¹) {{has-level-apply c (<– e x) (<– e y)}})

module _ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} where
  Σ-assoc : Σ (Σ A B) (uncurry C) ≃ Σ A (λ a → Σ (B a) (C a))
  Σ-assoc = equiv (λ {((a , b) , c) → (a , (b , c))})
                  (λ {(a , (b , c)) → ((a , b) , c)}) (λ _ → idp) (λ _ → idp)

-- PathOver.agda (depends on Equivalence.agda)

-- Dependent paths over [ap f p]
module _ {i j k} {A : Type i} {B : Type j} (C : B → Type k) (f : A → B) where

  ↓-ap-in : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → u == v [ C ∘ f ↓ p ]
    → u == v [ C ↓ ap f p ]
  ↓-ap-in {p = idp} idp = idp

-- Mediating dependent paths with the transport version

module _ {i j} {A : Type i} where

  from-transp : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    → (transport B p u == v)
    → (u == v [ B ↓ p ])
  from-transp B idp idp = idp

  to-transp : {B : A → Type j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → (transport B p u == v)
  to-transp {p = idp} idp = idp

  to-transp-β : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    (q : transport B p u == v)
    → to-transp (from-transp B p q) == q
  to-transp-β B idp idp = idp

  to-transp-η : {B : A → Type j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    (q : u == v [ B ↓ p ])
    → from-transp B p (to-transp q) == q
  to-transp-η {p = idp} idp = idp

  to-transp-equiv : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'} → (u == v [ B ↓ p ]) ≃ (transport B p u == v)
  to-transp-equiv B p =
    equiv to-transp (from-transp B p) (to-transp-β B p) (to-transp-η)

  from-transp! : (B : A → Type j)
    {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    → (u == transport! B p v)
    → (u == v [ B ↓ p ])
  from-transp! B idp idp = idp

  to-transp! : {B : A → Type j}
    {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → (u == transport! B p v)
  to-transp! {p = idp} idp = idp

  to-transp!-β : (B : A → Type j)
    {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    (q : u == transport! B p v)
    → to-transp! (from-transp! B p q) == q
  to-transp!-β B idp idp = idp

  to-transp!-η : {B : A → Type j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    (q : u == v [ B ↓ p ])
    → from-transp! B p (to-transp! q) == q
  to-transp!-η {p = idp} idp = idp


  to-transp!-equiv : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'} → (u == v [ B ↓ p ]) ≃ (u == transport! B p v)
  to-transp!-equiv B p =
    equiv to-transp! (from-transp! B p) (to-transp!-β B p) (to-transp!-η)


transp-↓ : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
  (p : a₁ == a₂) (y : P a₂) → transport P (! p) y == y [ P ↓ p ]
transp-↓ _ idp _ = idp

transp-ap-↓ : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k) (h : A → B)
  {a₁ a₂ : A} (p : a₁ == a₂) (y : P (h a₂))
  → transport P (! (ap h p)) y == y [ P ∘ h ↓ p ]
transp-ap-↓ _ _ idp _ = idp


-- Sigma.agda (depends on Equivalence and PathOver)

module _ {i j} {A : Type i} {B : A → Type j} where

  pair : (a : A) (b : B a) → Σ A B
  pair a b = (a , b)

  -- pair= has already been defined

  fst= : {ab a'b' : Σ A B} (p : ab == a'b') → (fst ab == fst a'b')
  fst= = ap fst

  snd= : {ab a'b' : Σ A B} (p : ab == a'b')
    → (snd ab == snd a'b' [ B ↓ fst= p ])
  snd= {._} {_} idp = idp

  fst=-β : {a a' : A} (p : a == a')
    {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ])
    → fst= (pair= p q) == p
  fst=-β idp idp = idp

  snd=-β : {a a' : A} (p : a == a')
    {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ])
    → snd= (pair= p q) == q [ (λ v → b == b' [ B ↓ v ]) ↓ fst=-β p q ]
  snd=-β idp idp = idp

  pair=-η : {ab a'b' : Σ A B} (p : ab == a'b')
    → p == pair= (fst= p) (snd= p)
  pair=-η {._} {_} idp = idp

module _ {i j} {A : Type i} {B : A → Type j} where

  =Σ : (x y : Σ A B) → Type (lmax i j)
  =Σ (a , b) (a' , b') = Σ (a == a') (λ p → b == b' [ B ↓ p ])

  =Σ-econv : (x y : Σ A B) →  (=Σ x y) ≃ (x == y)
  =Σ-econv x y =
    equiv (λ pq → pair= (fst pq) (snd pq)) (λ p → fst= p , snd= p)
          (λ p → ! (pair=-η p))
          (λ pq → pair= (fst=-β (fst pq) (snd pq)) (snd=-β (fst pq) (snd pq)))


instance
  Σ-level : ∀ {i j} {n : ℕ₋₂} {A : Type i} {P : A → Type j}
    → has-level n A → ((x : A) → has-level n (P x))
      → has-level n (Σ A P)
  Σ-level {n = ⟨-2⟩} p q = has-level-in ((contr-center p , (contr-center (q (contr-center p)))) , lemma)
    where abstract lemma = λ y → pair= (contr-path p _) (from-transp! _ _ (contr-path (q _) _))
  Σ-level {n = S n} p q = has-level-in lemma where
    abstract
      lemma = λ x y → equiv-preserves-level (=Σ-econv x y)
        {{Σ-level (has-level-apply p _ _) (λ _ →
          equiv-preserves-level ((to-transp-equiv _ _)⁻¹) {{has-level-apply (q _) _ _}})}}

-- Equivalences in a Σ-type

Σ-fmap-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k)
  → (f : A → B) → (Σ A (P ∘ f) → Σ B P)
Σ-fmap-l P f (a , r) = (f a , r)

Σ-isemap-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k) {h : A → B}
  → is-equiv h → is-equiv (Σ-fmap-l P h)
Σ-isemap-l {A = A} {B = B} P {h} e = is-eq _ g f-g g-f
  where f = Σ-fmap-l P h

        g : Σ B P → Σ A (P ∘ h)
        g (b , s) = (is-equiv.g e b , transport P (! (is-equiv.f-g e b)) s)

        f-g : ∀ y → f (g y) == y
        f-g (b , s) = pair= (is-equiv.f-g e b) (transp-↓ P (is-equiv.f-g e b) s)

        g-f : ∀ x → g (f x) == x
        g-f (a , r) =
          pair= (is-equiv.g-f e a)
                (transport (λ q → transport P (! q) r == r [ P ∘ h ↓ is-equiv.g-f e a ])
                           (is-equiv.adj e a)
                           (transp-ap-↓ P h (is-equiv.g-f e a) r))

Σ-emap-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k)
  → (e : A ≃ B) → (Σ A (P ∘ –> e) ≃ Σ B P)
Σ-emap-l P (f , e) = _ , Σ-isemap-l P e

Σ-fmap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  → (∀ x → B x → C x) → (Σ A B → Σ A C)
Σ-fmap-r h (a , b) = (a , h a b)

Σ-isemap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  {h : ∀ x → B x → C x} → (∀ x → is-equiv (h x)) → is-equiv (Σ-fmap-r h)
Σ-isemap-r {A = A} {B = B} {C = C} {h} k = is-eq _ g f-g g-f
  where f = Σ-fmap-r h

        g : Σ A C → Σ A B
        g (a , c) = (a , is-equiv.g (k a) c)

        f-g : ∀ p → f (g p) == p
        f-g (a , c) = pair= idp (is-equiv.f-g (k a) c)

        g-f : ∀ p → g (f p) == p
        g-f (a , b) = pair= idp (is-equiv.g-f (k a) b)

Σ-emap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  → (∀ x → B x ≃ C x) → (Σ A B ≃ Σ A C)
Σ-emap-r k = _ , Σ-isemap-r (λ x → snd (k x))

-- Commutativity of products and derivatives.
module _ {i j} {A : Type i} {B : Type j} where
  ×-comm : Σ A (λ _ → B) ≃ Σ B (λ _ → A)
  ×-comm = equiv (λ {(a , b) → (b , a)}) (λ {(b , a) → (a , b)}) (λ _ → idp) (λ _ → idp)

module _ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k} where
  Σ₁-×-comm : Σ A (λ a → Σ B (λ b → C a b)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  Σ₁-×-comm = Σ-assoc ∘e Σ-emap-l _ ×-comm ∘e Σ-assoc ⁻¹


-- Function.agda

infixr 30 _∼_ 
_∼_ : ∀ {i j} {A : Type i} {B : A → Type j}
  (f g : (a : A) → B a) → Type (lmax i j)
f ∼ g = ∀ x → f x == g x


-- Funext.agda
-- difference: funext is turned into an axiom, and λ=-is-equiv is not proved
-- using univalence but with uip (it may be possible to prove it without uip
-- though)
module _ {i}{A : Type i}{j} {P : A → Type j} {f g : Π A P} where
  postulate
    λ= : f ∼ g → f == g

module _ {i}{A : Type i}{j} {P : A → Type j} {f g : Π A P} where
  app= : ∀ {f g : Π A P} (p : f == g) → f ∼ g
  app= p x = ap (λ u → u x) p

  λ=-equiv : (f ∼ g) ≃ (f == g)
  λ=-equiv = (λ= , λ=-is-equiv) where
    abstract
      λ=-is-equiv : is-equiv λ=
      λ=-is-equiv = is-eq λ= app= (λ b → uip _ _) λ a → λ= λ _ → uip _ _  

-- Pi.agda
instance
  Π-level : ∀ {i j} {A : Type i} {B : A → Type j} {n : ℕ₋₂}
    → ((x : A) → has-level n (B x)) → has-level n (Π A B)
  Π-level {n = ⟨-2⟩} p = has-level-in ((λ x → contr-center (p x)) , lemma)
    where abstract lemma = λ f → λ= (λ x → contr-path (p x) (f x))
  Π-level {n = S n} p = has-level-in lemma where
    abstract
      lemma = λ f g →
        equiv-preserves-level λ=-equiv {{Π-level (λ x → has-level-apply (p x) (f x) (g x))}}


-- Lift.agda
lift-equiv : ∀ {i j} {A : Type i} → A ≃ Lift {ℓ = j} A
lift-equiv = equiv lift lower (λ _ → idp) (λ _ → idp)


-- HoTT.agda

-- deprecated operators
module _ where
  infix 15 _∎
  _∎ = _=∎
