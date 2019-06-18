
open import Level 
-- open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to transport ; fst to ₁ ; snd to ₂)
-- open import HoTT renaming ( _∙_ to _◾_ ; idp to refl ; transport to transport ; fst to ₁ ; snd to ₂)
open import Hott renaming (fst to ₁ ; snd to ₂ ; _∙_ to _◾_ )
-- open import lib.types.Lift

module monlib where

open import Relation.Binary.PropositionalEquality public using (_≡_; refl)
open import Data.List public using (List; _∷_ ; map) renaming ([] to nil)
-- open import Data.List
open import Data.Nat renaming (suc to S)
-- _≡_ = _==_
-- infix 4 _≡_

-- I can't find this in the HoTT library
olookup : ∀ {a} {A : Set a} (xs : List A) → ℕ → A → A
olookup nil n e = e
olookup (x ∷ xs) 0 e = x
olookup (x ∷ xs) (S n) e = olookup xs n e

olookup-map : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) (x : ℕ) (err : A) l →
  olookup (map f l) x (f err) ≡ f (olookup l x err)
olookup-map f x err nil = refl
olookup-map f 0 err (x₁ ∷ l) = refl
olookup-map f (S x) err (x₁ ∷ l) =  olookup-map f x err l 

-- I can't find this in the HoTT library
map-∘ : ∀ {i j k} {A : Type i} {B : Type j} (f : A → B)
  {C : Type k} (g : C → A)  l → map f (map g l) ≡ map (λ x → f (g x)) l
map-∘ f g nil = refl
map-∘ f g (x ∷ l) = ap (f (g x) ∷_) (map-∘ f g l)

pw-map= : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B} (e : ∀ a → f a ≡ g a) →
  ∀ l → map f l ≡ map g l
pw-map=  e nil = refl
pw-map=  e (x ∷ l) = ap2 _∷_ (e x) (pw-map=  e l)

iter : ∀{l }{A : Set l}  (n : ℕ)(f : A → A) → A → A
iter 0 f  x = x
iter (S n) f x = f (iter n f x)


-- j'ai pas trouvé dans la libraire HoTT..
-- transport sur PathOver
tr!-over : ∀ {i j k} {A : Type i} {B : A → Type j}(C : ∀ a → B a → Type k)
  {x y : A} {p : x ≡ y} {u : B x} {v : B y} (q : u == v [ B ↓ p ]) → C y v → C x u
tr!-over C {p = refl} refl c = c

tr-over : ∀ {i j k} {A : Type i} {B : A → Type j}(C : ∀ a → B a → Type k)
  {x y : A} {p : x ≡ y} {u : B x} {v : B y} (q : u == v [ B ↓ p ]) → C x u → C y v
tr-over C {p = refl} refl c = c

forget-tr! : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y)
    (by  : B y)
     {k}{C : Set k}(g : ∀ {a} → B a → C) →
    g by ≡ g (transport! B p by)

forget-tr! B refl bx g = refl

-- to infer typeclasses
it : ∀{a}{A : Set a} {{_ : A}} → A
it {{x}} = x

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (lmax a b)
∃ = Σ _

propΣ= : ∀ {l j}{A : Set l} {B : A → Set j}{x y : ∃ B} (e : ₁ x ≡ ₁ y) → {{ b : ∀ {x} → is-prop (B x) }} →
  x ≡ y
propΣ= {B = B}{y = y} e {{ b }} = pair= e (from-transp _ e (prop-path {A = B (₁ y)}  (b {₁ y}) _ _ ))


{-
New version of agda does not support implicit arguments
for typeclasse instances !
Thus I make two version of the following lemmas: the original one with explicit arguments,
and a new one with implicit arguments.
Yet, the instances do not seem to be inferred as well as before...
-}

pathto-is-prop : ∀ {l}{A : Set l} (x : A) → is-prop (Σ A (λ t → t ≡ x))
-- we know it is contractile, thus uses typeclass resolution
pathto-is-prop x = raise-level ⟨-2⟩ (pathto-is-contr _)


instance
  i-pathto-is-prop : ∀ {l}{A : Set l} {x : A} → is-prop (Σ A (λ t → t ≡ x))
  -- we know it is contractile, thus uses typeclass resolution
  i-pathto-is-prop  = pathto-is-prop _

pathOverto-is-prop : 
  ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x ≡ y) (u : B y)  → is-prop (∃ (λ t → t == u [ B ↓ p ]))

pathOverto-is-prop B p u =
  equiv-preserves-level (
    Σ-emap-r λ tm' →
      to-transp!-equiv _ _ ⁻¹ )
      {{ pathto-is-prop _ }}
      -- before, this was inferred,
      -- {{ {!!} }}
     
      -- {{ pathto-is-prop _ }}


-- instance
--   i-pathOverto-is-prop : 
--     ∀ {i j} {A : Type i} {B : A → Type j}
--     {x y : A} {p : x ≡ y} {u : B y}  → is-prop (∃ (λ t → t == u [ B ↓ p ]))

--   i-pathOverto-is-prop = pathOverto-is-prop _ _ _

Lift-pathto-is-prop : ∀ {l j}{A : Set l} (x : A) → is-prop (Σ A (λ t → Lift {ℓ = j} (t ≡ x)))
Lift-pathto-is-prop {A = A} x =
  equiv-preserves-level {A = Σ A (λ t → t ≡ x) }
  (Σ-emap-r (λ x₁ → lift-equiv))
  {{ pathto-is-prop _ }}


instance

  i-Lift-pathto-is-prop : ∀ {l j}{A : Set l} {x : A} → is-prop (Σ A (λ t → Lift {ℓ = j} (t ≡ x)))
  i-Lift-pathto-is-prop {A = A} {x} = Lift-pathto-is-prop _ 

Lift-pathOverto-is-prop : 
  ∀ {i j k} {A : Type i} (B : A → Type j)
  {x y : A} (p : x ≡ y) (u : B y)  → is-prop (∃ (λ t → Lift {ℓ  = k}(t == u [ B ↓ p ])))
Lift-pathOverto-is-prop B p u =
      equiv-preserves-level {A = Σ _ (λ t → t == u [ B ↓ p ]) }
      (Σ-emap-r (λ x₁ → lift-equiv))
      {{ pathOverto-is-prop B p u }}

instance

  i-Lift-pathOverto-is-prop : 
    ∀ {i j k} {A : Type i} {B : A → Type j}
    {x y : A} {p : x ≡ y} {u : B y}  → is-prop (∃ (λ t → Lift {ℓ  = k}(t == u [ B ↓ p ])))
  i-Lift-pathOverto-is-prop = Lift-pathOverto-is-prop _ _ _
     
      -- (Σ-emap-r (λ x₁ → lift-equiv))
  -- {{ it }}
  -- raise-level ⟨-2⟩ it

-- this needs uip (not contractile although)
Σpathto-is-prop : ∀ {l l'}{A : Set l}{P : A → Set l'}(x : A)(y : Σ A P) → is-prop (Σ (P x) ( λ z → x , z ≡ y) )
Σpathto-is-prop x y = all-paths-is-prop  λ { (a , refl) (.a , refl) → refl  }

instance
  -- this needs uip (not contractile although)
  i-Σpathto-is-prop : ∀ {l l'}{A : Set l}{P : A → Set l'}{x : A}{y : Σ A P} → is-prop (Σ (P x) ( λ z → x , z ≡ y) )
  i-Σpathto-is-prop = Σpathto-is-prop _ _

-- this needs uip
₁snd= : ∀ {α β}{A : Set α}{B : A → Set β} {a : A}{b b' : B a}(e : _,_ {B = B} a b  ≡ _,_ {B = B} a b') → b ≡ b'
₁snd= refl = refl

-- this needs uip
₁triple= : ∀ {α β δ}{A : Set α}{B : A → Set β}{C : ∀ a → B a → Set δ}
  {a : A}{b b' : B a} {c : C a b} {c' : C a b'}
  (e : _,_ {A = Σ A B}{B = λ ab  → C (₁ ab) (₂ ab)} ((a , b)) c ≡
  _,_ {A = Σ A B}{B = λ ab  → C (₁ ab) (₂ ab)} ((a , b')) c') →
  (b , c) ≡ (b' , c')
₁triple= refl = refl


₁mk-triple= : ∀ {α β δ}{A : Set α}{B : A → Set β}{C :  (Σ _ B)  → Set δ}
  {a : A}{b b' : B a} {c : C (a , b)} {c' : C (a , b')}
  (eb : b ≡ b')
  (ec : c == c' [ _ ↓ eb ]) →
    _,_ {B = C} ((a , b)) c ≡ _,_ {B = C} ((a , b')) c' 
₁mk-triple= refl refl = refl


-- stuff for ModelRecord (picken from Ambrus'repo)
tr2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}(C : ∀ a → B a → Set k)
  {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : transport B a₂ b₀ ≡ b₁)
  → C a₀ b₀ → C a₁ b₁
tr2 {B = B} C {a₀} a₂ b₂ c₀ = transport (λ x → C (₁ x) (₂ x)) (pair= a₂ (from-transp _ a₂ b₂)) c₀

-- this is for InitialMorphism
tr3 : 
  ∀ {i j k l}{A : Set i}{B : A → Set j}{C : ∀ a → B a → Set k}
  (D : ∀ a b → C a b → Set l)
  {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : transport B a₂ b₀ ≡ b₁)
  {c₀ : C _ b₀}{c₁ : C _ b₁}(c₂ : tr2 C a₂ b₂ c₀  ≡ c₁)
  → D a₀ b₀ c₀ → D a₁ b₁ c₁
tr3 {B = B} {C = C} D refl refl refl c₀ = c₀

-- -- this is for InitialMorphism
-- tr2=transport :
--   ∀ {i j k}{A : Set i}{B : A → Set j}(C : ∀ a → B a → Set k)
--   {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
--   {b₀ : B a₀}{b₁ : B a₁}(b₂ : transport B a₂ b₀ ≡ b₁)
--   → (c : C a₀ b₀) → tr2 C a₂ b₂ c ≡ transport (λ x → C (₁ x) (₂ x)) (pair= a₂ (from-transp _ a₂ b₂)) c
-- tr2=transport {B = B} C {a₀}{.a₀} refl refl c₀ = refl

-- can't find this in Hott Lib...
transpose-tr! :  ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y)
  {a : B y} {b : B x} (e : a ≡ transport B p b) → transport B (! p) a ≡ b  
transpose-tr!  B refl e = e

-- this is for ModelRecord
transpose-tr!' :  ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y)
  {a : B y} {b : B x} (e : transport B p b ≡ a ) → b ≡ transport B (! p) a
transpose-tr!' B refl e = e

-- stuff for ModelMorphism

-- custom datatype not enjoying eta to block the reduction
-- of a function which takes an argument of this type ⊤' and
-- performs a pattern matching on it (then it won't reduce
-- unless we give it explicitely the constructor)
data ⊤' {i}: Type i  where
  unit' : ⊤'

-- can't find this in Hott Lib...
transpose-transport :  ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : y ≡ x)
  {a : B y} {b : B x} (e : a ≡ transport B (! p) b) → transport B p a ≡ b  
transpose-transport  B refl e = e

tr-swap :  ∀ {i j k} {A : Type i} {B : A → Type j}{C : A → Type k} (f : ∀ a → B a → C a) {x y : A} (p : x ≡ y)
  (b : B x)→ f _ (transport B p b) ≡ transport C p (f _ b)
tr-swap f refl b = refl



instance
  uip-prop : ∀ {i} {A : Type i} {x y : A} → is-prop (x ≡ y)
  uip-prop = all-paths-is-prop uip

uip-over-prop :
  ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x ≡ y)(v : B x) (u : B y)   → is-prop (v == u [ B ↓ p ])
uip-over-prop B p u v = equiv-preserves-level (to-transp!-equiv _ _ ⁻¹)
-- Jesper
  {{ uip-prop }}
  -- {{ uip-prop }}

-- instance
--   i-uip-over-prop :
--     ∀ {i j} {A : Type i} {B : A → Type j}
--     {x y : A} {p : x ≡ y}{v : B x} {u : B y}   → is-prop (v == u [ B ↓ p ])
--   i-uip-over-prop = uip-over-prop _ _ _ _

uip-coe : ∀ {i }  {x y : Type i} (p q : x ≡ y)  {b : x}  →
  coe p b ≡ coe q b
uip-coe refl refl = refl

coe-∙2' : ∀ {i } {A B C D : Type i} (p : A ≡ B) (q : B ≡ C)(r : C ≡ D) (a : A)
  → coe r (coe q (coe p a)) ≡ coe (p ◾ q ◾ r) a
coe-∙2' refl refl q a = refl

-- stuff for InitialMorphism2
-- I can't find this in Hott Lib, only the coe! version..
transport-! : ∀ {i j} {A : Type i}(C : A → Type j) {x y : A} (p : x ≡ y)
  (b : C y) → transport C (! p) b ≡ transport! C p b
transport-! C refl b = refl

-- pour Embedding (piqué de Lib.agda)
-- _&_ :
--   ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
--   → f a₀ ≡ f a₁
-- f & refl = refl
-- infixl 9 _&_

-- from Ambrus' & Andrac' StrictLib
-- heterogeneous equality
------------------------------------------------------------

infix 4 _≅_
data _≅_ {α}{A : Set α}(a : A) : ∀ {B} → B → Set α where
  refl≅ : a ≅ a

-- this uses uip
uip-=[] :
  {i j : ULevel} {A : Type i} (B : A → Type j) {x : A} →
  (e : x ≡ x) → {px : B x} → {py : B x} →  px == py [ B ↓ e ] → px ≡ py
uip-=[] B refl p = p

-- this uses UIP
≅↓ : 
  {i j : ULevel} {A : Type i} {B : A → Type j} {x y : A} →
  {e : x ≡ y} → {px : B x} → {py : B y} →  px ≅ py →  px == py [ B ↓ e ]
≅↓ {e = refl} refl≅ = refl

-- but not this
↓≅ :
  {i j : ULevel} {A : Type i} {B : A → Type j} {x y : A} →
  {e : x ≡ y} → {px : B x} → {py : B y} → px == py [ B ↓ e ] → px ≅ py
↓≅ {e = refl} refl = refl≅

infixr 5 _∘≅_ 
_∘≅_ :
  ∀ {α : ULevel} {A : Set α}  {B : Set α}{C : Set α} →
  {a : A}{ b : B}{c : C}(ebc : c ≅ a)(eab : a ≅ b) → c ≅ b
refl≅ ∘≅ q = q

_!≅ :
  ∀ {α : ULevel} {A : Set α}  {B : Set α} →
  {a : A}{ b : B}(ebc : b ≅ a) → a ≅ b
refl≅ !≅ = refl≅

=≅ : {i : ULevel} {A : Type i} → {x : A}{y : A} (e : x ≡ y) → x ≅ y
=≅ refl = refl≅

-- ≅≡ : ∀ {i } {A : Type i} {x y : A} (p : x ≅ y) → x ≡ y

infixr 10 _≅⟨_⟩_
infix  15 _≅∎

_≅⟨_⟩_ : ∀ {i} {A B C : Type i} (x : A) {y : B}{ z : C} → x ≅ y → y ≅ z → x ≅ z
_ ≅⟨ refl≅ ⟩ refl≅ = refl≅

_≅∎ : ∀ {i} {A : Type i} (x : A) → x ≅ x
_ ≅∎ = refl≅

-- -}
