
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)

module monlib where

-- postulate
--   admit : ∀ {a}{A : Set a} → A

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

  -- this needs uip
  ₁snd= : ∀ {α β}{A : Set α}{B : A → Set β} {a : A}{b b' : B a}(e : pair {B = B} a b  ≡ pair {B = B} a b') → b ≡ b'
  ₁snd= refl = refl

  -- this needs uip
  ₁triple= : ∀ {α β δ}{A : Set α}{B : A → Set β}{C : ∀ a → B a → Set δ}
    {a : A}{b b' : B a} {c : C a b} {c' : C a b'}
    (e : pair {A = Σ A B}{B = λ ab  → C (₁ ab) (₂ ab)} ((a , b)) c ≡
    pair {A = Σ A B}{B = λ ab  → C (₁ ab) (₂ ab)} ((a , b')) c') →
    (b , c) ≡ (b' , c')
  ₁triple= refl = refl


  ₁mk-triple= : ∀ {α β δ}{A : Set α}{B : A → Set β}{C :  (Σ _ B)  → Set δ}
    {a : A}{b b' : B a} {c : C (a , b)} {c' : C (a , b')}
    (eb : b ≡ b')
    (ec : c == c' [ _ ↓ eb ]) →
     pair {B = C} ((a , b)) c ≡ pair {B = C} ((a , b')) c' 
  ₁mk-triple= refl refl = refl


-- stuff for ModelRecord
tr2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}(C : ∀ a → B a → Set k)
  {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
  {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → C a₀ b₀ → C a₁ b₁
tr2 {B = B} C {a₀}{.a₀} refl refl c₀ = c₀

-- can't find this in Hott Lib...
transpose-tr! :  ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y)
  {a : B y} {b : B x} (e : a ≡ tr B p b) → tr B (! p) a ≡ b  
transpose-tr!  B refl e = e

-- stuff for ModelMorphism

-- can't find this in Hott Lib...
transpose-tr :  ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : y ≡ x)
  {a : B y} {b : B x} (e : a ≡ tr B (! p) b) → tr B p a ≡ b  
transpose-tr  B refl e = e

tr-swap :  ∀ {i j k} {A : Type i} {B : A → Type j}{C : A → Type k} (f : ∀ a → B a → C a) {x y : A} (p : x ≡ y)
  (b : B x)→ f _ (tr B p b) ≡ tr C p (f _ b)
tr-swap f refl b = refl


uip : ∀ {i} {A : Type i} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

uip-coe : ∀ {i }  {x y : Type i} (p q : x ≡ y)  {b : x}  →
  coe p b ≡ coe q b
uip-coe refl refl = refl

coe-∙2' : ∀ {i } {A B C D : Type i} (p : A ≡ B) (q : B ≡ C)(r : C ≡ D) (a : A)
  → coe r (coe q (coe p a)) ≡ coe (p ◾ q ◾ r) a
coe-∙2' refl refl q a = refl
