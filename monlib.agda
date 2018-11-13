
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

  -- same, but we ask for a sigma equality
  -- ₁pair-triple= : ∀ {α β δ}{A : Set α}{B : A → Set β}{C :  (Σ _ B)  → Set δ}
  --   {a : A}{b b' : B a} {c : C (a , b)} {c' : C (a , b')}
  --   (eb : (b , c) ≡ b' , c') →
  --   pair {B = C} ((a , b)) c ≡ pair {B = C} ((a , b')) c' 
  -- ₁pair-triple= refl = refl
