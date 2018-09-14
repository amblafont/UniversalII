
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
