{-
Paper: section 7.3

A proof that initiality is equivalent to induction in any CwF-K-Eq.
-}

{-# OPTIONS --without-K #-}
open import StrictLib
open import Data.Nat
import Level as L

-- Some background lemmas for propositionality of initiality.
-- We use "without-K" because we can without much difficulty.
--------------------------------------------------------------------------------

isContr : ∀ {i} → Set i → Set i
isContr A = Σ A λ a → ∀ a' → a' ≡ a

isProp : ∀ {i} → Set i → Set i
isProp A = (a a' : A) → a ≡ a'

isSet : ∀ {i} → Set i → Set i
isSet A = (a a' : A) → isProp (a ≡ a')

contr→prop : ∀ {i}{A : Set i} → isContr A → isProp A
contr→prop (a* , p) a a' = p a ◾ p a' ⁻¹

lem : ∀ {i}{A : Set i}{a b c : A} (p : b ≡ c) (q : a ≡ b) → coe ((a ≡_) & p) q ≡ (q ◾ p)
lem refl refl = refl

lem2 : ∀ {i}{A : Set i}{a b c : A} (p : a ≡ b) q (r : a ≡ c) → (p ◾ q) ≡ r → q ≡ (p ⁻¹ ◾ r)
lem2 refl _ _ s = s

prop→set : ∀ {i}{A : Set i} → isProp A → isSet A
prop→set {_}{A} f a a' p q =
    (lem2 (f a a) _ _ (lem p (f a a) ⁻¹ ◾ apd (f a) p))
  ◾ (lem2 (f a a) _ _ (lem q (f a a) ⁻¹ ◾ apd (f a) q) ⁻¹)

contrProp : ∀ {i}(A : Set i) → isProp (isContr A)
contrProp A (a , p) (a' , p') = ,≡ (p' a) (ext λ x → prop→set (contr→prop (a , p)) _ _ _ _)

--------------------------------------------------------------------------------

record CwF-K-Eq : Set₂ where
  infixl 5 _▶_ _[_]T _[_]t _,ₛ_
  infixr 5 _∘ₛ_
  field
    Con     : Set₁
    ∙       : Con
    Sub     : Con → Con → Set
    Ty      : Con → Set₁
    Tm      : ∀ Γ → Ty Γ → Set
    _▶_     : (Γ : Con) → Ty Γ → Con
    π₁      : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Sub Γ Δ
    _[_]T   : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    π₂      : ∀ {Γ Δ A} → (σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)
    idₛ     : ∀ {Γ} → Sub Γ Γ

    _∘ₛ_    : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
    idlₛ    : ∀{Γ Δ}{σ : Sub Γ Δ} → (_∘ₛ_ {Γ}{Δ}{Δ} idₛ σ) ≡ σ
    idrₛ    : ∀{Γ Δ}{σ : Sub Γ Δ} → (_∘ₛ_ {Γ}{Γ}{Δ} σ idₛ) ≡ σ
    assₛ    : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ} →
                _∘ₛ_ {Γ}{Δ}{Ω}(_∘ₛ_ {Δ}{Σ}{Ω} σ δ) ν ≡ _∘ₛ_ {Γ}{Σ}{Ω} σ (_∘ₛ_ {Γ}{Δ}{Σ} δ ν)
    [idₛ]T  : ∀ {Γ}{A} → A [ idₛ {Γ} ]T ≡ A
    [][]T   : ∀{Γ Θ Δ}{A : Ty Δ}{σ : Sub Θ Δ}{δ : Sub Γ Θ} → A [ σ ]T [ δ ]T ≡ A [ σ ∘ₛ δ ]T
    _[_]t   : ∀ {Γ Δ A} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
    _,ₛ_    : ∀ {Γ Δ A}(σ : Sub Γ Δ)(t : Tm Γ (A [ σ ]T)) → Sub Γ (Δ ▶ A)
    ε       : ∀ {Γ} → Sub Γ ∙
    εη      : ∀ {Γ σ} → σ ≡ ε {Γ}

    -- Constant families
    -- Given by natural isomorphisms
    K      : Con → ∀ {Γ} → Ty Γ
    K[]    : ∀ {Γ Δ Σ}{σ : Sub Σ Δ} → K Γ {Δ} [ σ ]T ≡ K Γ
    unk    : ∀ {Γ Δ} → Tm Γ (K Δ) → Sub Γ Δ
    mk     : ∀ {Γ Δ} → Sub Γ Δ → Tm Γ (K Δ)
    unk[]  : ∀ {Γ Δ Σ}(δ : Sub Γ Δ)(σ : Sub Δ Σ) → coe (Tm Γ & K[]) (mk σ [ δ ]t) ≡ mk (σ ∘ₛ δ)
    Kβ     : ∀ {Γ Δ σ} → unk {Γ}{Δ} (mk σ) ≡ σ
    Kη     : ∀ {Γ Δ t} → mk {Γ}{Δ} (unk t) ≡ t

    -- Extensional equality (with only reflection)
    Eq      : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
    Eq[]    : ∀ {Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ}{t u} → Eq {A = A} t u [ σ ]T ≡ Eq (t [ σ ]t) (u [ σ ]t)
    Reflect : ∀ {Γ A}{t u : Tm Γ A}(e : Tm Γ (Eq t u)) → t ≡ u

  Initial : Con → Set₁
  Initial Γ = ∀ Δ → isContr (Sub Γ Δ)

  Induction : Con → Set₁
  Induction Γ = ∀ A → Tm Γ A

  Initial⇒Induction : ∀ Γ → Initial Γ → Induction Γ
  Initial⇒Induction Γ init A =
    coe ( Tm Γ & (
            (A [_]T) & (init Γ .₂ _ ◾ init Γ .₂ _ ⁻¹)
          ◾ [idₛ]T))
        (π₂ (init (Γ ▶ A) .₁))

  Induction⇒Initial : ∀ Γ → Induction Γ → Initial Γ
  Induction⇒Initial Γ ind Δ =
    unk (ind (K Δ)) ,
    λ σ → Kβ ⁻¹ ◾ unk & Reflect (ind (Eq (mk σ) (ind (K Δ))))

  InitialityProp : ∀ Γ → isProp (Initial Γ)
  InitialityProp Γ init init' = ext λ Δ → contrProp (Sub Γ Δ) (init Δ) (init' Δ)

  InductionProp : ∀ Γ → isProp (Induction Γ)
  InductionProp Γ ind ind' = ext λ A → Reflect (ind (Eq (ind A) (ind' A)))
