{-
Paper: section 7.2

This file contains a part of the CwF-K-Eq of natural number algebras,
and a (specialized to this case) proof that induction is logically
equivalent to initiality.
-}

{-# OPTIONS --without-K #-}

open import StrictLib

Con : Set₁
Con = Σ Set λ N → N × (N → N)

Sub : Con → Con → Set
Sub (N , z , s) (N' , z' , s') = Σ (N → N') λ Nᴹ → (Nᴹ z ≡ z') × (∀ n → Nᴹ (s n) ≡ s' (Nᴹ n))

Ty : Con → Set₁
Ty (N , z , s) = Σ (N → Set) λ Nᶠ → Nᶠ z × (∀ n → Nᶠ n → Nᶠ (s n))

Tm : ∀ Γ → Ty Γ → Set
Tm (N , z , s) (Nᶠ , zᶠ , sᶠ) = Σ (∀ n → Nᶠ n) λ Nˢ → (Nˢ z ≡ zᶠ) × (∀ n → Nˢ (s n) ≡ sᶠ n (Nˢ n))

infixl 5 _▶_
_▶_ : (Γ : Con) → Ty Γ → Con
(N , z , s) ▶ (Nᶠ , zᶠ , sᶠ) = Σ N Nᶠ , (z , zᶠ) , λ {(n , nᶠ) → s n , sᶠ n nᶠ}

π₁ : ∀ {Γ Δ A} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {N , z , s} {N' , z' , s'} (Nᴹ , zᴹ , sᴹ) = (₁ ∘ Nᴹ) , (₁ & zᴹ) , λ n → ₁ & sᴹ n

infixl 5 _[_]T
_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {N , z , s}{N' , z' , s'} (Nᶠ , zᶠ , sᶠ) (Nᴹ , zᴹ , sᴹ) =
  (Nᶠ ∘ Nᴹ) , coe (Nᶠ & (zᴹ ⁻¹)) zᶠ , λ n nᶠ → coe (Nᶠ & (sᴹ n ⁻¹)) (sᶠ (Nᴹ n) nᶠ)

π₂ : ∀ {Γ Δ A} → (σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ {Γ}{Δ}{A} σ ]T)
π₂ {N , z , s} {N' , z' , s'}{Aᶠ , zᶠ , sᶠ}(Nᴹ , refl , sᴹ) =
  (₂ ∘ Nᴹ) , refl , λ n →
      J (λ x eq → ₂ x ≡ coe (Aᶠ & (₁ & eq)) (sᶠ (₁ (Nᴹ n)) (₂ (Nᴹ n)))) refl (sᴹ n ⁻¹)
    ◾ (λ x → coe (Aᶠ & x) (sᶠ (₁ (Nᴹ n)) (₂ (Nᴹ n)))) & (&⁻¹ ₁ (sᴹ n) ⁻¹)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {N , z , s} = id , refl , λ _ → refl

[idₛ]T : ∀ {Γ}{A} → A [ idₛ {Γ} ]T ≡ A
[idₛ]T {Γ}{A} = refl

-- Initiality and induction
------------------------------------------------------------

contr : ∀ {α} → Set α → Set α
contr A = Σ A λ a → ∀ a' → a' ≡ a

Initial : Con → Set₁
Initial Γ = ∀ Δ → contr (Sub Γ Δ)

Induction : Con → Set₁
Induction Γ = ∀ A → Tm Γ A

------------------------------------------------------------

Initial⇒Induction : ∀ Γ → Initial Γ → Induction Γ
Initial⇒Induction Γ init A =
  coe (_&_ (Tm Γ) {A [ π₁ {Γ}{Γ}{A} (init (Γ ▶ A) .₁) ]T}{A}
           ((A [_]T) & (init Γ .₂ (π₁ {Γ}{Γ}{A} (init (Γ ▶ A) .₁)) ◾ init Γ .₂ idₛ ⁻¹)))
      (π₂ {Γ}{Γ}{A} (init (Γ ▶ A) .₁))

------------------------------------------------------------

K : Con → ∀ {Γ} → Ty Γ
K (N , z , s) {Γ} = (λ _ → N) , z , (λ _ → s)

unk : ∀ {Γ Δ} → Tm Γ (K Δ) → Sub Γ Δ
unk {Γ}{Δ} = id

-- likewise, (mk : Sub Γ Δ → Tm Γ (K Δ)) is just id,
-- and thus β and η rules for K are refl.

-- We can make do with only equality of Sub-s, if we don't want to
-- prove propositionality of induction.
Eq : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → Ty Γ
Eq {N₀ , z₀ , s₀}{N₁ , z₁ , s₁} (Nᴹ₀ , zᴹ₀ , sᴹ₀) (Nᴹ₁ , zᴹ₁ , sᴹ₁)
  = (λ n → Nᴹ₀ n ≡ Nᴹ₁ n) ,
    (zᴹ₀ ◾ zᴹ₁ ⁻¹) ,
    λ n p → sᴹ₀ n ◾ s₁ & p ◾ sᴹ₁ n ⁻¹

-- We can use this version to prove propositionality of induction.
Eq' : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
Eq' {N , z , s}{Nᵈ , zᵈ , sᵈ} (Nˢ₀ , zˢ₀ , sˢ₀) (Nˢ₁ , zˢ₁ , sˢ₁) =
  (λ n → Nˢ₀ n ≡ Nˢ₁ n) , (zˢ₀ ◾ zˢ₁ ⁻¹) , (λ n p → sˢ₀ n ◾ sᵈ n & p ◾ sˢ₁ n ⁻¹)

reflect : ∀ {Γ Δ σ δ} → Tm Γ (Eq {Γ}{Δ} σ δ) → (σ ≡ δ)
reflect {N₀ , z₀ , s₀}{N₁ , z₁ , s₁}
    {Nᴹ₀ , zᴹ₀ , sᴹ₀}{Nᴹ₁ , zᴹ₁ , sᴹ₁}
    (Nˢ , sˢ , zˢ) =
    ,≡ (ext Nˢ)
       (,≡ (UIP _ _) (ext (λ _ → UIP _ _)))

Induction⇒Initial : ∀ Γ → Induction Γ → Initial Γ
Induction⇒Initial Γ ind Δ =
  unk {Γ}{Δ} (ind (K Δ)) ,
  λ σ → reflect (ind (Eq {Γ}{Δ} σ (ind (K Δ))))

-- Some other K/Eq operations
------------------------------------------------------------

mk : ∀ {Γ Δ} → Sub Γ Δ → Tm Γ (K Δ)
mk {Γ}{Δ} = id

Refl : ∀ {Γ Δ} (σ : Sub Γ Δ) → Tm Γ (Eq {Γ}{Δ} σ σ)
Refl σ = (λ _ → refl) , (UIP _ _) , (λ _ → UIP _ _)

Eq← : ∀ {Γ Δ σ δ} → (σ ≡ δ) → Tm Γ (Eq {Γ}{Δ} σ δ)
Eq← {Γ}{Δ}{σ}{δ} p = tr (λ δ → Tm Γ (Eq {Γ}{Δ} σ δ)) p (Refl {Γ}{Δ} σ)
