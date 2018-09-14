{-# OPTIONS  --rewriting #-}
-- an attempt with rewrite rules, but by postulating the model rather than defining a record (because rewrite rules don't work)

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)

module Model {ℓ}  where
  infixl 5 _▶_
  infixl 5 _^^_
  postulate
    Con  : Set ℓ
    Telescope : Con → Set ℓ
    Ty   : Con → Set ℓ
    Tm   : (Γ : Con) → Ty Γ → Set ℓ
    -- Var   : (Γ : Con) → Ty Γ → Set ℓ

    ∙    : Con
    _▶_  : (Γ : Con) → Ty Γ → Con


    _^^_ : (Γ : Con)(Δ : Telescope Γ) → Con

    ∙t    : ∀ Γ → Telescope Γ
    _▶t_  : ∀ {Γ}(Δ : Telescope Γ) → Ty (Γ ^^ Δ) → Telescope Γ

    ^^∙t : (Γ : Con) → (Γ ^^ ∙t Γ) ↦ Γ
    ^^▶t : (Γ : Con)(Δ : Telescope Γ)(A : Ty (Γ ^^ Δ)) →
      (Γ ^^ (Δ ▶t A)) ↦ ((Γ ^^ Δ) ▶ A)




    U    : (Γ : Con) → Ty Γ
    El   : (Γ : Con) → Tm Γ (U Γ) → Ty Γ
    ΠΠ    : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) → Ty Γ


    wkC : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ) → Telescope (Γ ▶ Ex)

    wk∙t : (Γ : Con)(Ex : Ty Γ) → wkC Γ Ex (∙t _) ↦ ∙t _

  {-# REWRITE ^^∙t  #-}
  {-# REWRITE ^^▶t  #-}
  {-# REWRITE wk∙t  #-}

  postulate

    liftT : (Γ : Con)(Δ : Telescope Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ)) → Ty ((Γ ▶ Ex) ^^ wkC Γ Ex Δ)
    liftt : (Γ : Con)(Δ : Telescope Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ))(t : Tm _ A) →
      Tm ((Γ ▶ Ex) ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A)

    -- wk▶t : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ)
    --   (A : Ty (Γ ^^ Δ)) → ((Γ ▶ Ex) ^^ wkC Γ Ex (Δ ▶t A)) ↦ (((Γ ▶ Ex) ^^ (wkC Γ Ex Δ)) ▶ liftT Γ Δ Ex A)
    wk▶t : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ)(A : Ty (Γ ^^ Δ)) →
      (wkC Γ Ex (Δ ▶t A)) ↦ ((wkC Γ Ex Δ) ▶t liftT Γ Δ Ex A)



  {-# REWRITE wk▶t  #-}

  wkT : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ) → Ty (Γ ▶ Ex)
  wkT Γ Ex A = liftT Γ (∙t Γ) Ex A

  wkt : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ)(t : Tm Γ A) → Tm (Γ ▶ Ex) (wkT Γ Ex A)
  wkt Γ Ex A t = liftt Γ (∙t Γ) Ex A t

  postulate
    V0 : (Γ : Con)(A : Ty Γ) → Tm (Γ ▶ A) (wkT Γ A A)
    -- VS : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ) (x : Var Γ A) → Var (Γ ▶ Ex) (wkT Γ Ex A)

    subT : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → Ty (Γ ▶ Ex) → Ty Γ
    subt : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → (A : Ty (Γ ▶ Ex) ) (u : Tm _ A )→ Tm Γ (subT Γ Ex t A)

    -- v : (Γ : Con)(A : Ty Γ)(x : Var Γ A) → Tm Γ A
    app : (Γ : Con)(A : Ty Γ)(B : Ty (Γ ▶ A)) (t : Tm Γ (ΠΠ Γ A B)) (u : Tm Γ A) →
      Tm Γ (subT Γ A u B)
