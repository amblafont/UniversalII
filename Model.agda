{-# OPTIONS  --rewriting  #-}
-- an attempt with rewrite rules, but by postulating the model rather than defining a record (because rewrite rules don't work)

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)



module Model {ℓ}  where
  infixl 5 _▶_
  infixl 5 _^^_
  -- syntax PathOver B p u v = u == v [ B ↓ p ]

  -- PathOver' : ∀ {i j} {A : Type i} (B : A → Type j)
  --   {x y : A} (p : x ≡ y) (u : B x) (v : B y) → Type j
  -- PathOver' B e u v = u == v [ B ↓ e ] 


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
    ΠΠ    : (Γ : Con)(A : Tm Γ (U Γ))(B : Ty (Γ ▶ (El Γ A))) → Ty Γ


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
    app : (Γ : Con)(A : Tm Γ (U _))(B : Ty (Γ ▶ El _ A)) (t : Tm Γ (ΠΠ Γ A B)) (u : Tm Γ (El _ A)) →
      Tm Γ (subT Γ (El _ A) u B)

    -- this is not the right thing but, a first attempt..
    -- this is the counter part of com_lift in thee syntax
    lift-wkT : {Γ : Con}{Δ : Telescope Γ}(A : Ty (Γ ^^ Δ))
       (B : Ty (Γ ^^ Δ))
      (E : Ty Γ) →
      liftT Γ (Δ ▶t A) E (wkT (Γ ^^ Δ) A B) ≡ wkT (Γ ▶ E ^^ wkC Γ E Δ) (liftT Γ Δ E A) (liftT Γ Δ E B)


     -- definitional in the syntax
    liftU : {Γ : Con}(Δ : Telescope Γ)(E : Ty Γ) →
      liftT Γ Δ E (U _) ↦ U _

  {-# REWRITE liftU  #-}

  postulate
    -- definitional in the syntax
    liftEl : {Γ : Con}(Δ : Telescope Γ)(E : Ty Γ)(a : Tm (Γ ^^ Δ) (U _)) →
      liftT Γ Δ E (El _ a) ↦ El (Γ ▶ E ^^ wkC Γ E Δ) (liftt Γ Δ E (U _) a)
  {-# REWRITE liftEl  #-}
  postulate
    -- definitional in the syntax
    -- we can deal without definitional equation?
    liftΠ : {Γ : Con}(Δ : Telescope Γ)(E : Ty Γ)(A : Tm (Γ ^^ Δ) (U _))
      (B : Ty ((Γ ^^ Δ) ▶ (El _ A))) →
      liftT Γ Δ E (ΠΠ _ A B) ≡
        ΠΠ _ (liftt Γ Δ E _ A) (liftT Γ (Δ ▶t (El _ A)) E B)


    -- I did not need this equation in the syntax (because it was immediate ?)
    liftV0 : (Γ : Con)(Δ : Telescope Γ) (A : Ty (Γ ^^ Δ))(Ex : Ty Γ) →
      liftt Γ (Δ ▶t A)  Ex (wkT (Γ ^^ Δ) A A) (V0 (Γ ^^ Δ) A)
       == V0 (Γ ▶ Ex ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A) [ Tm _ ↓ lift-wkT {Γ} {Δ} A A Ex  ]
    -- I did not need this equation in the syntax (because it was immediate ?)
    lift-wkt : {Γ : Con}(Δ : Telescope Γ) (A : Ty (Γ ^^ Δ))(B : Ty (Γ ^^ Δ))(Ex : Ty Γ) →
      (t : Tm (Γ ^^ Δ) B) →
        liftt Γ (Δ ▶t A) Ex (wkT (Γ ^^ Δ) A B) (wkt (Γ ^^ Δ) A B t) ==
        wkt (Γ ▶ Ex ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A) (liftT Γ Δ Ex B)
        (liftt Γ Δ Ex B t) [ Tm _ ↓ lift-wkT {Δ = Δ} A B Ex ]


      
