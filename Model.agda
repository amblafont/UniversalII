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

    -- note that this is weaker that we could naively require (z : Tm (Γ ^^ Δ) (weakening de E))
    -- mais comemnt exprimer ce weakening?
    l-subT : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope Γ) (z : Tm Γ Ex)
      (A : Ty ((Γ ▶ Ex) ^^ (wkC _ Ex Δ))) → Ty (Γ ^^ Δ)

  subT : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → Ty (Γ ▶ Ex) → Ty Γ
  subT Γ Ex = l-subT Ex (∙t _)


  postulate

    subt : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → (A : Ty (Γ ▶ Ex) ) (u : Tm _ A )→
      -- Tm Γ (subT Γ Ex t A)
      Tm Γ (l-subT Ex (∙t _) t A)

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
      liftT Γ Δ E (ΠΠ _ A B) ↦
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

  {-# REWRITE liftΠ  #-}

      
-- for the application case of lifttw
-- remove to show Nicolas the pb
  postulate
    subU : {Γ : Con}(Ex : Ty Γ)(t : Tm Γ Ex) →
      l-subT Ex (∙t _) t (U _) ↦ U _
  {-# REWRITE subU  #-}
  postulate
    subEl : {Γ : Con}(Ex : Ty Γ)(t : Tm Γ Ex) (u : Tm (Γ ▶ Ex) (U _)) →
      l-subT Ex (∙t _) t (El _ u) ↦ El Γ (subt Γ Ex t (U _) u)

      -- TODO: decomment after this rewrite pb has been solved
      {-
  {-# REWRITE subEl  #-}
  postulate
    -- counter part of the syntax lift-sub
    lift-subT : {Γ : Con}(Δ : Telescope Γ)(Ex : Ty Γ) (A : Ty (Γ ^^ Δ))(B : Ty ((Γ ^^ Δ) ▶ A))
      (t : Tm (Γ ^^ Δ) A) →
      liftT Γ Δ Ex (subT _ _ t B) ≡ subT _ _ (liftt Γ Δ Ex _ t) (liftT Γ (Δ ▶t A) Ex B)

    --definitional in the syntax ?
    lift-app : {Γ : Con}(Δ : Telescope Γ)(Ex : Ty Γ)
      (A : Tm _ (U (Γ ^^ Δ)))(B : Ty ((Γ ^^ Δ) ▶ El _ A))
      (t : Tm _ (ΠΠ _ A B)) (u : Tm _ (El _ A)) →
      liftt Γ Δ Ex _ (app _ A B t u) ==
        app (Γ ▶ Ex ^^ wkC Γ Ex Δ) (liftt Γ Δ Ex _ A) (liftT Γ (Δ ▶t El _ A) Ex B )
          (liftt Γ Δ Ex _ t) (liftt Γ Δ Ex _ u)
        [ Tm _ ↓ lift-subT Δ Ex _ B u ]

    -- definitional in the syntax
     {-
    sub-app : {Γ : Con}(E : Ty Γ)
       (A : Tm (Γ ▶ E) (U _))(B : Ty (Γ ▶ E ▶ (El _ A)))
       (t : Tm _ (ΠΠ (Γ ▶ E) A B)) (u : Tm _ (El _ A))
       (z : Tm _ E) →
       subt _ E z (subT _ (El _ A) u B) (app _ A B t u) ≡
       app Γ (subt _ E z _ A) {! !} {!subt _ E z!} (subt _ E z (El _ A) u)
    --    -}


    -- not needed in the syntax??
    lift-subt : {Γ : Con}(Δ : Telescope Γ)(Ex : Ty Γ) (A : Ty (Γ ^^ Δ))(B : Ty ((Γ ^^ Δ) ▶ A))
      (t : Tm (Γ ^^ Δ) A)(u : Tm _ B) →
      liftt Γ Δ Ex (subT _ _ t B) (subt _ _ t B u) ==
        subt _ _ (liftt Γ Δ Ex _ t)(liftT Γ (Δ ▶t A) Ex B)(liftt Γ (Δ ▶t A) Ex B u)
        [ Tm _ ↓ lift-subT Δ Ex A B t ]



-- -}
