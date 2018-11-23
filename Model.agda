{-# OPTIONS  --rewriting   #-}
-- an attempt with rewrite rules, but by postulating the model rather than defining a record (because rewrite rules don't work)

-- probably a lot of statments of rewrite rules about subT should be generalized to l-subT

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

    -- redundant with ▶t and ^^
    -- indeed, Γ ▶ A could be defined as (Γ ^^ (∙t ▶t A)).
    -- but then the rewrite rule ^^▶t would introduce a loop:
    -- (Γ ^^ (Δ ▶t A)) ↦ (Γ ^^ Δ) ^^ (∙t ▶t A) ↦ Γ ^^ Δ ^^ ∙t ^^ (∙t ▶t A) ↦ ...
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


    -- needed for l-subT
    subTel : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex)) (z : Tm Γ Ex) → Telescope Γ

    sub∙t : (Γ : Con)(Ex : Ty Γ)(z : Tm Γ Ex) → subTel Ex (∙t _) z ↦ ∙t _

-- note that this is weaker that we could naively require (z : Tm (Γ ^^ Δ) (weakening de E))
-- mais comemnt exprimer ce weakening?
-- Also, note that this generalized version of substitution is not required for defining
-- the functional relation, but to show that this relation is preserved by substitution
-- this is also the case of lifts
-- Γ ⊢ t : E     Γ , E ⊢ Δ      Γ , E , Δ ⊢ A  
-- then
-- Γ , Δ[t] ⊢ A[t] 
    l-subT : {Γ : Con}(E : Ty Γ)(Δ : Telescope (Γ ▶ E)) (z : Tm Γ E)
      (A : Ty ((Γ ▶ E) ^^ Δ)) → Ty (Γ ^^ subTel E Δ z)


    sub▶t : (Γ : Con)(Ex : Ty Γ)(z : Tm Γ Ex) 
       (Δ : Telescope (Γ ▶ Ex) ) (A : Ty ((Γ ▶ Ex) ^^ Δ)) 
       → subTel Ex (Δ ▶t A) z ↦ (subTel Ex Δ z ▶t l-subT Ex Δ z A)
  {-# REWRITE sub∙t  #-}
  {-# REWRITE sub▶t  #-}


  -- postulate
  subT : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → Ty (Γ ▶ Ex) → Ty Γ
  subT Γ Ex = l-subT Ex (∙t _)


  postulate
    l-subt : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex) →
      (A : Ty (Γ ▶ Ex ^^ Δ) ) (u : Tm _ A )→
      Tm (Γ ^^ (subTel Ex Δ t)) (l-subT Ex Δ  t A)

  subt : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → (A : Ty (Γ ▶ Ex) ) (u : Tm _ A )→
    -- Tm Γ (subT Γ Ex t A)
    Tm (Γ ^^ (∙t Γ)) (l-subT Ex (∙t _)  t A)
  subt Γ Ex t A u = l-subt Ex (∙t _) t A u

  postulate

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

      
-- for the substitution
-- remove to show Nicolas the pb
  postulate
    l-subU : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex) →
      l-subT Ex Δ t (U _) ↦ U _

  {-# REWRITE l-subU  #-}
  postulate
    l-subEl : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex)
      (u : Tm (Γ ▶ Ex ^^ Δ) (U _)) →
      -- subT _ Ex  t (El _ u) ↦ El Γ (subt Γ Ex t (U _) u)
      l-subT Ex Δ t (El _ u) ↦ El (Γ ^^ (subTel Ex Δ t)) (l-subt Ex Δ t (U _) u)

  {-# REWRITE l-subEl  #-}
  postulate
    l-subΠ : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex)
        (A : Tm (Γ ▶ Ex ^^ Δ) (U _))(B : Ty (Γ ▶ Ex ^^ Δ ▶ (El _ A))) →
        l-subT Ex Δ t (ΠΠ _ A B) ↦ ΠΠ (Γ ^^ (subTel Ex Δ t)) (l-subt Ex Δ t _ A)
        (l-subT Ex (Δ ▶t (El _ _)) t B)

  {-# REWRITE l-subΠ  #-}

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

    -- counter part of the syntax l-subT-subT
    l-subT-subT : {Γ : Con}(E : Ty Γ)(Δ : Telescope (Γ ▶ E)) (z : Tm _ E)
      (A : Ty (Γ ▶ E ^^ Δ)) (a : Tm _ A)  (B : Ty (Γ ▶ E ^^ Δ ▶ A)) →
      l-subT E Δ z (subT (Γ ▶ E ^^ Δ) A a B) ≡
        subT (Γ ^^ subTel E Δ z) (l-subT E Δ z A) (l-subt E Δ z _ a)
          (l-subT E (Δ ▶t A) z B)
    --definitional in the syntax ?
    sub-app : {Γ : Con}(E : Ty Γ)(Δ : Telescope (Γ ▶ E))(z : Tm _ E)
       (A : Tm _ (U (Γ ▶ E ^^ Δ)))(B : Ty ((Γ ▶ E ^^ Δ) ▶ El _ A))
       (t : Tm _ (ΠΠ _ A B)) (u : Tm _ (El _ A)) 
      → l-subt E Δ z _ (app _ _ _ t u)  == app _ _ _ (l-subt E Δ z _ t) (l-subt E Δ z _ u)
        [ Tm _ ↓ l-subT-subT E Δ z (El (Γ ▶ E ^^ Δ) A) u B  ]

    {-
    counter part of the syntax l-subT-wkT/l-subt-wkt

    -}
    l-subT-wkT : {Γ : Con} {E : Ty Γ}(z : Tm _ E)
      {Δ : Telescope (Γ ▶ E)}(A : Ty (Γ ▶ E ^^ Δ))(C : Ty (Γ ▶ E ^^ Δ)) →
      l-subT E (Δ ▶t C) z (wkT (Γ ▶ E ^^ Δ) C A) ≡
         wkT (Γ ^^ subTel E Δ z) (l-subT E Δ z C) (l-subT E Δ z A) 

    l-subt-wkt : {Γ : Con} {E : Ty Γ}(z : Tm _ E)
      {Δ : Telescope (Γ ▶ E)}{A : Ty (Γ ▶ E ^^ Δ)}(t : Tm _ A)(C : Ty (Γ ▶ E ^^ Δ)) →
      l-subt E (Δ ▶t C) z (wkT (Γ ▶ E ^^ Δ) C A) (wkt (Γ ▶ E ^^ Δ) C A t) ==
        wkt _ _ _ (l-subt E Δ z A t) [ Tm _ ↓ l-subT-wkT z {Δ = Δ} A C  ]

    -- counter part of the syntax lemma subT-wkT
    subT-wkT : {Γ : Con} {E : Ty Γ}(z : Tm _ E) (A : Ty Γ) →
      subT Γ E z (wkT Γ E A) ≡ A

    subt-wkt : {Γ : Con} {E : Ty Γ}(z : Tm _ E) {A : Ty Γ}(t : Tm _ A) →
      subt Γ E z (wkT Γ E A) (wkt Γ E A t) == t [ Tm _ ↓ subT-wkT z A  ]


    -- l-subt 0 u v0 = u (definitional in the syntax)
    subt-v0 : {Γ : Con} {E : Ty Γ} (z : Tm _ E) →
      subt Γ E z (wkT Γ E E) (V0 _ E) == z [ Tm _ ↓ subT-wkT z E ]
      

    -- l-subt (S n) u v0 = v0 (definitional in the syntax)
    Sn-subt-v0 : {Γ : Con} {E : Ty Γ} (z : Tm _ E)
      {Δ : Telescope (Γ ▶ E)}(A : Ty (Γ ▶ E ^^ Δ)) →
      l-subt {Γ = Γ} E (Δ ▶t A) z _ (V0 _ _) == V0 _ _
        [ Tm _ ↓ l-subT-wkT z {Δ = Δ } A A ]
    
    

{-
    sub-app : {Γ : Con}(E : Ty Γ)
       (A : Tm (Γ ▶ E) (U _))(B : Ty (Γ ▶ E ▶ (El _ A)))
       (t : Tm _ (ΠΠ (Γ ▶ E) A B)) (u : Tm _ (El _ A))
       (z : Tm _ E) →
       subt _ E z (subT _ (El _ A) u B) (app _ A B t u) ≡
       -- we want that Γ ⊢ B[u][z] is equal to Γ ⊢ B[z][u[z]]
       {!
        app Γ (subt _ E z _ A)
         (l-subT E (∙t _ ▶t (El _ A)) z B) 
          {!subt _ E z!} (subt _ E z (El _ A) u)
       !}


    -- not needed in the syntax??
    lift-subt : {Γ : Con}(Δ : Telescope Γ)(Ex : Ty Γ) (A : Ty (Γ ^^ Δ))(B : Ty ((Γ ^^ Δ) ▶ A))
      (t : Tm (Γ ^^ Δ) A)(u : Tm _ B) →
      liftt Γ Δ Ex (subT _ _ t B) (subt _ _ t B u) ==
        subt _ _ (liftt Γ Δ Ex _ t)(liftT Γ (Δ ▶t A) Ex B)(liftt Γ (Δ ▶t A) Ex B u)
        [ Tm _ ↓ lift-subT Δ Ex A B t ]



-- -}
-- -}
