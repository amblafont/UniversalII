-- a definition of model, without rewrite rules. It exactly follows the rewrite rule version.

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)


module ModelRecord   where


-- tr-tp : ∀ {i j} {A B : Type i} (p : A ≡ B) (x : A) (C : A → Type j)
-- (c : )

record Model {ℓ} : Set (Level.suc ℓ) where
  infixl 5 _▶_
  infixl 5 _^^_
  field

    Con  : Set ℓ
    Telescope : Con → Set ℓ
    Ty   : Con → Set ℓ
    Tm   : (Γ : Con) → Ty Γ → Set ℓ

  tr-Tm : {Γ : Con}  {A : Ty Γ}{B : Ty Γ} (e : A ≡ B)(t : Tm _ A) → Tm _ B
  tr-Tm {Γ} = tr (Tm Γ)

  tr-Ty : {Γ : Con} {Δ : Con}  (e : Γ ≡ Δ)(A : Ty Γ) → Ty Δ
  tr-Ty = tr Ty

  tr2-Tm : {Γ : Con} {Δ : Con} {A : Ty Γ} (e : Γ ≡ Δ)(t : Tm _ A) →
    Tm  _ (tr-Ty e A) 
  tr2-Tm e t  = tr2 Tm e refl t

  tr2-Tm⁻¹ : {Γ : Con} {Δ : Con} {A : Ty Γ} (e : Γ ≡ Δ) →
    (t : Tm  _ (tr-Ty e A) ) → Tm _ A
  tr2-Tm⁻¹ e t  = tr2 Tm (! e) (! (transp-∙ e (! e) _) ◾ ap (λ x → tr Ty x _) (!-inv-r e) ) t
  -- tr2 Tm e refl ?



  field
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

    ^^∙t : {Γ : Con} → (Γ ^^ ∙t Γ) ≡ Γ
    ^^▶t : {Γ : Con}{Δ : Telescope Γ}{A : Ty (Γ ^^ Δ)} →
      (Γ ^^ (Δ ▶t A)) ≡ ((Γ ^^ Δ) ▶ A)




    U    : (Γ : Con) → Ty Γ
    El   : (Γ : Con) → Tm Γ (U Γ) → Ty Γ
    ΠΠ    : (Γ : Con)(A : Tm Γ (U Γ))(B : Ty (Γ ▶ (El Γ A))) → Ty Γ


    wkC : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ) → Telescope (Γ ▶ Ex)

    wk∙t : {Γ : Con}{Ex : Ty Γ} → wkC Γ Ex (∙t _) ≡ ∙t _



    liftT : (Γ : Con)(Δ : Telescope Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ)) → Ty ((Γ ▶ Ex) ^^ wkC Γ Ex Δ)
    liftt : (Γ : Con)(Δ : Telescope Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ))(t : Tm _ A) →
      Tm ((Γ ▶ Ex) ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A)

    -- wk▶t : (Γ : Con)(Ex : Ty Γ)(Δ : Telescope Γ)
    --   (A : Ty (Γ ^^ Δ)) → ((Γ ▶ Ex) ^^ wkC Γ Ex (Δ ▶t A)) ↦ (((Γ ▶ Ex) ^^ (wkC Γ Ex Δ)) ▶ liftT Γ Δ Ex A)
    wk▶t : {Γ : Con}{Ex : Ty Γ}{Δ : Telescope Γ}{A : Ty (Γ ^^ Δ)} →
      (wkC Γ Ex (Δ ▶t A)) ≡ ((wkC Γ Ex Δ) ▶t liftT Γ Δ Ex A)


    


  wkT : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ) → Ty (Γ ▶ Ex)
  wkT Γ Ex A = tr-Ty
    (ap (_^^_ _) wk∙t ◾ ^^∙t )
     (liftT Γ (∙t Γ) Ex (tr-Ty (! ^^∙t ) A)) 

  wkt : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ)(t : Tm Γ A) → Tm (Γ ▶ Ex) (wkT Γ Ex A)
  wkt Γ Ex A t
    = 
    tr2-Tm 
      (ap (_^^_ _) wk∙t ◾  ^^∙t )
      (liftt Γ (∙t Γ) Ex (tr-Ty (! ^^∙t) A) (tr2-Tm(! ^^∙t) t))

  field
    V0 : (Γ : Con)(A : Ty Γ) → Tm (Γ ▶ A) (wkT Γ A A)


    -- needed for l-subT
    subTel : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex)) (z : Tm Γ Ex) → Telescope Γ

    sub∙t : {Γ : Con}{Ex : Ty Γ}{z : Tm Γ Ex} → subTel Ex (∙t _) z ≡ ∙t _

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


    sub▶t : {Γ : Con}{Ex : Ty Γ}{z : Tm Γ Ex} 
       {Δ : Telescope (Γ ▶ Ex) } {A : Ty ((Γ ▶ Ex) ^^ Δ)} 
       → subTel Ex (Δ ▶t A) z ≡ (subTel Ex Δ z ▶t l-subT Ex Δ z A)


  -- postulate
  -- l-subT Ex (∙t _)


  field
    l-subt : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex) →
      (A : Ty (Γ ▶ Ex ^^ Δ) ) (u : Tm _ A )→
      Tm (Γ ^^ (subTel Ex Δ t)) (l-subT Ex Δ  t A)

  -- very similar to wkT / wkt
  subT : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → Ty (Γ ▶ Ex) → Ty Γ
  subT Γ Ex z A = tr-Ty 
    (ap (_^^_ _) sub∙t ◾ ^^∙t)
    (l-subT Ex (∙t _) z (tr-Ty (! ^^∙t) A))

  subt : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → (A : Ty (Γ ▶ Ex) ) (u : Tm _ A )→
    -- Tm Γ (subT Γ Ex t A)
    Tm Γ  (subT _ Ex  t A)
  subt Γ Ex t A u = 
    tr2-Tm 
    (ap (_^^_ _) sub∙t ◾ ^^∙t)
    (l-subt Ex (∙t _) t _ (tr2-Tm (! ^^∙t ) u))

  field

    -- v : (Γ : Con)(A : Ty Γ)(x : Var Γ A) → Tm Γ A
    app : (Γ : Con)(A : Tm Γ (U _))(B : Ty (Γ ▶ El _ A)) (t : Tm Γ (ΠΠ Γ A B)) (u : Tm Γ (El _ A)) →
      Tm Γ (subT Γ (El _ A) u B)

    -- this is not the right thing but, a first attempt..
    -- this is the counter part of com_lift in thee syntax
    -- this statment was designed to fit both lift-V0 and lift-wkt
    lift-wkT : {Γ : Con}{Δ : Telescope Γ}(A : Ty (Γ ^^ Δ))
       (B : Ty (Γ ^^ Δ))
      (Ex : Ty Γ) →
      tr Ty
        (ap (_^^_ (Γ ▶ Ex ^^ wkC Γ Ex Δ ▶ liftT Γ Δ Ex A)) wk∙t ◾ ^^∙t)
        (liftT (Γ ▶ Ex ^^ wkC Γ Ex Δ) (∙t (Γ ▶ Ex ^^ wkC Γ Ex Δ))
        (liftT Γ Δ Ex A) (tr Ty (! ^^∙t) (liftT Γ Δ Ex B)))
      ≡
      tr Ty (ap (_^^_ (Γ ▶ Ex)) wk▶t ◾ ^^▶t)
        (liftT Γ (Δ ▶t A) Ex
        (tr Ty (! ^^▶t)
        (tr Ty (ap (_^^_ (Γ ^^ Δ ▶ A)) wk∙t ◾ ^^∙t)
        (liftT (Γ ^^ Δ) (∙t (Γ ^^ Δ)) A (tr Ty (! ^^∙t) B)))))

      -- liftT Γ (Δ ▶t A) E
      -- ( tr-Ty (! ^^▶t) (wkT (Γ ^^ Δ) A B) )
      --   == liftT (Γ ▶ E ^^ wkC Γ E Δ) (∙t _)(liftT Γ Δ E A)
      --   (tr-Ty (! ^^∙t) (liftT Γ Δ E B))
      --   [ Ty ↓  ap (_^^_ _) wk▶t ◾ ^^▶t ◾ ! (^^∙t) ◾ ap (_^^_ _) (! wk∙t)   ]
        -- == wkT (Γ ▶ E ^^ wkC Γ E Δ) (liftT Γ Δ E A) (liftT Γ Δ E B)
        -- [ Ty ↓  ap (_^^_ _) wk▶t ◾ ^^▶t   ]


     -- definitional in the syntax

    liftU : {Γ : Con}(Δ : Telescope Γ)(E : Ty Γ) →
      liftT Γ Δ E (U _) ≡ U _



    -- definitional in the syntax
    liftEl : {Γ : Con}(Δ : Telescope Γ)(E : Ty Γ)(a : Tm (Γ ^^ Δ) (U _)) →
      liftT Γ Δ E (El _ a) ≡ El (Γ ▶ E ^^ wkC Γ E Δ)
        (tr-Tm (liftU _ _) (liftt Γ Δ E (U _) a) )

    -- definitional in the syntax
    -- we can deal without definitional equation?
    liftΠ : {Γ : Con}(Δ : Telescope Γ)(E : Ty Γ)(A : Tm (Γ ^^ Δ) (U _))
      (B : Ty ((Γ ^^ Δ) ▶ (El _ A))) →
      liftT Γ Δ E (ΠΠ _ A B) ≡
        ΠΠ _ (tr-Tm (liftU _ _) (liftt Γ Δ E _ A))
        -- this proof is designed to make lift-app easier
        -- ∙' allows to destruct liftEl easily (_ ∙' refl reduces to _)
          (tr-Ty (ap (_^^_ _) (wk▶t ∙' ap (_▶t_ _) (liftEl _ _ _)) ◾ ^^▶t)
          ((liftT Γ (Δ ▶t El _ A) E
            (tr-Ty (! ^^▶t) B))
            )
            )

    -- I did not need this equation in the syntax (because it was immediate ?)
    liftV0 : (Γ : Con)(Δ : Telescope Γ) (A : Ty (Γ ^^ Δ))(Ex : Ty Γ) →
      -- tr2-Tm {Δ = (Γ ▶ Ex ^^ wkC Γ Ex Δ ▶ liftT Γ Δ Ex A)}
      -- ( ap (_^^_ _) (wk▶t _ _ _ _)  ◾ ^^▶t
      -- )
      (liftt Γ (Δ ▶t A)  Ex (tr-Ty (! ^^▶t) (wkT (Γ ^^ Δ) A A))
        (tr2-Tm (! ^^▶t) (V0 (Γ ^^ Δ) A) ))
        ≡
        -- (λ x → {!!})
        (tr2-Tm⁻¹ {Γ = (Γ ▶ Ex ^^ wkC Γ Ex (Δ ▶t A))}
        -- (ap (_^^_ _) (wk▶t _ _ _ _)  ◾ ^^▶t)
        (ap (_^^_ _)
          wk▶t ◾ ^^▶t)
        (
        tr-Tm (lift-wkT A A Ex )
        (V0 (Γ ▶ Ex ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A) ) )
        )
        

       -- [ Tm _ ↓ ? ]
       -- lift-wkT {Γ} {Δ} A A Ex  ]
    -- I did not need this equation in the syntax (because it was immediate ?)
    lift-wkt : {Γ : Con}(Δ : Telescope Γ) (A : Ty (Γ ^^ Δ))(B : Ty (Γ ^^ Δ))(Ex : Ty Γ) →
      (t : Tm (Γ ^^ Δ) B) →
        liftt Γ (Δ ▶t A) Ex (tr-Ty (! ^^▶t) (wkT (Γ ^^ Δ) A B)) (tr2-Tm (! ^^▶t) (wkt (Γ ^^ Δ) A B t)) ==
        tr2-Tm (! (    ap (_^^_ _) wk▶t ◾ ^^▶t)) (wkt (Γ ▶ Ex ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A) (liftT Γ Δ Ex B)
        (liftt Γ Δ Ex B t)) 
        [ Tm _ ↓  ! (transpose-tr! _ _ (lift-wkT {Δ = Δ} A B Ex )) ]



      
-- for the substitution
-- remove to show Nicolas the pb
    l-subU : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex) →
      l-subT Ex Δ t (U _) ≡ U _

    l-subEl : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex)
      (u : Tm (Γ ▶ Ex ^^ Δ) (U _)) →
      -- subT _ Ex  t (El _ u) ↦ El Γ (subt Γ Ex t (U _) u)
      l-subT Ex Δ t (El _ u) ≡ El (Γ ^^ (subTel Ex Δ t)) (tr-Tm (l-subU _ _ _) (l-subt Ex Δ t (U _) u) )

    l-subΠ : {Γ : Con}(Ex : Ty Γ)(Δ : Telescope (Γ ▶ Ex))(t : Tm Γ Ex)
        (A : Tm (Γ ▶ Ex ^^ Δ) (U _))(B : Ty (Γ ▶ Ex ^^ Δ ▶ (El _ A))) →
        l-subT Ex Δ t (ΠΠ _ A B) ≡ ΠΠ (Γ ^^ (subTel Ex Δ t)) (tr-Tm (l-subU _ _ _) (l-subt Ex Δ t _ A))
        -- pareil que pour liftΠ : le ∙' permet de détruire l-subEl ..
        -- et d'obtenir un but adéquat dans sub-app
        (tr-Ty (ap (_^^_ _) sub▶t ◾ ^^▶t ∙' ap (_▶_ _) (l-subEl _ _ _ _))
        (l-subT Ex (Δ ▶t (El _ A)) t (tr-Ty (! ^^▶t) B)) )


    -- counter part of the syntax lift-sub
    lift-subT : {Γ : Con}(Δ : Telescope Γ)(Ex : Ty Γ) (A : Ty (Γ ^^ Δ))(B : Ty ((Γ ^^ Δ) ▶ A))
      (t : Tm (Γ ^^ Δ) A) →
      liftT Γ Δ Ex (subT _ _ t B) ≡ subT _ _ (liftt Γ Δ Ex _ t)
        (tr-Ty (ap (_^^_ _) wk▶t ◾ ^^▶t) (liftT Γ (Δ ▶t A) Ex (tr-Ty (! ^^▶t) B)))

    --definitional in the syntax ?
    -- it is not used later in this file
    lift-app : {Γ : Con}(Δ : Telescope Γ)(Ex : Ty Γ)
      (A : Tm _ (U (Γ ^^ Δ)))(B : Ty ((Γ ^^ Δ) ▶ El _ A))
      (t : Tm _ (ΠΠ _ A B)) (u : Tm _ (El _ A)) →
      liftt Γ Δ Ex _ (app _ A B t u) ==
        app (Γ ▶ Ex ^^ wkC Γ Ex Δ) (tr-Tm (liftU _ _) (liftt Γ Δ Ex _ A))
          -- (tr-Ty (ap (_^^_ _) wk▶t ◾ ^^▶t ◾ ap (_▶_ _) (liftEl _ _ _ ) )
          (tr-Ty (ap (_^^_ (Γ ▶ Ex)) (wk▶t ∙' ap (_▶t_ (wkC Γ Ex Δ)) (liftEl Δ Ex A))
              ◾ ^^▶t)
          (liftT Γ (Δ ▶t El _ A) Ex (tr-Ty (! ^^▶t) B) ))
        (tr-Tm ((liftΠ _ _ _ _ )) (liftt Γ Δ Ex _ t) ) (tr-Tm (liftEl _ _ _) (liftt Γ Δ Ex _ u))
        [ Tm _ ↓ lift-subT Δ Ex _ B u ◾
        
          J
            (λ E e →
               -- the l.h.s does not depend on E/e
                tr Ty (ap (_^^_ (Γ ▶ Ex ^^ wkC Γ Ex Δ)) sub∙t ◾ ^^∙t)
               (l-subT (liftT Γ Δ Ex (El (Γ ^^ Δ) A))
               (∙t _)
               (liftt Γ Δ Ex (El (Γ ^^ Δ) A) u)
                (tr Ty (! ^^∙t)
                (tr Ty (ap (_^^_ (Γ ▶ Ex)) wk▶t ◾ ^^▶t)
               (liftT Γ (Δ ▶t El (Γ ^^ Δ) A) Ex (tr Ty (! ^^▶t) B)))))

               ≡
               -- the r.h.s. depends on E/e
               tr Ty (ap (_^^_ (Γ ▶ Ex ^^ wkC Γ Ex Δ)) sub∙t ◾ ^^∙t)
               (l-subT E (∙t _)
                (tr (Tm (Γ ▶ Ex ^^ wkC Γ Ex Δ)) e (liftt Γ Δ Ex (El (Γ ^^ Δ) A) u))
                (tr Ty (! ^^∙t)
                 (tr Ty
                  (ap (_^^_ (Γ ▶ Ex)) (wk▶t ∙' ap (_▶t_ (wkC Γ Ex Δ)) e) ◾ ^^▶t)
                  (liftT Γ (Δ ▶t El (Γ ^^ Δ) A) Ex (tr Ty (! ^^▶t) B))))))
            refl (liftEl _ _ _ )
            
            ]
        -- lift-subT Δ Ex _ B u ]

    -- counter part of the syntax l-subT-subT
    -- only used for sub-app
    l-subT-subT : {Γ : Con}(E : Ty Γ)(Δ : Telescope (Γ ▶ E)) (z : Tm _ E)
      (A : Ty (Γ ▶ E ^^ Δ)) (a : Tm _ A)  (B : Ty (Γ ▶ E ^^ Δ ▶ A)) →
      l-subT E Δ z (subT (Γ ▶ E ^^ Δ) A a B) ≡
        subT (Γ ^^ subTel E Δ z) (l-subT E Δ z A) (l-subt E Δ z _ a)
          ( tr-Ty (ap (_^^_ _) sub▶t ◾ ^^▶t) (l-subT E (Δ ▶t A) z
            ( tr-Ty (! ^^▶t) B )) )

    --definitional in the syntax ?
    -- this is not used later
    sub-app : {Γ : Con}(E : Ty Γ)(Δ : Telescope (Γ ▶ E))(z : Tm _ E)
       (A : Tm _ (U (Γ ▶ E ^^ Δ)))(B : Ty ((Γ ▶ E ^^ Δ) ▶ El _ A))
       (t : Tm _ (ΠΠ _ A B)) (u : Tm _ (El _ A)) 
      → l-subt E Δ z _ (app _ _ _ t u)  ==
        tr2-Tm (ap (_^^_ (Γ ^^ subTel E Δ z)) sub∙t ◾ ^^∙t)
        (tr2-Tm⁻¹
           {Γ ^^ subTel E Δ z ^^
            subTel (l-subT E Δ z (El (Γ ▶ E ^^ Δ) A))
            (∙t _)
            (l-subt E Δ z (El (Γ ▶ E ^^ Δ) A) u)}
           (ap (_^^_ _) sub∙t ◾ ^^∙t)
           (tr-Tm
           -- same J as in lift-app

           (J
              (λ EL e →
                 tr Ty (ap (_^^_ (Γ ^^ subTel E Δ z)) sub∙t ◾ ^^∙t)
                 (l-subT EL (∙t _)
                  (tr (Tm (Γ ^^ subTel E Δ z)) e
                   (l-subt E Δ z (El (Γ ▶ E ^^ Δ) A) u))
                  (tr Ty (! ^^∙t)
                   (tr Ty (ap (_^^_ Γ) sub▶t ◾ ^^▶t ∙' ap (_▶_ (Γ ^^ subTel E Δ z)) e)
                    (l-subT E (Δ ▶t El (Γ ▶ E ^^ Δ) A) z (tr Ty (! ^^▶t) B)))))
                 ≡
                 tr Ty (ap (_^^_ (Γ ^^ subTel E Δ z)) sub∙t ◾ ^^∙t)
                 (l-subT (l-subT E Δ z (El (Γ ▶ E ^^ Δ) A)) (∙t _)
                  (l-subt E Δ z (El (Γ ▶ E ^^ Δ) A) u)
                  (tr Ty (! ^^∙t)
                   (tr Ty (ap (_^^_ Γ) sub▶t ◾ ^^▶t)
                    (l-subT E (Δ ▶t El (Γ ▶ E ^^ Δ) A) z (tr Ty (! ^^▶t) B))))))
              refl (l-subEl _ _ _ _))

            (app (Γ ^^ subTel E Δ z) ( tr-Tm (l-subU _ _ _) (l-subt  E Δ z _ A)  )
             (tr-Ty
             (ap (_^^_ Γ) sub▶t ◾ ^^▶t ∙' ap (_▶_ (Γ ^^ subTel E Δ z)) (l-subEl E Δ z A))
              (l-subT E (Δ ▶t El _ _) z (tr-Ty (! ^^▶t) B))
             )
             (tr-Tm (l-subΠ E Δ z A B   ) (l-subt E Δ z _ t))
             (tr-Tm (l-subEl _ _ _ _) (l-subt E Δ z _ u))) ))
        [ Tm _ ↓  l-subT-subT E Δ z (El (Γ ▶ E ^^ Δ) A) u B   ]


    {-
    counter part of the syntax l-subT-wkT/l-subt-wkt

    used for l-subt-wkt and Sn-subt-v0
    -}
    l-subT-wkT : {Γ : Con} {E : Ty Γ}(z : Tm _ E)
      {Δ : Telescope (Γ ▶ E)}(A : Ty (Γ ▶ E ^^ Δ))(C : Ty (Γ ▶ E ^^ Δ)) →
      l-subT E (Δ ▶t C) z (tr-Ty (! ^^▶t) (wkT (Γ ▶ E ^^ Δ) C A)) ≡
        tr-Ty ( ! (ap (_^^_ _) sub▶t ◾ ^^▶t)) (wkT (Γ ^^ subTel E Δ z) (l-subT E Δ z C) (l-subT E Δ z A))  

    -- not used later
    l-subt-wkt : {Γ : Con} {E : Ty Γ}(z : Tm _ E)
      {Δ : Telescope (Γ ▶ E)}{A : Ty (Γ ▶ E ^^ Δ)}(t : Tm _ A)(C : Ty (Γ ▶ E ^^ Δ)) →
      l-subt E (Δ ▶t C) z ( tr-Ty (! ^^▶t) (wkT (Γ ▶ E ^^ Δ) C A))
        (tr2-Tm (! ^^▶t) (wkt (Γ ▶ E ^^ Δ) C A t) ) ==
         tr2-Tm  (! (ap (_^^_ Γ) sub▶t ◾ ^^▶t)) (wkt (Γ  ^^ _) (l-subT E Δ z C) _ (l-subt E Δ z A t)) 
        [ Tm _ ↓ l-subT-wkT z {Δ = Δ} A C  ]

    -- counter part of the syntax lemma subT-wkT
    subT-wkT : {Γ : Con} {E : Ty Γ}(z : Tm _ E) (A : Ty Γ) →
      subT Γ E z (wkT Γ E A) ≡ A

    subt-wkt : {Γ : Con} {E : Ty Γ}(z : Tm _ E) {A : Ty Γ}(t : Tm _ A) →
      subt Γ E z (wkT Γ E A) (wkt Γ E A t) ==  t  [ Tm _ ↓ subT-wkT z A  ]



    -- l-subt 0 u v0 = u (definitional in the syntax)
    subt-v0 : {Γ : Con} {E : Ty Γ} (z : Tm _ E) →
      subt Γ E z (wkT Γ E E) (V0 _ E) == z [ Tm _ ↓ subT-wkT z E ]
      

    -- l-subt (S n) u v0 = v0 (definitional in the syntax)
    Sn-subt-v0 : {Γ : Con} {E : Ty Γ} (z : Tm _ E)
      {Δ : Telescope (Γ ▶ E)}(A : Ty (Γ ▶ E ^^ Δ)) →
      l-subt {Γ = Γ} E (Δ ▶t A) z _ ( tr2-Tm (! ^^▶t)(V0 _ A) ) ==
        tr2-Tm (! (ap (_^^_ Γ) sub▶t ◾ ^^▶t)) (V0 _ (l-subT E Δ z A )) 
        [ Tm _ ↓ l-subT-wkT z {Δ = Δ } A A ]

   
