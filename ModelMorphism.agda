

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import ModelRecord
open import monlib
-- Then, a definition of model morphism, based on a definition of model without rewrite rules
-- The big proofs : wkTᴹ and subTᴹ because they deal with horrible transports
module ModelMorphism where


module _ {ℓ₁} {ℓ₂} {A1 : Model1 {ℓ₁}} (A2 : Model2 A1) {B1 : Model1 {ℓ₂}} (B2 : Model2 B1)  where

  -- I split the def in two parts because I want to keep the def of wkTm and subTm separate from the record part
  record ModelMorphism1 : Set (lmax ℓ₁ ℓ₂)  where
    -- infixl 5 _▶_
    -- infixl 5 _^^_
    module M = Model1 A1
    module N = Model1 B1
    field
      Conᴹ : M.Con → N.Con
      Telescopeᴹ : ∀ {Γ} → M.Telescope Γ → N.Telescope (Conᴹ Γ)
      Tyᴹ : ∀ {Γ} → M.Ty Γ → N.Ty (Conᴹ Γ)
      Tmᴹ : ∀ {Γ} {A} → M.Tm Γ A → N.Tm (Conᴹ Γ) (Tyᴹ A)

      ∙ᴹ : Conᴹ M.∙ ≡ N.∙ 
      ▶ᴹ : ∀ {Γ} {A} → (Conᴹ (Γ M.▶ A)) ≡ (Conᴹ Γ N.▶ Tyᴹ A)
      ^^ᴹ : ∀ {Γ}{Δ} → (Conᴹ (Γ M.^^ Δ)) ≡ (Conᴹ Γ N.^^ Telescopeᴹ Δ)

      ∙tᴹ : ∀ {Γ} → Telescopeᴹ (M.∙t Γ) ≡ N.∙t _
      ▶tᴹ : ∀ {Γ}{Δ : M.Telescope Γ}{A} →
        (Telescopeᴹ (Δ M.▶t A)) ≡ ((Telescopeᴹ Δ) N.▶t N.tr-Ty ^^ᴹ (Tyᴹ A) )

      Uᴹ : ∀ {Γ} → (Tyᴹ (M.U Γ)) ≡ N.U _
      Elᴹ : ∀ {Γ}{A : M.Tm Γ (M.U Γ)} → Tyᴹ (M.El _ A) ≡ N.El _ (N.tr-Tm Uᴹ (Tmᴹ A))
      ΠΠᴹ : ∀ {Γ}{A : M.Tm Γ (M.U Γ)}{B} →
        Tyᴹ (M.ΠΠ _ A B) ≡ N.ΠΠ _ (N.tr-Tm Uᴹ (Tmᴹ A))
        -- the ∙' instead of ◾ is to make the definition of V0ᴹ easier
        -- as I will destruct the equality Elᴹ
          (N.tr-Ty (▶ᴹ ∙' ap (λ x → N._▶_ _ x) Elᴹ) (Tyᴹ B))

      wkCᴹ : ∀ {Γ}{E}{Δ} →
        Telescopeᴹ (M.wkC Γ E Δ) ≡ tr N.Telescope (! ▶ᴹ) (N.wkC _ (Tyᴹ E) (Telescopeᴹ Δ))

    ▶^^ᴹ : ∀ {Γ}{E}{Δ} →
      Conᴹ (Γ M.▶ E M.^^ Δ) ≡
      (Conᴹ Γ N.▶ Tyᴹ E N.^^ tr N.Telescope ▶ᴹ (Telescopeᴹ Δ))
    ▶^^ᴹ {Γ} {E} {Δ} = tr2 {B = N.Telescope} (λ x y →  Conᴹ (Γ M.▶ E M.^^ Δ) ≡ N._^^_ x y)
      ▶ᴹ refl ^^ᴹ



    ▶wkCᴹ : ∀ {Γ}{Δ : M.Telescope Γ}{E : M.Ty Γ} →
      Conᴹ (Γ M.▶ E M.^^ M.wkC Γ E Δ) ≡
      (Conᴹ Γ N.▶ Tyᴹ E N.^^ N.wkC (Conᴹ Γ) (Tyᴹ E) (Telescopeᴹ Δ))
    ▶wkCᴹ {Γ} {Δ} {E} = ▶^^ᴹ ◾ ap (λ x → N._^^_ _ x) (transpose-tr _ _ wkCᴹ)



    field

      liftTᴹ : ∀ {Γ}{Δ}{E : M.Ty Γ}{A : M.Ty (Γ M.^^ Δ)} →
        Tyᴹ (M.liftT _ _ E A) ≡
        N.tr-Ty (! (▶wkCᴹ {Δ = Δ} {E = E}))
          (N.liftT _ _ (Tyᴹ E) (N.tr-Ty ^^ᴹ (Tyᴹ A)))

      lifttᴹ : ∀ {Γ}{Δ}{E : M.Ty Γ}{A : M.Ty (Γ M.^^ Δ)}(t : M.Tm _ A) →
        Tmᴹ (M.liftt _ _ E A t) ≡
        N.tr2-Tm⁻¹
          {Δ =
          N._^^_ (N._▶_ (Conᴹ Γ) (Tyᴹ E))
          (N.wkC (Conᴹ Γ) (Tyᴹ E) (Telescopeᴹ Δ))}
            ▶wkCᴹ 
            (N.tr-Tm (! ((transpose-tr N.Ty ▶wkCᴹ liftTᴹ)) )
          (N.liftt _ _ (Tyᴹ E)(N.tr-Ty ^^ᴹ (Tyᴹ A))
            (N.tr2-Tm ^^ᴹ (Tmᴹ t))))

      -- needed for l-subT
      subTelᴹ : ∀ {Γ : M.Con}{Ex : M.Ty Γ}{Δ : M.Telescope (Γ M.▶ Ex)}
        {z : M.Tm Γ Ex} → Telescopeᴹ (M.subTel  Ex Δ z) ≡
        N.subTel (Tyᴹ Ex) (tr N.Telescope ▶ᴹ (Telescopeᴹ Δ)) (Tmᴹ z)

    ^^subTelᴹ : ∀ {Γ}{E}{Δ}{z} →
      Conᴹ (Γ M.^^ M.subTel E Δ z) ≡ (Conᴹ Γ N.^^
        N.subTel (Tyᴹ E) (tr N.Telescope ▶ᴹ (Telescopeᴹ Δ)) (Tmᴹ z))
    ^^subTelᴹ {Γ}{E}{Δ}{z} = ^^ᴹ ◾ ap (λ x → N._^^_ _ x) subTelᴹ

    field

      l-subTᴹ : ∀ {Γ : M.Con}{E : M.Ty Γ}{Δ : M.Telescope (Γ M.▶ E)} {z : M.Tm Γ E}
        {A : M.Ty ((Γ M.▶ E) M.^^ Δ)} →
        Tyᴹ (M.l-subT E Δ z A) ≡ N.tr-Ty (! ^^subTelᴹ) 
        (N.l-subT (Tyᴹ E) (tr N.Telescope ▶ᴹ (Telescopeᴹ Δ)) (Tmᴹ z)
          (N.tr-Ty ▶^^ᴹ (Tyᴹ A)))

      l-subtᴹ : ∀ {Γ : M.Con}{E : M.Ty Γ}{Δ : M.Telescope (Γ M.▶ E)} {z : M.Tm Γ E}
        {A : M.Ty ((Γ M.▶ E) M.^^ Δ)} {t : M.Tm _ A}→
        Tmᴹ (M.l-subt E Δ z A t) ≡
        -- fit to please InitialMorphism1
          tr2 N.Tm (! ^^subTelᴹ)
            (! l-subTᴹ)
            (N.l-subt (Tyᴹ E)
              (tr N.Telescope ▶ᴹ (Telescopeᴹ Δ))(Tmᴹ z) (N.tr-Ty ▶^^ᴹ (Tyᴹ A))
              (N.tr2-Tm ▶^^ᴹ (Tmᴹ t)))
        
        


  module _ (MOR1 : ModelMorphism1) where
    open ModelMorphism1 MOR1

    tr-swap-Tyᴹ : ∀ {x y : M.Con} (p : x ≡ y) b → Tyᴹ (tr M.Ty p b) ≡ tr (λ Γ' → N.Ty (Conᴹ Γ')) p (Tyᴹ b)
    tr-swap-Tyᴹ {x} {y} =
      tr-swap {A = M.Con} {B = M.Ty} {C = λ Γ' → N.Ty (Conᴹ Γ')}
      (λ Γ' A' → Tyᴹ {Γ = Γ'} A') {x} {y} 


    wkTᴹ : ∀ {Γ}{E}{A} → Tyᴹ (M.wkT Γ E A ) ≡ N.tr-Ty (! ▶ᴹ) (N.wkT _ _ (Tyᴹ A))
    wkTᴹ {Γ}{E}{A}= 
      (_
      =⟨
        tr-swap-Tyᴹ
      _
      (M.liftT Γ (M.∙t Γ) E (tr M.Ty (! M.^^∙t) A))


      ⟩
      _ 
      =⟨
      ap (tr _ _) liftTᴹ
      ⟩
      _
      ∎)
      ◾

      ap
        (λ A' →
          tr (λ Γ' → N.Ty (Conᴹ Γ')) (ap (M._^^_ (Γ M.▶ E)) M.wk∙t ◾ M.^^∙t)
            (N.tr-Ty (! ▶wkCᴹ)
            A'))
          ( 
          ap (N.liftT _ _ _ )
            (
            ap (N.tr-Ty _ ) (tr-swap-Tyᴹ _ A)
            ◾
            -- {! ! (coe-∙ _ _ _)) !}
            ! (coe-∙
                (ap (λ Γ' → N.Ty (Conᴹ Γ')) (! M.^^∙t) )
                (ap N.Ty ^^ᴹ )
              (Tyᴹ A))
              ◾
              uip-coe (ap (λ Γ' → N.Ty (Conᴹ Γ')) (! M.^^∙t) ◾ ap N.Ty ^^ᴹ)
                (ap N.Ty (! (ap (N._^^_ _) ∙tᴹ ◾ N.^^∙t)))
              -- Goal: coe (ap (λ Γ' → N.Ty (Conᴹ Γ')) (! M.^^∙t) ◾ ap N.Ty ^^ᴹ)
              -- (Tyᴹ A)
            )

          ◾
          (
          N.liftT (Conᴹ Γ) (Telescopeᴹ (M.∙t Γ)) (Tyᴹ E)
            (coe (ap N.Ty (! (ap (N._^^_ (Conᴹ Γ)) ∙tᴹ ◾ N.^^∙t))) (Tyᴹ A))
          =⟨
            J
              (λ Δ' e →
                ∀ q →
                N.liftT (Conᴹ Γ) (Telescopeᴹ (M.∙t Γ)) (Tyᴹ E)
                (coe (ap N.Ty (! (ap (N._^^_ (Conᴹ Γ)) e ◾ q))) (Tyᴹ A))
                ≡
                N.tr-Ty
                (ap
                  (λ Δ → N._^^_ (N._▶_ (Conᴹ Γ) (Tyᴹ E)) (N.wkC (Conᴹ Γ) (Tyᴹ E) Δ))
                  (! e))
                (N.liftT (Conᴹ Γ) Δ' (Tyᴹ E) (coe (ap N.Ty (! q)) (Tyᴹ A))))
              (λ _ → refl) ∙tᴹ N.^^∙t
                    -- )
          ⟩
          N.tr-Ty (ap (λ Δ → N._^^_ _ (N.wkC _ _ Δ)) (! ∙tᴹ)) (N.liftT (Conᴹ Γ) (N.∙t _) (Tyᴹ E) 
          (coe (ap N.Ty (! N.^^∙t)) (Tyᴹ A)))

          ∎)
          )
          -- y a plus qu'à fusionner les transports et utiliser uip

      ◾

        coe-∙2'
        (ap N.Ty (ap (λ Δ → Conᴹ Γ N.▶ Tyᴹ E N.^^ N.wkC (Conᴹ Γ) (Tyᴹ E) Δ) (! ∙tᴹ)))
        (ap N.Ty (! ▶wkCᴹ ) )
        (ap (λ Γ' → N.Ty (Conᴹ Γ')) (ap (M._^^_ (Γ M.▶ E)) M.wk∙t ◾ M.^^∙t))
        (N.liftT (Conᴹ Γ) (N.∙t (Conᴹ Γ)) (Tyᴹ E) (N.tr-Ty  (! N.^^∙t) (Tyᴹ A)))


      ◾
      -- maybe uip is not needed at this point, but it simplifies a lot
      -- how sad is it that agda is not able to infer the proof of equalities from the goal :(
      uip-coe
        (
          (ap N.Ty (ap (λ Δ → Conᴹ Γ N.▶ Tyᴹ E N.^^ N.wkC (Conᴹ Γ) (Tyᴹ E) Δ) (! ∙tᴹ)))
          ◾
          (ap N.Ty (! ▶wkCᴹ ) )
          ◾
          (ap (λ Γ' → N.Ty (Conᴹ Γ')) (ap (M._^^_ (Γ M.▶ E)) M.wk∙t ◾ M.^^∙t))
        )
        (
          (ap N.Ty (ap (N._^^_ (Conᴹ Γ N.▶ Tyᴹ E)) N.wk∙t ◾ N.^^∙t))
          ◾
          (ap N.Ty (! ▶ᴹ))
        )

      ◾
      --merge the transports
      coe-∙
        (ap N.Ty (ap (N._^^_ (Conᴹ Γ N.▶ Tyᴹ E)) N.wk∙t ◾ N.^^∙t))
        (ap N.Ty (! ▶ᴹ))
        (N.liftT (Conᴹ Γ) (N.∙t (Conᴹ Γ)) (Tyᴹ E) (N.tr-Ty  (! N.^^∙t) (Tyᴹ A)))









    ∙t▶ᴹ : ∀ {Γ}{E} →
      tr N.Telescope ▶ᴹ (Telescopeᴹ (M.∙t (Γ M.▶ E)))
      ≡
      N.∙t (Conᴹ Γ N.▶ Tyᴹ E) 
    ∙t▶ᴹ {Γ}{E} = 
      ap (tr N.Telescope ▶ᴹ) ∙tᴹ
      ◾
        J' {A = N.Con} {a = N._▶_ (Conᴹ Γ) (Tyᴹ E)}
        (λ Γ' e →
        tr N.Telescope e (N.∙t Γ') ≡ N.∙t (N._▶_ (Conᴹ Γ) (Tyᴹ E)))
        refl ▶ᴹ



    -- subTᴹ : the proof is similar to wkTᴹ
    -- subpart1
    subTᴹ-1 : ∀ {Γ}{E}{z}{A} → _
    subTᴹ-1 {Γ}{E}{z}{A} = 
        (
            _
            =⟨ l-subTᴹ ⟩

            N.tr-Ty (! (^^ᴹ ◾ ap (N._^^_ (Conᴹ Γ)) subTelᴹ))
              (N.l-subT (Tyᴹ E) (tr N.Telescope ▶ᴹ (Telescopeᴹ (M.∙t (Γ M.▶ E))))
              (Tmᴹ z)
              (N.tr-Ty ▶^^ᴹ
                (Tyᴹ (M.tr-Ty (! M.^^∙t) A))))

            =⟨ ap (N.tr-Ty _)
            ( ap (N.l-subT _ _ _ )
              (ap (N.tr-Ty ▶^^ᴹ ) (tr-swap-Tyᴹ (! M.^^∙t) A)
              ◾
              ! (coe-∙ (ap (λ Γ' → N.Ty (Conᴹ Γ')) (! M.^^∙t)) (ap N.Ty ▶^^ᴹ)  (Tyᴹ A) )
              ◾
              uip-coe (ap (λ Γ' → N.Ty (Conᴹ Γ')) (! M.^^∙t) ◾ ap N.Ty ▶^^ᴹ)
                (
                -- !
                (ap N.Ty
                  -- (ap (N._^^_ _) ∙t▶ᴹ ◾ N.^^∙t ◾ ! ▶ᴹ)
                  (▶ᴹ ◾ ! N.^^∙t ∙' ! (ap (N._^^_ (N._▶_ (Conᴹ Γ) (Tyᴹ E))) ∙t▶ᴹ) )
                )
                  )
              )
              ◾
              (
              N.l-subT (Tyᴹ E)
                (tr N.Telescope ▶ᴹ (Telescopeᴹ (M.∙t (Γ M.▶ E)))) (Tmᴹ z)
                (coe
                (
                -- !
                  (ap N.Ty
                  (▶ᴹ ◾ ! N.^^∙t ∙' ! (ap (N._^^_ (N._▶_ (Conᴹ Γ) (Tyᴹ E))) ∙t▶ᴹ) ) ))
                  -- (ap (N._^^_ (Conᴹ Γ N.▶ Tyᴹ E)) ∙t▶ᴹ ◾ N.^^∙t ◾ ! ▶ᴹ)))
                (Tyᴹ A))

              =⟨
              J'
                (λ Δ e →
                    N.l-subT (Tyᴹ E) Δ (Tmᴹ z)
                    (coe
                    (
                      (ap N.Ty
                      (▶ᴹ ◾ ! N.^^∙t ∙' ! (ap (N._^^_ (N._▶_ (Conᴹ Γ) (Tyᴹ E))) e ))))
                    (Tyᴹ A))
                    ≡
                    N.tr-Ty (ap (λ Δ' → N._^^_ _ (N.subTel (Tyᴹ E) Δ' (Tmᴹ z))) (! e))
                    (N.l-subT (Tyᴹ E) (N.∙t _) (Tmᴹ z)
                    (N.tr-Ty (▶ᴹ ◾ ! N.^^∙t) (Tyᴹ A))))
                refl ∙t▶ᴹ
              ⟩

              N.tr-Ty
                (ap (λ Δ' → N._^^_ _ (N.subTel (Tyᴹ E) Δ' (Tmᴹ z))) (! ∙t▶ᴹ))
                (N.l-subT (Tyᴹ E) (N.∙t _) (Tmᴹ z)
                (N.tr-Ty ( ▶ᴹ ◾ ! N.^^∙t) (Tyᴹ A)))
              =⟨ ap (λ A' → N.tr-Ty _ (N.l-subT _ _ _ A'))
                  (transp-∙ ▶ᴹ (! N.^^∙t) (Tyᴹ A)) 
                ⟩

              N.tr-Ty
                (ap (λ Δ' → N._^^_ _ (N.subTel (Tyᴹ E) Δ' (Tmᴹ z))) (! ∙t▶ᴹ))
                (N.l-subT (Tyᴹ E) (N.∙t _) (Tmᴹ z)
                (N.tr-Ty (! N.^^∙t) (N.tr-Ty ▶ᴹ (Tyᴹ A))))

              ∎
              )
              )
              -- ◾
              -- {!!}
              ⟩

            _
            ∎

            )



    -- this ⊤ is to block the reduction, because other wise in InitialMorphism2, it makes
    -- make type checking too slow of appᴹ
    subTᴹ :   ⊤' {ℓ₂} →
      ∀ {Γ}{E}{z}{A} → Tyᴹ (M.subT Γ E z A) ≡ N.subT _ (Tyᴹ E) (Tmᴹ z) (N.tr-Ty ▶ᴹ (Tyᴹ A))
    -- subTᴹ = subTᴹ' ?

    -- it won't reduce unless I give you a unit' as a first argument
    subTᴹ unit' {Γ}{E}{z}{A}  =
        tr-swap-Tyᴹ (ap (M._^^_ Γ) M.sub∙t ◾ M.^^∙t) _
        ◾
        (
          tr (λ Γ' → N.Ty (Conᴹ Γ')) (ap (M._^^_ Γ) M.sub∙t ◾ M.^^∙t) 
            (Tyᴹ (M.l-subT E (M.∙t (Γ M.▶ E)) z (M.tr-Ty (! M.^^∙t) A)))
        =⟨
          ap (tr (λ Γ' → N.Ty (Conᴹ Γ')) (ap (M._^^_ Γ) M.sub∙t ◾ M.^^∙t)) 
          subTᴹ-1
        ⟩
        _
        =⟨
          coe-∙2'
          (ap N.Ty (ap (λ Δ' → Conᴹ Γ N.^^ N.subTel (Tyᴹ E) Δ' (Tmᴹ z)) (! ∙t▶ᴹ)))
          (ap N.Ty (! (^^ᴹ ◾ ap (N._^^_ (Conᴹ Γ)) subTelᴹ)))
          (ap (λ Γ' → N.Ty (Conᴹ Γ')) (ap (M._^^_ Γ) M.sub∙t ◾ M.^^∙t))
          (N.l-subT (Tyᴹ E) (N.∙t (Conᴹ Γ N.▶ Tyᴹ E)) (Tmᴹ z)
            (N.tr-Ty (! N.^^∙t) (N.tr-Ty ▶ᴹ (Tyᴹ A))))

        ⟩

        _ 

        =⟨
          uip-coe 
          (
            ap N.Ty (ap (λ Δ' → Conᴹ Γ N.^^ N.subTel (Tyᴹ E) Δ' (Tmᴹ z)) (! ∙t▶ᴹ))
            ◾
            ap N.Ty (! (^^ᴹ ◾ ap (N._^^_ (Conᴹ Γ)) subTelᴹ))
            ◾
            ap (λ Γ' → N.Ty (Conᴹ Γ')) (ap (M._^^_ Γ) M.sub∙t ◾ M.^^∙t)
          )
          (
          ap N.Ty (ap (N._^^_ (Conᴹ Γ)) N.sub∙t ◾ N.^^∙t)
          )

        ⟩
        N.tr-Ty (ap (N._^^_ (Conᴹ Γ)) N.sub∙t ◾ N.^^∙t)
          (N.l-subT (Tyᴹ E) (N.∙t (Conᴹ Γ N.▶ Tyᴹ E)) (Tmᴹ z)
          (N.tr-Ty (! N.^^∙t) (N.tr-Ty ▶ᴹ (Tyᴹ A))))
        ∎)



    record ModelMorphism2 : Set (lmax ℓ₁ ℓ₂)  where
      field

        V0ᴹ : ∀ {Γ}{A : M.Ty Γ} → Tmᴹ (M.V0 _ A) ≡
          N.tr2-Tm⁻¹ {Δ = N._▶_ (Conᴹ Γ) (Tyᴹ A)} ▶ᴹ
          (N.tr-Tm ( ! (transpose-tr _ _ wkTᴹ)) (N.V0 (Conᴹ Γ) (Tyᴹ A)))

        appᴹ : ∀ (top : ⊤'){Γ}{A : M.Tm _ (M.U Γ)}{B}{t}{u} →
          Tmᴹ (M.app _ A B t u) ≡
          -- tr o N.l-subT o tr o tr o Tyᴹ ≡ Tyᴹ o tr o M.l-subT o trj
          -- this ∙' is to ease iniappᴹ
          N.tr-Tm (! (subTᴹ top ∙'  (_
          =⟨
            J
              (λ EL e →
                N.subT (Conᴹ Γ) (Tyᴹ (M.El Γ A)) (Tmᴹ u) (N.tr-Ty ▶ᴹ (Tyᴹ B)) ≡
                N.subT (Conᴹ Γ) EL (N.tr-Tm e (Tmᴹ u))
                (N.tr-Ty (▶ᴹ ∙' ap (N._▶_ (Conᴹ Γ)) e) (Tyᴹ B)))
              refl
              Elᴹ
          ⟩
            N.subT (Conᴹ Γ) (N.El (Conᴹ Γ) (N.tr-Tm Uᴹ (Tmᴹ A)))
            (N.tr-Tm Elᴹ (Tmᴹ u))
            (N.tr-Ty (▶ᴹ ∙' ap (N._▶_ _) Elᴹ) (Tyᴹ B)) ∎)
            )
            )
          (N.app (Conᴹ Γ)
          (N.tr-Tm Uᴹ (Tmᴹ A))
          (N.tr-Ty (▶ᴹ ∙' ap (N._▶_ _) Elᴹ) (Tyᴹ B))
          (N.tr-Tm ΠΠᴹ (Tmᴹ t))
          (N.tr-Tm Elᴹ (Tmᴹ u)))

