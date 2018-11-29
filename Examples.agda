{-# OPTIONS --rewriting #-}
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import ModelRecord
open import monlib
open import Syntax
-- open import Model
open import SyntaxIsRecord
open import SyntaxIsRecord2

module Examples  where
  -- module S1 = Model1 syntax1
  -- module S1 = Model
  test : (S1.U (S1.∙ S1.▶ S1.U S1.∙)) ≡ S1.liftT S1.∙ (S1.∙t S1.∙) (S1.U S1.∙) (S1.U S1.∙)
  test = {!S1.liftU!}

  -- simple arrow
  S→ : (Γ : S1.Con) (A : S1.Tm Γ (S1.U Γ))(B : S1.Ty Γ) → S1.Ty Γ
  S→ Γ A B = S1.ΠΠ Γ A (S1.wkT Γ (S1.El Γ A) B)

 --non dependent application
  Sa : (Γ : S1.Con) (A : S1.Tm Γ (S1.U Γ))(B : S1.Ty Γ)
      (t : S1.Tm Γ (S→ Γ A B))(u : S1.Tm Γ (S1.El Γ A)) → S1.Tm Γ B
  Sa Γ A B t u
    = 
      tr (λ B' → Σ Tmp (Tmw (₁ Γ) B'))
      (Syntax.subT-wkT (₁ B) (₁ u))
      (S1.app Γ A (S1.wkT Γ (S1.El Γ A) B) t u )
      


  C-U = S1.∙ S1.▶ S1.U S1.∙

  t-V0 = (S1.V0  S1.∙ (S1.U S1.∙)) 

  T-Π : S1.Ty C-U
  T-Π = S→ C-U  t-V0 (S1.U C-U)
  -- S1.ΠΠ C-U
  --   t-V0
  --   (S1.U (C-U S1.▶ (S1.El C-U t-V0)))
  

-- A: U, B : A -> U , ∙ : A , ▶ : (Γ : A) → B Γ → A , u : (Γ:A) → B Γ , el (Γ : A) →
  ex1 : S1.Con 
  ex1 =
    U,Π,El
    S1.▶ T-▶
    S1.▶ T-u
    S1.▶ T-el
    where
      U,Π = C-U S1.▶ T-Π
      U,Π⊢Π = S1.wkT C-U T-Π T-Π
      U,Π⊢A = (S1.wkt C-U T-Π (S1.U C-U) t-V0 )
      U,Π,El = U,Π S1.▶ S1.El U,Π U,Π⊢A
      U,Π,El⊢Π = S1.wkT U,Π (S1.El U,Π U,Π⊢A) U,Π⊢Π
      U,Π,El⊢A = S1.wkt U,Π (S1.El U,Π U,Π⊢A) (S1.U U,Π) U,Π⊢A
      U,Π,El,A = U,Π,El S1.▶ (S1.El U,Π,El U,Π,El⊢A)
      U,Π,El,A⊢A = S1.wkt U,Π,El (S1.El U,Π,El U,Π,El⊢A) (S1.U U,Π,El) U,Π,El⊢A
      U,Π,El⊢B = S1.wkt U,Π (S1.El U,Π U,Π⊢A) U,Π⊢Π (S1.V0 C-U T-Π)
      U,Π,El,A⊢B = S1.wkt U,Π,El (S1.El U,Π,El U,Π,El⊢A) U,Π,El⊢Π U,Π,El⊢B
      T-▶' = (S→ U,Π,El,A
        (Sa U,Π,El,A U,Π,El,A⊢A (S1.U U,Π,El,A) U,Π,El,A⊢B
        (S1.V0 U,Π,El (S1.El U,Π,El U,Π,El⊢A)))
        (S1.El U,Π,El,A U,Π,El,A⊢A))
      T-▶ = 
        S1.ΠΠ U,Π,El U,Π,El⊢A T-▶'
      C-▶ = U,Π,El S1.▶ T-▶
      ▶⊢A = S1.wkt U,Π,El T-▶ (S1.U U,Π,El) U,Π,El⊢A
      ▶⊢B = S1.wkt U,Π,El T-▶ U,Π,El⊢Π  U,Π,El⊢B
      ▶,A = C-▶ S1.▶ (S1.El C-▶ ▶⊢A)
      ▶,A⊢A = S1.wkt C-▶ (S1.El C-▶  ▶⊢A) (S1.U C-▶) ▶⊢A
      ▶⊢Π = S1.wkT U,Π,El T-▶ U,Π,El⊢Π
      ▶,A⊢B = S1.wkt C-▶ (S1.El C-▶  ▶⊢A) ▶⊢Π ▶⊢B
      T-u = S1.ΠΠ C-▶ ▶⊢A (S1.El ▶,A (Sa ▶,A ▶,A⊢A (S1.U ▶,A) ▶,A⊢B (S1.V0 C-▶ (S1.El C-▶ ▶⊢A) )))
      C-u = C-▶ S1.▶ T-u
      u⊢A = S1.wkt C-▶ T-u (S1.U C-▶) ▶⊢A
      u⊢B = S1.wkt C-▶ T-u ▶⊢Π  ▶⊢B
      u,A = C-u S1.▶ (S1.El C-u u⊢A)
      u,A⊢A = S1.wkt C-u (S1.El C-u  u⊢A) (S1.U C-u) u⊢A
      u,A,A = u,A S1.▶ (S1.El u,A u,A⊢A)
      u,A,A⊢A = S1.wkt u,A (S1.El u,A  u,A⊢A) (S1.U u,A) u,A⊢A
      u⊢Π = S1.wkT C-▶ T-u ▶⊢Π
      u,A⊢Π = S1.wkT C-u (S1.El C-u  u⊢A) u⊢Π
      u,A⊢B = S1.wkt C-u (S1.El C-u  u⊢A) u⊢Π u⊢B
      u,A,A⊢B = S1.wkt u,A (S1.El u,A  u,A⊢A) u,A⊢Π u,A⊢B
      T-el  = S1.ΠΠ C-u u⊢A
         (S1.El u,A
           (Sa u,A u,A⊢A (S1.U u,A) u,A⊢B
             ▶ΓuΓ
             ))
        where
          ▶⊢T▶ = S1.wkT U,Π,El T-▶ T-▶
          u⊢▶ = S1.wkt C-▶ T-u ▶⊢T▶ (S1.V0 U,Π,El T-▶)
          u⊢T▶ = S1.wkT C-▶ T-u ▶⊢T▶
          u⊢Tu = S1.wkT C-▶ T-u T-u
          -- u⊢Tu = S1.wkT C-▶ T-u T-u
          u,A⊢▶ = S1.wkt C-u (S1.El C-u u⊢A) u⊢T▶ u⊢▶
          u,A⊢u = S1.wkt C-u (S1.El C-u u⊢A) u⊢Tu (S1.V0 C-▶ T-u )
          -- (S1.V0 U,Π,El T-▶)
          T-▶'' =
             (S→ u,A
            (Sa u,A u,A⊢A (S1.U u,A) u,A⊢B
            (S1.V0 C-u (S1.El C-u u⊢A)))
            (S1.El u,A u,A⊢A))
          T-▶''' =
            (S→ u,A,A
            (Sa u,A,A u,A,A⊢A (S1.U u,A,A) u,A,A⊢B
            (S1.V0 u,A (S1.El u,A u,A⊢A)))
            (S1.El u,A,A u,A,A⊢A))
          u,A,A⊢T-▶'' : S1.Ty u,A,A
          u,A,A⊢T-▶'' = S1.wkT u,A (S1.El u,A u,A⊢A) T-▶''
          ▶ΓuΓ = Sa u,A
            -- ici je mets le type de ▶ Γ qui est B Γ 
            (Sa u,A u,A⊢A (S1.U u,A) u,A⊢B (S1.V0 C-u (S1.El C-u u⊢A)))
            (S1.El u,A u,A⊢A)

            (S1.app u,A u,A⊢A 
              -- u,A,A⊢T-▶''
              -- I can't write it the right way..
              T-▶'''
              
              -- (_ , Πw (₂ u,A,A)
              --   {!appw!}
              --   {!!})
              -- ici c'est ▶ appliqué à Γ
              -- {! u,A⊢▶ !}
              u,A⊢▶
              (S1.V0 C-u (S1.El C-u u⊢A)))
            (S1.app u,A u,A⊢A
               (S1.El u,A,A
               -- c'est B Γ
                 (Sa u,A,A u,A,A⊢A (S1.U u,A,A) u,A,A⊢B (S1.V0 u,A (S1.El u,A u,A⊢A))) )
               u,A⊢u
               (S1.V0 C-u (S1.El C-u u⊢A))) -- S1.app u,A {!!} {!!} u,A⊢▶ {!!}

      -- T-u = S1.ΠΠ 

   
    -- (S1.wkt C-U T-Π (S1.U C-U))
  -- M.El _ {!M.V0!}
