-- In this file, we finish the proof that we have a morphism from the syntax to the postulated model
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import ModelRecord
open import monlib
open import Syntax
open import SyntaxIsRecord
open import SyntaxIsRecord2
open import ModelRewIsRecord
open import ModelRewIsRecord2
open import ModelMorphism
-- import Model
open import Relation
open import RelationProp
open import RelationInhabit
open import RelWeakening


module InitialMorphism2 {l}  where
  open import InitialMorphism1 {l}

  iniV0ᴹ : ∀ (Γ : S1.Con)(A : S1.Ty Γ) →
     -- morTm {Γ S1.▶ A}{S1.wkT Γ A A}(S1.V0 Γ A)
     -- {!refl {a = morTm {Γ S1.▶ A}{S1.wkT Γ A A}(S1.V0 Γ A)}  !}
     morTm {Γ S1.▶ A}{S1.wkT Γ A A}(S1.V0 Γ A)
     ≡
      -- MM.tr2-Tm⁻¹ refl
        (MM.tr-Tm (! (wkTᴹ syntax2 m2 iniMor1 {Γ = Γ}{A}{A}))
          (N.V0  (morCon Γ) (morTy {Γ} A)))
  -- use of uip
  iniV0ᴹ Γ A = ! (coe-! _ (N.V0  (morCon Γ) (morTy {Γ} A)))
    ◾ ap (λ x → coe x (N.V0 (morCon Γ) (morTy {Γ} A))) (uip _ _)


  iniappᴹ  :
    ∀ uu (Γ : S1.Con )
      (A : S1.Tm Γ (S1.U Γ))
      (B : S1.Ty (Γ S1.▶ (S1.El Γ A)))
      (t : S1.Tm Γ (S1.ΠΠ Γ A B))
      (u : S1.Tm Γ (S1.El Γ A))
      -- e-sub
      →  
        morTm {Γ} {S1.subT Γ (S1.El Γ A) u B}  (S1.app Γ A B t u)
        ≡
         
        MM.tr-Tm 
        (! (subTᴹ syntax2 m2 iniMor1 uu {Γ}{S1.El Γ A}{u}{B}))
        (MM.app (morCon Γ)
          (morTm {Γ} {S1.U Γ} A)
          (morTy {Γ S1.▶ (S1.El Γ A)} B)
          (morTm {Γ}{S1.ΠΠ Γ A B}t)
          (morTm {Γ}{S1.El Γ A} u))
        
        
        

  iniappᴹ uu Γ A B t u  =
    Tm~path' _ Γm _ sBm  tu tum
    _
    (Am , Bm , tm , um ,
      (pair= e-subT (from-transp! _ _ (transport-! (N.Tm (₁ Γm)) e-subT _))))
    where
      Γm = ΣmorCon Γ
      Am = ΣmorTm {Γ}{S1.U Γ} A
      El-A = S1.El Γ A
      Bm = ΣmorTy {Γ S1.▶ El-A} B
      tu = S1.app Γ A B t u
      tum = ΣmorTm {Γ} {S1.subT Γ El-A u B}  tu
      tm = ΣmorTm {Γ}{S1.ΠΠ Γ A B}t
      um = ΣmorTm {Γ}{El-A} u
      sB = S1.subT Γ (El-A) u B
      sBm = ΣmorTy {Γ} sB
      e-subT = subTᴹ syntax2 m2 iniMor1 uu {Γ}{S1.El Γ A}{u}{B}
      

  iniMor2 : ModelMorphism2 syntax2 (m2 {l}) iniMor1
  iniMor2 = record
   { V0ᴹ = λ {Γ}{A } → iniV0ᴹ Γ A ;
    appᴹ = λ uu {Γ}{A}{B}{t}{u} →  
      iniappᴹ uu Γ A B t u
    }
