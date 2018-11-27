{- unicity of the initial morphism -}

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
import Model

module ModelMorUnique {l} where
  open import ModelMorRewRel {l}
  open import Relation {l}
  open import RelationProp {l}
  open import RelationInhabit {l}
  open import InitialMorphism1 {l}
  open import ModelMorRew {l}

  module MOR1 = ModelMorphism1 iniMor1
  module MOR2 = ModelMorphism1 mor1


  Con= : ∀ (Γ : S1.Con) → MOR1.Conᴹ Γ ≡ MOR2.Conᴹ Γ

  Con= Γ = Con~path Γ (ΣmorCon Γ) _ (Conᴹ~ (₂ Γ))

  Ty= : ∀ (Γ : S1.Con)(A : S1.Ty Γ) →
    pair {B = MOR1.N.Ty} (MOR1.Conᴹ Γ) (MOR1.Tyᴹ {Γ = Γ} A) ≡
    (MOR2.Conᴹ Γ , MOR2.Tyᴹ {Γ = Γ} A)
  Ty= Γ A =
    ConTy~path (ΣmorCon Γ) (₂ Γ) _
      (Conᴹ~ (₂ Γ))
      (ΣmorTy {Γ = Γ} A) 
      _
      (Tyᴹ~ Γ (₂ A))
  
  -- TODO: move to Relation
  ConTyTm~path : ∀ {Γp Γw} (Γm : Σ _ (Con~' Γp Γw))  Γm' (Γr' : Con~' Γp Γw Γm')
    {Ap Aw} (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm))) -- Aw'
    Am'
    → Ty~' Γp Ap Aw Γm' Am' →
    ∀ {tp} {tw} (tm : Σ _ (Tm~' Γp Ap tp tw (₁ Γm)(₁ Am)))
    tm'
    → Tm~' Γp Ap tp tw  Γm' Am' tm'
    →   ((₁ Γm , ₁ Am) , ₁ tm)≡ ((Γm' , Am') , tm')

  ConTyTm~path {Γp}{Γw}Γm  Γm' Γr' {Ap}{Aw} Am Am' Ar' {tp}{tw}tm tm' tr'
    = aux (Γm' , Γr') (Am' , Ar')(tm' , tr')
    where 
      aux :
        (Γm' : Σ _ (Con~' Γp Γw))
        (Am' : Σ _ (Ty~' Γp _ Aw (₁ Γm')))
        (tm' : Σ _ (Tm~' Γp _ _ tw (₁ Γm')(₁ Am')))
        →
        ((₁ Γm , ₁ Am) , ₁ tm) ≡ ((₁ Γm' , ₁ Am') , ₁ tm')
      aux Γm' Am' tm'
       rewrite prop-has-all-paths Γm' Γm
       | prop-has-all-paths Am' Am
       | prop-path (TmP _ _ _ tw (₁ Γm) (₁ Am)) tm' tm
        = refl

  Tm= : ∀ (Γ : S1.Con)(A : S1.Ty Γ) (t : S1.Tm Γ A) →
    pair
      {A =  Σ _  MOR1.N.Ty }
       {B = λ x → MOR1.N.Tm (₁ x) (₂ x)}
       ( pair {B = MOR1.N.Ty} (MOR1.Conᴹ Γ) (MOR1.Tyᴹ {Γ = Γ} A) ) ( MOR1.Tmᴹ {Γ = Γ} {A} t) ≡
      ( (MOR2.Conᴹ Γ , MOR2.Tyᴹ {Γ = Γ} A) ,  MOR2.Tmᴹ {Γ = Γ} {A} t)
  Tm= Γ A t =
    ConTyTm~path
      (ΣmorCon Γ) _ (Conᴹ~ (₂ Γ))
      (ΣmorTy {Γ = Γ} A)  _ (Tyᴹ~ Γ (₂ A))
      {tw = ₂ t} (ΣmorTm {Γ = Γ}{A} t) _ (Tmᴹ~ Γ A (₂ t))
