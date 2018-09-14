{-# OPTIONS  --rewriting --allow-unsolved-metas #-}

-- proof that is 
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
import Model
open import Syntax

module RelSubst {α} where
  open import Relation {α}
  open import RelationProp {α}

{-


Preservation of the relation by substitution


-}
-- do I need such a general statment, can I do it only when A = El a ?
-- I don't think assuming A = El a makes the proof simpler anyway
-- Do I need to enforce that Γm is related ?
  subT~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) →
      ∀{Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
      {Bp} Bw (Bm : (Σ _ (Ty~' (Γp ▶p Ap) Bp Bw (₁ Γm M.▶ ₁ Am) )))
      {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
      (Bsw : Tyw Γp (subT up Bp) )
      → Ty~' Γp (subT up Bp) Bsw (₁ Γm)
        (M.subT (₁ Γm)(₁ Am) (₁ um)  (₁ Bm))
  subT~ = {!!}

