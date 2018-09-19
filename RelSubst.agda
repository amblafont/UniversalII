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



  -- si Γ ⊢ u : A ~ Γm  ⊢ um  : Am
  --  et Γ , A ⊢ t : B avec t ~ tm, Bm
  -- alors Γ ⊢ u[t] : B[t] ~ um[tm], Bm[tm]
  subt~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) →
    ∀{Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
    {Bp} (Bm : M.Ty (₁ Γm M.▶ ₁ Am))
    {tp} tw (tm : (Σ _ (Tm~' (Γp ▶p Ap) Bp tp tw (₁ Γm M.▶ ₁ Am) Bm)))
    {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
    (tsw : Tmw Γp (subT up Bp) (subt up tp) )
    → Tm~' Γp (subT up Bp)(subt up tp) tsw (₁ Γm)
    (M.subT (₁ Γm)(₁ Am) (₁ um)  Bm)
    (M.subt (₁ Γm)(₁ Am) (₁ um)  Bm (₁ tm))


  -- subT~ {Γw} Γw Γm {Ap} Aw Am {Bp} Bw Bm {up} uw um Bsw = {!!}
  subT~ {.Γp} Γw Γm {Ap} Aw Am {.Up} (Uw .(Γp ▶p Ap) Γw₁) (.(Model.U (₁ Γm Model.▶ ₁ Am)) , refl) {up} uw um (Uw Γp Γw₂) = refl

  subT~ {Γp} Γw Γm {Ap} Aw Am {.(ΠΠp (Elp ap) Bp)} (Πw ΓAw {ap} aw {Bp} Bw) (.(Model.ΠΠ (₁ Γm Model.▶ ₁ Am) (₁ am) (₁ Bm)) , am , Bm , refl) {up} uw um (Πw Γw' Asw Bsw) =
    (_ , subt~ Γw Γm Aw Am (M.U _) aw am uw um Asw) ,
    ?

  --  Γ ▶ A ⊢ B : U   ~ Bm
  -- Γ ⊢ u : A   ~ um
  subT~ {Γp} Γw Γm {Ap} Aw Am {.(Elp Bp)} (Elw Γw₁ {Bp} Bw) (.(M.El (₁ Γm M.▶ ₁ Am) (₁ Bm)) , Bm , refl) {up} uw um (Elw Γw₂ aw₁) =
    (_ , subt~ Γw Γm Aw Am {Up} (M.U _) Bw Bm uw um aw₁) ,
      refl

  subt~ {Γp} Γw Γm {Ap} Aw Am {Bp} Bm {tp} tw tm {up} uw um tsw = {!!}
