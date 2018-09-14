{-# OPTIONS  --rewriting  #-}

-- proof that is 
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
import Model
open import Syntax

module RelationProp {α} where
  open import Relation {α}
  import monlib

    {-


The relation is almost functional (at most 1 inhabitant)

-}
  -- needs UIP or that M.Con & M.Ty are hset
  -- this is needed for one of the case to that liftV~
  instance 
    ConP : ∀ Γp Γw → is-prop (Σ _ (Con~' Γp Γw))
    TelescopeP : ∀ (Γp : Conp) Δp Δw Γm → is-prop (Σ _ (Telescope~ {Γp} Δp Δw Γm))
    TyP : ∀ Γp Ap Aw Γm → is-prop (Σ _ (Ty~' Γp Ap Aw Γm))
    TmP : ∀ Γp Ap tp tw Γm Am → is-prop (Σ _ (Tm~' Γp Ap tp tw Γm Am))
    VarP : ∀ Γp Ap xp xw Γm Am → is-prop (Σ _ (Var~' Γp Ap xp xw Γm Am))

    ConP .∙p ∙w = pathto-is-prop M.∙

    ConP .(_ ▶p _) (▶w Γw Aw) =

      equiv-preserves-level
      -- ((Σ-emap-r λ Γm → {!? ∘e Σ₁-×-comm!} ∘e Σ₁-×-comm) ⁻¹)
      (Σ₁-×-comm   ∘e
      -- -- this superfluous ∘e makes Σ₁-×-comm automatically infer its arguments..
      Σ-emap-r λ Γm → Σ₁-×-comm ∘e ide _)
        {{helper }}
      where
      helper : is-prop  (Σ (Σ M.Con (Con~' _ Γw))
        (λ z →
        Σ (Σ (M.Ty (₁ z)) (Ty~' _ _ Aw (₁ z)))
        (λ a → Σ M.Con (λ z₁ → z₁ ≡ (₁ z M.▶ ₁ a)))))
      helper = 
        Σ-level (ConP _ Γw)
          λ Γm → Σ-level (TyP _ _ Aw (₁ Γm))
          λ Am → it


    TelescopeP Γp ∙p Δw Γm = it
    TelescopeP Γp (Δp ▶p x) (▶w Δw Aw) Γm =
      equiv-preserves-level
      ( Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e ide _)
      {{ Σ-level it
        λ Δm →
        Σ-level (TyP _ _ Aw (Γm M.^^ ₁ Δm))
        -- Σ-level it
        λ Am → it }}

    TyP Γp .Up (Uw .Γp Γw) Γm = it
    TyP Γp .(ΠΠp (Elp _) _) (Πw Γw Aw Aw₁) Γm =
     equiv-preserves-level
     (
     Σ₁-×-comm ∘e Σ-emap-r λ Am' →
     Σ₁-×-comm ∘e Σ-emap-r λ Bm' →
      ide _
     )
     {{ Σ-level (TmP _ _ _ Aw Γm (M.U Γm)) λ Am' →
     Σ-level (TyP _ _ Aw₁ (Γm M.▶ M.El Γm (₁ Am'))) λ Bm' →
         it
     
     }}

    TyP Γp .(Elp _) (Elw Γw aw) Γm =
      equiv-preserves-level Σ₁-×-comm 
      {{ Σ-level (TmP _ _ _ aw Γm (M.U Γm)) λ Am' →
        it
        }}

    TmP Γp Ap .(V _) (vw xw) Γm Am = VarP _ _ _ xw Γm Am

    TmP Γp .(l-subT 0 u Bp) .(app t u) (appw .Γp Γw ap₁ tw Bp Bw t tw₁ u tw₂) Γm Am =
      
      equiv-preserves-level
      (
        Σ₁-×-comm ∘e Σ-emap-r λ Am' →
        Σ₁-×-comm ∘e Σ-emap-r λ Bm' →
        Σ₁-×-comm ∘e Σ-emap-r λ tm' →
        Σ₁-×-comm ∘e Σ-emap-r λ um' →
        ide _
      )
      {{ Σ-level (TmP _ _ _ tw Γm (M.U Γm)) λ Am' →
        Σ-level ((TyP _ _ Bw _)) λ Bm' →
        Σ-level (TmP _ _ _ tw₁ _ _) λ tm' →
        Σ-level (TmP _ _ _ tw₂ _ _) λ um' →
         Σpathto-is-prop Am _
      
      }}
      

    VarP .(Γp ▶p Ap) .(liftT 0 Ap) .0 (V0w Γp Γw Ap Aw) Γm Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
       ide _)
      {{ Σ-level it λ Γm' →
      Σ-level (TyP _ _ Aw (₁ Γm')) λ Am' →
      Σpathto-is-prop (Γm , Am) _
      }}

    VarP .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Γm Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
      Σ₁-×-comm ∘e Σ-emap-r λ Bm →
      Σ₁-×-comm ∘e Σ-emap-r λ xm →
      ide _
      )
      {{ Σ-level it λ Γm' →
      Σ-level (TyP _ _ Aw (₁ Γm')) λ Am' →
      Σ-level (TyP _ _ Bw (₁ Γm')) λ Bm' →
      Σ-level (VarP _ _ _ xw (₁ Γm')(₁ Bm')) λ xm' →
      Σpathto-is-prop (Γm , Am) _
      
      }}
