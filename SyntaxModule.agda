-- a definition of the syntax as a module where types depends only on the the context, not on the fact
-- that the context is well typed. The definition as a model (specified as a model) suffers from
-- bad implicit arugment inferences because to define the well formed types, I do not need to know
-- that the context is well typed

open import Level 
open import monlib
open import HoTT renaming (_==_ to _≡_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂ ; _∙_ to _◾_ )
  hiding ( _∘_ ; Π )
import Syntax as S
import Composition as C


module SyntaxModule   where

Con = ∃ S.Conw
Ty = λ Γ → ∃ (S.Tyw Γ)
Tm = λ Γ A → ∃ (S.Tmw Γ A)
Tel = λ Γ → ∃ (λ Δ → S.Conw (Γ S.^^ Δ))
-- we ask for the well formed nedd of Γ. See _∘_ to understand how it improves
-- the implicit inference engine
Sub = λ Γ Δ → ∃ (λ σ → S.Conw Γ × S.Subw Γ Δ σ)
g : ∀ {Γ}{Δ} → Sub Γ Δ → S.Conw Γ
g s = ₁ (₂ s)

-- ∙ : Con
-- ∙ = _ , S.
_▶_ : ∀ (Γ : Con) (A : Ty (₁ Γ)) → Con
Γ ▶ A = (₁ Γ S.▶p ₁ A) , (S.▶w (₂ Γ) (₂ A))

U : ∀ (Γ : Con) → Ty (₁ Γ)
U Γ = S.Up , S.Uw (₁ Γ) (₂ Γ)

-- ah, là je suis quand même obligé de demander que Γ soit bien typé..
El : ∀ (Γ : Con) (a : Tm (₁ Γ) S.Up) → Ty (₁ Γ)
El Γ a = (S.Elp (₁ a)) , S.Elw (₂ Γ) (₂ a)

_∘_ : ∀ {Y}{Γ}{Δ}(σ : Sub Γ Δ)(δ : Sub Y Γ) → Sub Y Δ
σ ∘ δ = _ , (g δ) , C.∘w  (₂ (₂ σ)) (g δ) (₂ (₂ δ))


-- avant, c'était ca. La partie  Conw de Y n'était pas inféré
-- _⊢_S∘_ : ∀ (Y : Con){Γ}{Δ}(σ : SSub Γ Δ)(δ : SSub (₁ Y) Γ) → SSub (₁ Y) Δ
-- Y ⊢ σ S∘ δ = _ , S.∘w (₂ σ) (₂ Y) (₂ δ)

_[_]T : ∀ {Γ }{Δ} (A : Ty Δ ) (σ : Sub Γ Δ) → Ty Γ
_[_]T  A σ   = _ , (S.Tywₛ (₂ A) (g σ) (₂ (₂ σ)))

_[_]t : ∀ {Γ}{Δ}{A} (t : Tm Δ A ) (σ : Sub Γ Δ) → Tm Γ ( A S.[ (₁ σ) ]T)
_[_]t  t σ   = _ , (S.Tmwₛ (₂ t) (g σ) (₂ (₂ σ)))

U[] : ∀ {Γ Δ : Con}{σ : Sub (₁ Γ) (₁ Δ)} → (U Δ [ σ ]T) ≡ U Γ
U[] = {!refl!}

π₁ : ∀ {Γ Δ A} (v  : Sub Γ (Δ S.▶p A)) → Sub Γ Δ
π₁ (_ , Γw , S.,sw Δw vw Aw tw) = _ , Γw , vw

π₂ : ∀ {Γ Δ A} (v  : Sub Γ (Δ S.▶p A)) → Tm  Γ (A S.[ ₁ ( (π₁ v)) ]T)
π₂ (_ , _ , S.,sw Δw vw Aw tw) = _ , tw

keep : ∀ {Γ Δ} (σ : Sub Γ Δ) (A : Ty Δ) → Sub (Γ S.▶p (₁ A S.[ (₁ ( σ)) ]T)) (Δ S.▶p (₁ A))
keep σ A = (S.keep (₁ σ)) , (S.▶w (g σ) (S.Tywₛ (₂ A) (g σ) (₂ (₂ σ)))) , (  
  (S.keepw (g σ) (₂ (₂ σ)) (₂ A)))

id : ∀ (Γ : Con) → Sub (₁ Γ)(₁ Γ)
id Γ = (C.idp S.∣ ₁ Γ ∣) , (₂ Γ) , (  (C.idpw (₂ Γ)))

-- idr : ∀ (Γ : Con) (Δ : Con) (σ : Sub (₁ Γ) (₁ Δ)) → (σ ∘ id Γ) ≡ σ
-- idr Γ Δ σ = propΣ= (C.idr (₂ (₂ σ)))

idl : ∀ {Γ : S.Conp} (Δ : Con) (σ : Sub Γ (₁ Δ)) → (id Δ ∘ σ) ≡ σ
idl Δ σ = propΣ= (C.idl (₂ (₂ σ)))

-- peut se déduire des autres égalités de CwF du papier
π₁∘ : ∀ {Γ }{A}{Δ}{Y} (σ : Sub Γ (Δ S.▶p A)) (δ : Sub Y Γ) → (π₁ σ ∘ δ) ≡ π₁ (σ ∘ δ) 
π₁∘ (.(_ :: _) , Γw , S.,sw Δw σw Aw tw) δ = refl

wk : ∀ (Γ : Con) (A : Ty (₁ Γ)) → (Sub (₁ (Γ ▶ A)) (₁ Γ))
wk Γ A = S.wkS (₁ (id Γ)) , S.▶w (₂ Γ) (₂ A) , S.wkSw (₂ (₂ (id Γ))) (₂ A)

-- celui la se déduit des autres
-- wk ∘ v ≡ π₁ v
wk∘ : ∀ {Γ}(Δ : Con)A (σ : Sub Γ (₁ (Δ  ▶  A))) → ((wk Δ A) ∘ σ) ≡ π₁ σ
wk∘ {Γ} Δ A  (.(_ :: _) , Γw , S.,sw Δw σw Aw tw)
  = propΣ= (C.wk∘:: _ _ _ ◾ C.idl  σw)
  -- {!!} ◾ ap π₁ (idl (Δ ▶ A) σ)
-- -}
