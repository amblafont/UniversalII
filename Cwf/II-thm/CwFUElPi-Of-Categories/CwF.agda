{-
Paper: section 7.4

CwF structure on the category of strict categories.
-}

{-# OPTIONS --rewriting #-}

open import Level
module CwFUElPi-Of-Categories.CwF {α β : Level} where

open import StrictLib hiding (id; _∘_)

open import CwFUElPi-Of-Categories.Cats renaming (
  Cat         to Con ; mkCat         to mkCon ; mkCat≡         to mkCon≡;
  Functor     to Sub ; mkFunctor     to mkSub ; mkFunctor≡     to mkSub≡; mkFunctor≃     to mkSub≃;
  DispCat     to Ty  ; mkDispCat     to mkTy  ; mkDispCat≡     to mkTy≡ ; mkDispCat≃     to mkTy≃;
  SectionDisp to Tm  ; mkSectionDisp to mkTm  ; mkSectionDisp≡ to mkTm≡ ; mkSectionDisp≃ to mkTm≃;
  Id to idₛ; Comp to _∘ₛ_; Idl to idlₛ; Idr to idrₛ; Ass to assₛ)
  public

-- Total categories
infixl 5 _▶_
_▶_ : ∀ Γ → Ty {α}{β} Γ → Con {α}{β}
Γ ▶ A = record
  { Obj = Σ Γ.Obj A.Obj
  ; _⇒_ = λ {(i , ii) (j , jj) → Σ (i Γ.⇒ j) λ f → ii A.⇒[ f ] jj}
  ; id  = Γ.id , A.id
  ; _∘_ = λ {(f , ff) (g , gg) → (f Γ.∘ g) , ff A.∘ gg}
  ; idl = ,≡≃ Γ.idl A.idl
  ; idr = ,≡≃ Γ.idr A.idr
  ; ass = ,≡≃ Γ.ass A.ass }
  where module A = Ty A; module Γ = Con Γ

-- singleton category
∙ : Con {α}{β}
∙ = record
  { Obj = Lift ⊤
  ; _⇒_ = λ _ _ → Lift ⊤
  ; id  = lift tt
  ; _∘_ = λ _ _ → lift tt
  ; idl = refl
  ; idr = refl
  ; ass = refl }

-- unique morphism into singleton category
ε : {Γ : Con {α}{β}} → Sub Γ ∙
ε {Γ} = mkSub (λ _ → lift tt) (λ _ → lift tt) refl refl

abstract
  εη : ∀ {Γ : Con {α}{β}}{σ : Sub Γ ∙} → σ ≡ ε
  εη {Γ}{σ} = mkSub≡ (λ _ → refl) (λ _ _ _ → refl̃)

-- "reindexing", (type substitution)
infixl 7 _[_]T
_[_]T : {Γ Δ : Con {α}{β}}(A : Ty Δ)(σ : Sub Γ Δ) → Ty Γ
_[_]T {Γ}{Δ} A σ = record
  { Obj    = λ i → A.Obj (σ.Obj i)
  ; _⇒[_]_ = λ ii f jj → ii A.⇒[ σ.⇒ f ] jj
  ; id     = λ {i}{ii} → coe ((λ f → ii A.⇒[ f ] ii) & (σ.id ⁻¹)) A.id
  ; _∘_    = λ {i}{j}{k}{f}{g}{ii}{jj}{kk} ff gg → coe ((λ f → ii A.⇒[ f ] kk) & (σ.∘ ⁻¹)) (ff A.∘ gg)
  ; idl    = λ {i}{j}{f}{ii}{jj}{ff} →
                 uncoe ((λ f₁ → ii A.⇒[ f₁ ] jj) & (σ.∘ ⁻¹)) _
               ◾̃ ap2̃̃ (λ f (ff' : jj A.⇒[ f ] jj) → ff' A.∘ ff)
                     σ.id (uncoe ((λ f₁ → jj A.⇒[ f₁ ] jj) & (σ.id ⁻¹)) A.id)
               ◾̃ A.idl
  ; idr    = λ {i}{j}{f}{ii}{jj}{ff} →
                 uncoe (((λ f₁ → ii A.⇒[ f₁ ] jj) & (σ.∘ ⁻¹))) _
               ◾̃ ap2̃̃ (λ f (ff' : ii A.⇒[ f ] ii) → ff A.∘ ff')
                     σ.id (uncoe ((λ f₁ → ii A.⇒[ f₁ ] ii) & (σ.id ⁻¹)) A.id)
               ◾̃ A.idr
  ; ass    = λ {i}{j}{k}{l}{f}{g}{h}{ii}{jj}{kk}{ll}{ff}{gg}{hh} →
                 uncoe ((λ f₁ → ii A.⇒[ f₁ ] ll) & (σ.∘ ⁻¹)) _
               ◾̃ ap2̃̃ (λ f (ff' : ii A.⇒[ f ] kk) → ff A.∘ ff') σ.∘
                     (uncoe ((λ f₁ → ii A.⇒[ f₁ ] kk) & (σ.∘ ⁻¹)) (gg A.∘ hh))
               ◾̃ A.ass
               ◾̃ ap2̃̃ (λ f (ff' : jj A.⇒[ f ] ll) → ff' A.∘ hh)
                     σ.∘ (uncoe ((λ f₁ → jj A.⇒[ f₁ ] ll) & (σ.∘ ⁻¹)) (ff A.∘ gg)) ⁻¹̃
               ◾̃ uncoe ((λ f₁ → ii A.⇒[ f₁ ] ll) & (σ.∘ ⁻¹)) _ ⁻¹̃}
  where module A = Ty A; module σ = Sub σ

abstract
  [id]T : ∀{Γ}{A : Ty Γ} → A [ idₛ ]T ≡ A
  [id]T {Γ}{A} = mkTy≡
    (λ _ → refl)
    (λ {refl̃ refl̃ → refl})
    (λ {refl̃ → refl̃})
    (λ {refl̃ refl̃ refl̃ refl̃ refl̃ → refl̃})
    where module A = Ty A; module Γ = Con Γ

abstract
  [][]T : ∀{Γ Δ Σ}(A : Ty Σ)(σ : Sub Γ Δ)(δ : Sub Δ Σ)
          → A [ δ ]T [ σ ]T ≡ A [ δ ∘ₛ σ ]T
  [][]T {Γ}{Δ}{Σ} A σ δ = mkTy≡
    (λ i → refl)
    (λ {refl̃ refl̃ → refl})
    (λ { {i}{ii₀}{ii₀} refl̃ →
            uncoe ((λ f → ii₀ A.⇒[ δ.⇒ f ] ii₀) & (σ.id ⁻¹)) _
          ◾̃ uncoe ((λ f → ii₀ A.⇒[ f ] ii₀) & (δ.id ⁻¹)) A.id
          ◾̃ uncoe ((λ f → ii₀ A.⇒[ f ] ii₀) & ((δ.⇒ & σ.id ◾ δ.id) ⁻¹)) A.id ⁻¹̃})
    (λ { {i} {j} {k} {f} {g} {ii₀} {.ii₀} refl̃
         {jj₀} {.jj₀} refl̃ {kk₀} {.kk₀} refl̃
         {ff₀} {.ff₀} refl̃ {gg₀} {.gg₀} refl̃ →
            uncoe ((λ f → ii₀ A.⇒[ δ.⇒ f ] kk₀) & (σ.∘ ⁻¹)) _
          ◾̃ uncoe ((λ f → ii₀ A.⇒[ f ] kk₀) & (δ.∘ ⁻¹)) (ff₀ A.∘ gg₀)
          ◾̃ uncoe ((λ f → ii₀ A.⇒[ f ] kk₀) & ((δ.⇒ & σ.∘ ◾ δ.∘) ⁻¹)) _ ⁻¹̃})
    where module σ = Sub σ; module δ = Sub δ; module A = Ty A
          module Γ = Con Γ; module Δ = Con Δ

infixl 5 _,s_
_,s_ : ∀{Γ Δ A}(σ : Sub Γ Δ) → Tm {γ = α}{β} Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,s_ {Γ}{Δ}{A} σ t = mkSub
  (λ i → (σ.Obj i) , (t.Obj i))
  (λ {i}{j} f → (σ.⇒ f) , (t.⇒ f))
  (λ {i} → ,≡≃ σ.id ((t.id ~)
                    ◾̃ uncoe ((λ f → t.Obj i A.⇒[ f ] t.Obj i) & (σ.id ⁻¹)) _))
  (λ {i}{j}{k}{f}{g} →
           ,≡≃ σ.∘ ((t.∘ ~)
                    ◾̃ uncoe ((λ f₁ → t.Obj i A.⇒[ f₁ ] t.Obj k) & (σ.∘ ⁻¹)) _))
  where module σ = Sub σ; module t = Tm t; module A = Ty A
        module Δ = Con Δ; module Γ = Con Γ

π₁ : ∀ Γ Δ (A : Ty Δ) → Sub {α}{β} Γ (Δ ▶ A) → Sub Γ Δ
π₁ Γ Δ A σ = mkSub (λ i → ₁ (σ.Obj i)) (λ f → ₁ (σ.⇒ f)) (₁ & σ.id) (₁ & σ.∘)
  where module σ = Sub σ

infixl 8 _[_]t
_[_]t : ∀{Γ : Con{α}{β}}{Δ}{A : Ty Δ}
        → Tm {γ = α}{β} Δ A → (σ : Sub Γ Δ) → Tm {γ = α}{β} Γ (A [ σ ]T)
_[_]t {Γ}{Δ}{A} t σ = mkTm
  (λ i → t.Obj (σ.Obj i))
  (λ f → t.⇒ (σ.⇒ f))
  (λ {i} → uñ (ap̃̃ t.⇒ σ.id
            ◾̃ (t.id ~)
            ◾̃ uncoe ((λ f → t.Obj (σ.Obj i) A.⇒[ f ] t.Obj (σ.Obj i)) & (σ.id ⁻¹)) _ ⁻¹̃))
  (λ {i}{j}{k}{f}{g} →
           uñ (ap̃̃ t.⇒ σ.∘
            ◾̃ (t.∘ ~)
            ◾̃ uncoe ((λ f₁ → t.Obj (σ.Obj i) A.⇒[ f₁ ] t.Obj (σ.Obj k)) & (σ.∘ ⁻¹)) _ ⁻¹̃))
  where module σ = Sub σ; module t = Tm t; module A = Ty A
        module Δ = Con Δ; module Γ = Con Γ

π₂ : ∀ Γ Δ (A : Ty Δ)(σ : Sub Γ (Δ ▶ A)) → Tm {γ = α}{β} Γ (A [ π₁ Γ Δ A σ ]T)
π₂ Γ Δ A σ = mkTm
  (λ i → ₂ (σ.Obj i))
  (λ {i}{j} f → ₂ (σ.⇒ f))
  (λ {i} → uñ (ap̃̃ ₂ (σ.id {i})
             ◾̃ uncoe ((λ f → ₂ (σ.Obj i) A.⇒[ f ] ₂ (σ.Obj i)) & (Sub.id (π₁ Γ Δ A σ) ⁻¹)) _ ⁻¹̃))
  (λ {i}{j}{k}{f}{g} →
           uñ (ap̃̃ ₂ σ.∘
             ◾̃ uncoe ((λ f₁ → ₂ (σ.Obj i) A.⇒[ f₁ ] ₂ (σ.Obj k)) & (₁ & σ.∘ ⁻¹)) _ ⁻¹̃))
  where module σ = Sub σ; module A = Ty A; module Δ = Con Δ; module Γ = Con Γ


abstract
  π₁β : ∀ Γ Δ (A : Ty Δ) (σ : Sub Γ Δ)(a : Tm Γ (A [ σ ]T))
          → (π₁ Γ Δ A (σ ,s a)) ≡ σ
  π₁β Γ Δ A σ a = mkSub≡ (λ i → refl) (λ i j f → refl̃)
    where module σ = Sub σ; module a = Tm a; module A = Ty A
          module Δ = Con Δ; module Γ = Con Γ

  π₂β : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{a : Tm Γ (A [ σ ]T)}
          → (π₂ Γ Δ A (_,s_ {Γ}{Δ}{A} σ a)) ≃ a
  π₂β {Γ}{Δ}{A}{σ}{a} =
    mkTm≃
      refl ((A [_]T) & π₁β Γ Δ A σ a ~)
      (λ { {i₀}{i₀} refl̃ → refl̃})
      λ { {i₀}{i₀} refl̃ {j₀}{j₀} refl̃ {f₀}{f₀} refl̃ → refl̃}
    where module σ = Sub σ; module a = Tm a; module A = Ty A
          module Δ = Con Δ; module Γ = Con Γ

abstract
  πη : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ (Δ ▶ A)} → (π₁ Γ Δ A σ) ,s (π₂ Γ Δ A σ) ≡ σ
  πη {Γ}{Δ}{A}{σ} = mkSub≡ (λ i → refl) (λ i j f → refl̃)

  ,∘ : ∀{Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub {α}{β} Σ Γ}{A : Ty Δ}{t : Tm Γ (A [ δ ]T)}
        → (_∘ₛ_ {C = Σ}{Γ}{Δ ▶ A} (_,s_ {Γ} {Δ} {A} δ t) σ)
        ≡ (δ ∘ₛ σ) ,s (coe (Tm Σ & [][]T A σ δ) (t [ σ ]t))
  ,∘ {Γ}{Δ}{Σ}{δ}{σ}{A}{t} = mkSub≡
    (λ i → ,≡ refl (uñ (
      ap2̃̃ (λ (A : Ty Σ) (t : Tm {α}{β}{α}{β} Σ A) → Tm.Obj {D = A} t i)
        ([][]T A σ δ)
        (uncoe (Tm Σ & [][]T A σ δ) (t [ σ ]t) ⁻¹̃))))
    (λ i j f →
      ,≡≃' (λ a → A._⇒[_]_ &
                (uñ (ap2̃̃ (λ (A : Ty Σ) (t : Tm {α}{β}{α}{β} Σ A) → Tm.Obj {D = A} t i)
                    ([][]T A σ δ)
                    (uncoe (Tm Σ & [][]T A σ δ) (t [ σ ]t) ⁻¹̃)) ⁻¹)
              ⊗ refl
              ⊗ (uñ (ap2̃̃ (λ (A : Ty Σ) (t : Tm {α}{β}{α}{β} Σ A) → Tm.Obj {D = A} t j)
                    ([][]T A σ δ)
                    (uncoe (Tm Σ & [][]T A σ δ) (t [ σ ]t) ⁻¹̃)) ⁻¹))
           refl
           (ap2̃̃ (λ (A : Ty Σ) (t : Tm {α}{β}{α}{β} Σ A) → Tm.⇒ {D = A} t f)
                 ([][]T A σ δ ⁻¹)
                 (uncoe (Tm Σ & [][]T A σ δ) (t [ σ ]t))) ⁻¹̃)
    where module σ = Sub σ; module t = Tm t; module A = Ty A
          module Δ = Con Δ; module Γ = Con Γ; module Σ' = Con Σ

wk : ∀ {Γ A} → Sub (Γ ▶ A) Γ
wk {Γ}{A} = π₁ (Γ ▶ A) Γ A idₛ

vz : ∀ {Γ A} → Tm {γ = α}{β} (Γ ▶ A) (A [ wk ]T)
vz {Γ}{A} = π₂ (Γ ▶ A) Γ A idₛ

infixl 5 _^_
_^_ : {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ A [ σ ]T) (Δ ▶ A)
_^_ {Γ}{Δ} σ A = (σ ∘ₛ wk) ,s coe (Tm (Γ ▶ A [ σ ]T) & ([][]T A (wk{Γ}{A [ σ ]T}) σ))
                                  (vz {Γ}{A [ σ ]T})
