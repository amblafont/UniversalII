{-
Paper: section 7.4

Basic definitions and helpers about strict categories.
-}

module CwFUElPi-Of-Categories.Cats where

open import Level
open import StrictLib hiding (id; _∘_)

-- Categories
--------------------------------------------------------------------------------

module _ {α β : Level} where

  record Cat : Set (suc α ⊔ suc β) where
    constructor mkCat
    infixr 4 _⇒_
    infixr 5 _∘_
    field
      Obj  : Set α
      _⇒_  : Obj → Obj → Set β
      id   : ∀ {i} → i ⇒ i
      _∘_  : ∀ {i j k} → j ⇒ k → i ⇒ j → i ⇒ k
      idl  : ∀ {i j}{f : i ⇒ j} → id ∘ f ≡ f
      idr  : ∀ {i j}{f : i ⇒ j} → f ∘ id ≡ f
      ass  : ∀ {i j k l}{f : k ⇒ l}{g : j ⇒ k}{h : i ⇒ j} → f ∘ g ∘ h ≡ (f ∘ g) ∘ h
  -- open Cat public

  _ᵒᵖ : Cat → Cat
  C ᵒᵖ = record
    { Obj = C.Obj
    ; _⇒_ = λ i j → j C.⇒ i
    ; id  = C.id
    ; _∘_ = λ f g → g C.∘ f
    ; idl = C.idr
    ; idr = C.idl
    ; ass = C.ass ⁻¹ }
    where module C = Cat C

  abstract
    mkCat≡ :
      ∀ {Obj₀ Obj₁ : Set α}
          (Obj₂ : Obj₀ ≡ Obj₁)
        {_⇒₀_ : Obj₀ → Obj₀ → Set β}{_⇒₁_ : Obj₁ → Obj₁ → Set β}
          (⇒₂ : ∀ {i₀ i₁} (i₂ : i₀ ≃ i₁){j₀ j₁}(j₂ : j₀ ≃ j₁) → (i₀ ⇒₀ j₀) ≡ (i₁ ⇒₁ j₁))
        {id₀ : ∀ {i} → i ⇒₀ i}{id₁ : ∀ {i} → i ⇒₁ i}
          (id₂ : ∀ {i₀ i₁}(i₂ : i₀ ≃ i₁) → id₀ {i₀} ≃ id₁ {i₁})
        {_∘₀_ : ∀ {i j k} → j ⇒₀ k → i ⇒₀ j → i ⇒₀ k}
          {_∘₁_ : ∀ {i j k} → j ⇒₁ k → i ⇒₁ j → i ⇒₁ k}
            (∘₂ : ∀ {i₀ i₁} (i₂ : i₀ ≃ i₁) {j₀ j₁} (j₂ : j₀ ≃ j₁) {k₀ k₁} (k₂ : k₀ ≃ k₁)
                    {f₀ : j₀ ⇒₀ k₀}{f₁ : j₁ ⇒₁ k₁} (f₂ : f₀ ≃ f₁)
                    {g₀ : i₀ ⇒₀ j₀}{g₁ : i₁ ⇒₁ j₁} (g₂ : g₀ ≃ g₁)
                    → (f₀ ∘₀ g₀) ≃ (f₁ ∘₁ g₁))
        {idl₀ : ∀ {i j}{f : i ⇒₀ j} → (id₀ ∘₀ f) ≡ f}
        {idl₁ : ∀ {i j}{f : i ⇒₁ j} → (id₁ ∘₁ f) ≡ f}
        {idr₀ : ∀ {i j}{f : i ⇒₀ j} → (f ∘₀ id₀) ≡ f}
        {idr₁ : ∀ {i j}{f : i ⇒₁ j} → (f ∘₁ id₁) ≡ f}
        {ass₀ : ∀ {i j k l}{f : k ⇒₀ l}{g : j ⇒₀ k}{h : i ⇒₀ j}
                  → (f ∘₀ (g ∘₀ h)) ≡ ((f ∘₀ g) ∘₀ h)}
        {ass₁ : ∀ {i j k l}{f : k ⇒₁ l}{g : j ⇒₁ k}{h : i ⇒₁ j}
                  → (f ∘₁ (g ∘₁ h)) ≡ ((f ∘₁ g) ∘₁ h)}
      → mkCat Obj₀ _⇒₀_ id₀ _∘₀_ idl₀ idr₀ ass₀
      ≡ mkCat Obj₁ _⇒₁_ id₁ _∘₁_ idl₁ idr₁ ass₁
    mkCat≡ {Obj₀} refl {_⇒₀_} {_⇒₁_} ⇒₂ {id₀} {id₁} id₂ {_∘₀_} {_∘₁_} ∘₂
           {idl₀} {idl₁} {idr₀} {idr₁} {ass₀} {ass₁}
      with (_⇒₀_ ≡ _⇒₁_ ∋ ext λ i → ext λ j → ⇒₂ refl̃ refl̃)
        |  (λ {i} → id₀ {i}) ≃ (λ {i} → id₁ {i}) ∋ extĩ (λ i → id₂ refl̃)
        |  ((λ {i j k}(f : j ⇒₀ k)(g : i ⇒₀ j) → (f ∘₀ g)) ≃ (λ {i j k}(f : j ⇒₁ k)(g : i ⇒₁ j) → (f ∘₁ g))
             ∋ extĩ (λ i → extĩ (λ j → extĩ λ k
             → ext̃' (⇒₂ refl̃ refl̃) λ f₂ → ext̃' (⇒₂ refl̃ refl̃) λ g₂ → ∘₂ refl̃ refl̃ refl̃ f₂ g₂)))
    ... | refl | refl̃ | refl̃ =
        mkCat Obj₀ _⇒₀_ id₀ _∘₀_ & (exti λ _ → exti λ _ → exti λ _ → UIP _ _)
                                 ⊗ (exti λ _ → exti λ _ → exti λ _ → UIP _ _)
                                 ⊗ (exti λ _ → exti λ _ → exti λ _ → exti λ _
                                    → exti λ _ → exti λ _ → exti λ _ → UIP _ _)

-- Displayed categories
--------------------------------------------------------------------------------

  record DispCat (C : Cat) : Set (suc α ⊔ suc β) where
    constructor mkDispCat
    private module C = Cat C
    infixr 4 _⇒[_]_
    infixr 5 _∘_
    field
      Obj    : C.Obj → Set α
      _⇒[_]_ : ∀ {i j} → Obj i → i C.⇒ j → Obj j → Set β
      id     : ∀ {i}{ii : Obj i} → ii ⇒[ C.id {i} ] ii
      _∘_    : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j}{ii jj kk}
               → jj ⇒[ f ] kk → ii ⇒[ g ] jj
               → ii ⇒[ f C.∘ g ] kk
      idl    : ∀ {i j}{f : i C.⇒ j}{ii jj}{ff : ii ⇒[ f ] jj}
               → (id ∘ ff) ≃ ff
      idr    : ∀ {i j}{f : i C.⇒ j}{ii jj}{ff : ii ⇒[ f ] jj}
               → (ff ∘ id) ≃ ff
      ass    : ∀ {i j k l}{f : k C.⇒ l}{g : j C.⇒ k}{h : i C.⇒ j}
                 {ii jj kk ll}{ff : kk ⇒[ f ] ll}{gg : jj ⇒[ g ] kk}{hh : ii ⇒[ h ] jj}
               → (ff ∘ gg ∘ hh) ≃ (ff ∘ gg) ∘ hh
  -- open DispCat public


  abstract
    mkDispCat≃ :
        {C₀ C₁ : Cat} (C₂ : C₀ ≡ C₁) →
        let module C₀ = Cat C₀; module C₁ = Cat C₁ in
        {Obj₀    : C₀.Obj → Set α}
        {Obj₁    : C₁.Obj → Set α}
        (Obj₂    : ∀ {i₀ i₁} → i₀ ≃ i₁ → Obj₀ i₀ ≃ Obj₁ i₁)
        {_⇒[_]₀_ : ∀ {i j} → Obj₀ i → i C₀.⇒ j → Obj₀ j → Set β}
        {_⇒[_]₁_ : ∀ {i j} → Obj₁ i → i C₁.⇒ j → Obj₁ j → Set β}
        (_⇒[_]₂_ : ∀ {i₀ : C₀.Obj}{i₁ : C₁.Obj} → i₀ ≃ i₁ → ∀ {j₀ : C₀.Obj}{j₁ : C₁.Obj}
                   → j₀ ≃ j₁ → {ii₀ : Obj₀ i₀}{ii₁ : Obj₁ i₁} → ii₀ ≃ ii₁ → ∀ {f₀ f₁} → f₀ ≃ f₁ →
                   ∀ {jj₀ : Obj₀ j₀}{jj₁ : Obj₁ j₁} → jj₀ ≃ jj₁ → (ii₀ ⇒[ f₀ ]₀ jj₀) ≡ (ii₁ ⇒[ f₁ ]₁ jj₁))
        {id₀     : ∀ {i}{ii : Obj₀ i} → ii ⇒[ C₀.id {i} ]₀ ii}
        {id₁     : ∀ {i}{ii : Obj₁ i} → ii ⇒[ C₁.id {i} ]₁ ii}
        (id₂     : ∀ {i₀ i₁} → i₀ ≃ i₁ → ∀ {ii₀ ii₁} → ii₀ ≃ ii₁ → id₀ {i₀}{ii₀} ≃ id₁ {i₁}{ii₁})
        {_∘₀_    : ∀ {i j k}{f : j C₀.⇒ k}{g : i C₀.⇒ j}{ii jj kk}
                 → jj ⇒[ f ]₀ kk → ii ⇒[ g ]₀ jj
                 → ii ⇒[ f C₀.∘ g ]₀ kk}
        {_∘₁_    : ∀ {i j k}{f : j C₁.⇒ k}{g : i C₁.⇒ j}{ii jj kk}
                 → jj ⇒[ f ]₁ kk → ii ⇒[ g ]₁ jj
                 → ii ⇒[ f C₁.∘ g ]₁ kk}
        (∘₂      : ∀ {i₀ i₁} → i₀ ≃ i₁ → ∀ {j₀ j₁} → j₀ ≃ j₁ → ∀ {k₀ k₁} → k₀ ≃ k₁ → ∀ {f₀ f₁} → f₀ ≃ f₁
                   → ∀ {g₀ g₁} → g₀ ≃ g₁
                   → ∀ {ii₀ ii₁} → ii₀ ≃ ii₁ → ∀ {jj₀ jj₁} → jj₀ ≃ jj₁ → ∀ {kk₀ kk₁} → kk₀ ≃ kk₁
                   → ∀ {ff₀ ff₁} → ff₀ ≃ ff₁
                   → ∀ {gg₀ gg₁} → gg₀ ≃ gg₁
                   → _∘₀_ {i₀}{j₀}{k₀}{f₀}{g₀}{ii₀}{jj₀}{kk₀} ff₀ gg₀
                   ≃ _∘₁_ {i₁}{j₁}{k₁}{f₁}{g₁}{ii₁}{jj₁}{kk₁} ff₁ gg₁)
        {idl₀    : ∀ {i j}{f : i C₀.⇒ j}{ii jj}{ff : ii ⇒[ f ]₀ jj}
                 → (id₀ ∘₀ ff) ≃ ff}
        {idl₁    : ∀ {i j}{f : i C₁.⇒ j}{ii jj}{ff : ii ⇒[ f ]₁ jj}
                 → (id₁ ∘₁ ff) ≃ ff}
        {idr₀    : ∀ {i j}{f : i C₀.⇒ j}{ii jj}{ff : ii ⇒[ f ]₀ jj}
                 → (ff ∘₀ id₀) ≃ ff}
        {idr₁    : ∀ {i j}{f : i C₁.⇒ j}{ii jj}{ff : ii ⇒[ f ]₁ jj}
                 → (ff ∘₁ id₁) ≃ ff}
        {ass₀    : ∀ {i j k l}{f : k C₀.⇒ l}{g : j C₀.⇒ k}{h : i C₀.⇒ j}
                   {ii jj kk ll}{ff : kk ⇒[ f ]₀ ll}{gg : jj ⇒[ g ]₀ kk}{hh : ii ⇒[ h ]₀ jj}
                 → (ff ∘₀ (gg ∘₀ hh)) ≃ (ff ∘₀ gg) ∘₀ hh}
        {ass₁    : ∀ {i j k l}{f : k C₁.⇒ l}{g : j C₁.⇒ k}{h : i C₁.⇒ j}
                   {ii jj kk ll}{ff : kk ⇒[ f ]₁ ll}{gg : jj ⇒[ g ]₁ kk}{hh : ii ⇒[ h ]₁ jj}
                 → (ff ∘₁ (gg ∘₁ hh)) ≃ (ff ∘₁ gg) ∘₁ hh}
      → mkDispCat {C₀} Obj₀ _⇒[_]₀_ id₀ _∘₀_ idl₀ idr₀ ass₀
      ≃ mkDispCat {C₁} Obj₁ _⇒[_]₁_ id₁ _∘₁_ idl₁ idr₁ ass₁
    mkDispCat≃ refl {Obj₀} {Obj₁} Obj₂ {_⇒[_]₀_} {_⇒[_]₁_} _⇒[_]₂_ {id₀} {id₁}
               id₂ {_∘₀_} {_∘₁_} ∘₂ {idl₀} {idl₁} {idr₀} {idr₁} {ass₀} {ass₁}
               with (Obj₀ ≡ Obj₁ ∋ ext (λ i → uñ (Obj₂ {i}{i} refl̃)))
    ... | refl with ((λ {i}{j} → _⇒[_]₀_ {i}{j}) ≡ (λ {i}{j} → _⇒[_]₁_ {i}{j}) ∋
                     exti λ _ → exti λ _ → ext λ _ → ext λ _ → ext λ _ → _⇒[_]₂_ refl̃ refl̃ refl̃ refl̃ refl̃)
    ... | refl with ((λ {i}{ii} → id₀{i}{ii}) ≡ (λ {i}{ii} → id₁{i}{ii}) ∋
                     exti λ _ → exti λ _ → uñ (id₂ refl̃ refl̃))
    ... | refl with ((λ {i}{j}{k}{f}{g}{ii}{jj}{kk} → _∘₀_ {i}{j}{k}{f}{g}{ii}{jj}{kk}) ≡
                     (λ {i}{j}{k}{f}{g}{ii}{jj}{kk} → _∘₁_ {i}{j}{k}{f}{g}{ii}{jj}{kk}) ∋
                     exti λ i → exti λ j → exti λ k → exti λ f → exti λ g → exti λ ii → exti λ jj → exti λ kk →
                     ext λ ff → ext λ gg → uñ (∘₂ refl̃ refl̃ refl̃ refl̃ refl̃ refl̃ refl̃ refl̃ refl̃ refl̃))
    ... | refl = (mkDispCat Obj₀ _⇒[_]₀_ id₀ _∘₀_ &
             (exti λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _ → UIP̃ _ _)
           ⊗ (exti λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _ → UIP̃ _ _)
           ⊗ (exti λ _ → exti λ _ → exti λ _ → exti λ _
              → exti λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _
              → exti λ _ → exti λ _ → exti λ _ → exti λ _ → UIP̃ _ _)) ~

    mkDispCat≡ :
      ∀ {C : Cat} → let module C = Cat C in
        {Obj₀ Obj₁  : C.Obj → Set α}
        (Obj₂       : ∀ i → Obj₀ i ≡ Obj₁ i)
        {_⇒[_]₀_    : ∀ {i j} → Obj₀ i → i C.⇒ j → Obj₀ j → Set β}
        {_⇒[_]₁_    : ∀ {i j} → Obj₁ i → i C.⇒ j → Obj₁ j → Set β}
        (_⇒[_]₂_    : ∀ {i j} → {ii₀ : Obj₀ i}{ii₁ : Obj₁ i} → ii₀ ≃ ii₁ → ∀ {f} →
                      ∀ {jj₀ : Obj₀ j}{jj₁ : Obj₁ j} → jj₀ ≃ jj₁ → (ii₀ ⇒[ f ]₀ jj₀) ≡ (ii₁ ⇒[ f ]₁ jj₁))
        {id₀        : ∀ {i}{ii : Obj₀ i} → ii ⇒[ C.id {i} ]₀ ii}
        {id₁        : ∀ {i}{ii : Obj₁ i} → ii ⇒[ C.id {i} ]₁ ii}
        (id₂        : ∀ {i} → ∀ {ii₀ ii₁} → ii₀ ≃ ii₁ → id₀ {i}{ii₀} ≃ id₁ {i}{ii₁})
        {_∘₀_       : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j}{ii jj kk}
                    → jj ⇒[ f ]₀ kk → ii ⇒[ g ]₀ jj
                    → ii ⇒[ f C.∘ g ]₀ kk}
        {_∘₁_       : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j}{ii jj kk}
                    → jj ⇒[ f ]₁ kk → ii ⇒[ g ]₁ jj
                    → ii ⇒[ f C.∘ g ]₁ kk}
        (∘₂         : ∀ {i j k f g}
                      → ∀ {ii₀ ii₁} → ii₀ ≃ ii₁ → ∀ {jj₀ jj₁} → jj₀ ≃ jj₁ → ∀ {kk₀ kk₁} → kk₀ ≃ kk₁
                      → ∀ {ff₀ ff₁} → ff₀ ≃ ff₁
                      → ∀ {gg₀ gg₁} → gg₀ ≃ gg₁
                      → _∘₀_ {i}{j}{k}{f}{g}{ii₀}{jj₀}{kk₀} ff₀ gg₀
                      ≃ _∘₁_ {i}{j}{k}{f}{g}{ii₁}{jj₁}{kk₁} ff₁ gg₁)
        {idl₀       : ∀ {i j}{f : i C.⇒ j}{ii jj}{ff : ii ⇒[ f ]₀ jj}
                    → (id₀ ∘₀ ff) ≃ ff}
        {idl₁       : ∀ {i j}{f : i C.⇒ j}{ii jj}{ff : ii ⇒[ f ]₁ jj}
                    → (id₁ ∘₁ ff) ≃ ff}
        {idr₀       : ∀ {i j}{f : i C.⇒ j}{ii jj}{ff : ii ⇒[ f ]₀ jj}
                    → (ff ∘₀ id₀) ≃ ff}
        {idr₁       : ∀ {i j}{f : i C.⇒ j}{ii jj}{ff : ii ⇒[ f ]₁ jj}
                    → (ff ∘₁ id₁) ≃ ff}
        {ass₀       : ∀ {i j k l}{f : k C.⇒ l}{g : j C.⇒ k}{h : i C.⇒ j}
                      {ii jj kk ll}{ff : kk ⇒[ f ]₀ ll}{gg : jj ⇒[ g ]₀ kk}{hh : ii ⇒[ h ]₀ jj}
                    → (ff ∘₀ (gg ∘₀ hh)) ≃ (ff ∘₀ gg) ∘₀ hh}
        {ass₁       : ∀ {i j k l}{f : k C.⇒ l}{g : j C.⇒ k}{h : i C.⇒ j}
                      {ii jj kk ll}{ff : kk ⇒[ f ]₁ ll}{gg : jj ⇒[ g ]₁ kk}{hh : ii ⇒[ h ]₁ jj}
                    → (ff ∘₁ (gg ∘₁ hh)) ≃ (ff ∘₁ gg) ∘₁ hh}
      → mkDispCat {C} Obj₀ _⇒[_]₀_ id₀ _∘₀_ idl₀ idr₀ ass₀ ≡ mkDispCat Obj₁ _⇒[_]₁_ id₁ _∘₁_ idl₁ idr₁ ass₁
    mkDispCat≡ {C} {Obj₀} {Obj₁} Obj₂ {_⇒[_]₀_} {_⇒[_]₁_} _⇒[_]₂_ {id₀} {id₁}
               id₂ {_∘₀_} {_∘₁_} ∘₂ {idl₀} {idl₁} {idr₀} {idr₁} {ass₀} {ass₁} =
               uñ (mkDispCat≃ refl (λ {refl̃ → Obj₂ _ ~})
                                   (λ {refl̃ refl̃ ii₂ refl̃ jj₂ → _⇒[_]₂_ ii₂ jj₂})
                                   (λ {refl̃ ii₂ → id₂ ii₂})
                                   (λ {refl̃ refl̃ refl̃ refl̃ refl̃ ii₂ jj₂ kk₂ ff₂ gg₂ → ∘₂ ii₂ jj₂ kk₂ ff₂ gg₂}))

-- Functors
--------------------------------------------------------------------------------

module _ {α β γ δ : Level} where
  record Functor (C : Cat {α}{β})(D : Cat{γ}{δ}) : Set (α ⊔ β ⊔ γ ⊔ δ) where
    constructor mkFunctor
    private module C = Cat C; private module D = Cat D
    field
      Obj : C.Obj → D.Obj
      ⇒   : ∀ {i j} → i C.⇒ j → Obj i D.⇒ Obj j
      id  : ∀ {i} → ⇒ (C.id {i}) ≡ D.id
      ∘   : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j} → ⇒ (f C.∘ g) ≡ ⇒ f D.∘ ⇒ g
  -- open Functor public

  abstract
    mkFunctor≃ :
     ∀ {C₀ C₁ : Cat}(C₂ : C₀ ≡ C₁) {D₀ D₁ : Cat}(D₂ : D₀ ≡ D₁) →
     let module C₀ = Cat C₀; module C₁ = Cat C₁; module D₀ = Cat D₀; module D₁ = Cat D₁ in
     ∀ {Obj₀ : C₀.Obj → D₀.Obj}
       {Obj₁ : C₁.Obj → D₁.Obj}
       (Obj₂ : ∀ {i₀ :  C₀.Obj}{i₁ : C₁.Obj} → i₀ ≃ i₁ → Obj₀ i₀ ≃ Obj₁ i₁)
       {⇒₀   : ∀ {i j} → i C₀.⇒ j → Obj₀ i D₀.⇒ Obj₀ j}
       {⇒₁   : ∀ {i j} → i C₁.⇒ j → Obj₁ i D₁.⇒ Obj₁ j}
       (⇒₂   : ∀ {i₀ i₁} (i₂ : i₀ ≃ i₁) {j₀ j₁} (j₂ : j₀ ≃ j₁) {f₀ f₁} (f₂ : f₀ ≃ f₁)
               → ⇒₀ {i₀}{j₀} f₀ ≃ ⇒₁ {i₁}{j₁} f₁)
       {id₀  : ∀ {i} → ⇒₀ (C₀.id {i}) ≡ D₀.id}
       {id₁  : ∀ {i} → ⇒₁ (C₁.id {i}) ≡ D₁.id}
       {∘₀   : ∀ {i j k}{f : j C₀.⇒ k}{g : i C₀.⇒ j} → ⇒₀ (f C₀.∘ g) ≡ ⇒₀ f D₀.∘ ⇒₀ g}
       {∘₁   : ∀ {i j k}{f : j C₁.⇒ k}{g : i C₁.⇒ j} → ⇒₁ (f C₁.∘ g) ≡ ⇒₁ f D₁.∘ ⇒₁ g}
       → mkFunctor {C₀}{D₀} Obj₀ ⇒₀ id₀ ∘₀ ≃ mkFunctor {C₁}{D₁} Obj₁ ⇒₁ id₁ ∘₁
    mkFunctor≃ refl refl {Obj₀} {Obj₁} Obj₂ {⇒₀} {⇒₁} ⇒₂
      with ((Obj₀ ≡ Obj₁) ∋ ext (λ i → uñ (Obj₂ refl̃)))
        |  ((λ {i}{j} → ⇒₀ {i}{j}) ≃ (λ {i}{j} → ⇒₁ {i}{j})
           ∋ extĩ (λ i → extĩ (λ j → ext̃ (λ f → ⇒₂ refl̃ refl̃ refl̃))))
    ... | refl | refl̃ =
      mkFunctor Obj₀ ⇒₀ & (exti λ _ → UIP _ _)
                        ⊗ (exti λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _ → UIP _ _) ~

    mkFunctor≡ :
     ∀ {C : Cat}{D : Cat} →
     let module C = Cat C; module D = Cat D in
     ∀ {Obj₀ : C.Obj → D.Obj}
       {Obj₁ : C.Obj → D.Obj}
       (Obj₂ : ∀ i → Obj₀ i ≡ Obj₁ i)
       {⇒₀   : ∀ {i j} → i C.⇒ j → Obj₀ i D.⇒ Obj₀ j}
       {⇒₁   : ∀ {i j} → i C.⇒ j → Obj₁ i D.⇒ Obj₁ j}
       (⇒₂   : ∀ i j f → ⇒₀ {i}{j} f ≃ ⇒₁ {i}{j} f)
       {id₀  : ∀ {i} → ⇒₀ (C.id {i}) ≡ D.id}
       {id₁  : ∀ {i} → ⇒₁ (C.id {i}) ≡ D.id}
       {∘₀   : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j} → ⇒₀ (f C.∘ g) ≡ ⇒₀ f D.∘ ⇒₀ g}
       {∘₁   : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j} → ⇒₁ (f C.∘ g) ≡ ⇒₁ f D.∘ ⇒₁ g}
       → mkFunctor {C}{D} Obj₀ ⇒₀ id₀ ∘₀ ≡ mkFunctor Obj₁ ⇒₁ id₁ ∘₁
    mkFunctor≡ {C}{D}{Obj₀}{Obj₁} Obj₂ ⇒₂ {id₀} {id₁} {∘₀} {∘₁} =
      uñ (mkFunctor≃ refl refl (λ { {i₀} refl̃ → Obj₂ i₀ ~})
                               (λ { {i₀} refl̃ {j₀} refl̃ {f₀} refl̃ → ⇒₂ _ _ f₀ }))

-- Sections of displayed categories ("dependent functor")
--------------------------------------------------------------------------------

  record SectionDisp (C : Cat {α}{β})(D : DispCat C) : Set (α ⊔ β) where
    constructor mkSectionDisp
    private module D = DispCat D; private module C = Cat C
    field
      Obj : ∀ i → D.Obj i
      ⇒   : ∀ {i j}(f : i C.⇒ j) → Obj i D.⇒[ f ] Obj j
      id  : ∀ {i} → ⇒ (C.id {i}) ≡ D.id
      ∘   : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j} → ⇒ (f C.∘ g) ≡ ⇒ f D.∘ ⇒ g
  -- open SectionDisp public

  abstract
    mkSectionDisp≡ :
     ∀ {C : Cat}{D : DispCat C} →
     let module D = DispCat D; module C = Cat C in
     ∀ {Obj₀ : ∀ i → D.Obj i}
       {Obj₁ : ∀ i → D.Obj i}
       (Obj₂ : ∀ i → Obj₀ i ≡ Obj₁ i)
       {⇒₀   : ∀ {i j}(f : i C.⇒ j) → Obj₀ i D.⇒[ f ] Obj₀ j}
       {⇒₁   : ∀ {i j}(f : i C.⇒ j) → Obj₁ i D.⇒[ f ] Obj₁ j}
       (⇒₂   : ∀ i j f → ⇒₀ {i}{j} f ≃ ⇒₁ {i}{j} f)
       {id₀  : ∀ {i} → ⇒₀ (C.id {i}) ≡ D.id}
       {id₁  : ∀ {i} → ⇒₁ (C.id {i}) ≡ D.id}
       {∘₀   : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j} → ⇒₀ (f C.∘ g) ≡ ⇒₀ f D.∘ ⇒₀ g}
       {∘₁   : ∀ {i j k}{f : j C.⇒ k}{g : i C.⇒ j} → ⇒₁ (f C.∘ g) ≡ ⇒₁ f D.∘ ⇒₁ g}
       → mkSectionDisp {C}{D} Obj₀ ⇒₀ id₀ ∘₀ ≡ mkSectionDisp Obj₁ ⇒₁ id₁ ∘₁
    mkSectionDisp≡ {C}{D}{Obj₀}{Obj₁} Obj₂ {⇒₀} {⇒₁} ⇒₂ {id₀} {id₁} {∘₀} {∘₁}
               with ext Obj₂
    ... | refl with ((λ {i}{j} → ⇒₀ {i}{j}) ≡ (λ {i}{j} → ⇒₁ {i}{j})
                     ∋ exti λ i → exti λ j → ext λ f → uñ (⇒₂ i j f))
    ... | refl = mkSectionDisp Obj₀ ⇒₀
            & exti (λ _ → UIP _ _)
            ⊗ exti (λ _ → exti λ _ → exti λ _ → exti λ _ → exti λ _ → UIP _ _)

    mkSectionDisp≃ :
     ∀ {C₀ C₁ : Cat}(C₂ : C₀ ≡ C₁)
       {D₀ : DispCat C₀}{D₁ : DispCat C₁}(D₂ : D₀ ≃ D₁) →
     let module D₀ = DispCat D₀; module C₀ = Cat C₀
         module D₁ = DispCat D₁; module C₁ = Cat C₁ in
     ∀ {Obj₀ : ∀ i → D₀.Obj i}
       {Obj₁ : ∀ i → D₁.Obj i}
       (Obj₂ : ∀ {i₀ i₁} → i₀ ≃ i₁ → Obj₀ i₀ ≃ Obj₁ i₁)
       {⇒₀   : ∀ {i j}(f : i C₀.⇒ j) → Obj₀ i D₀.⇒[ f ] Obj₀ j}
       {⇒₁   : ∀ {i j}(f : i C₁.⇒ j) → Obj₁ i D₁.⇒[ f ] Obj₁ j}
       (⇒₂   : ∀ {i₀ i₁} → i₀ ≃ i₁ → ∀ {j₀ j₁} → j₀ ≃ j₁ → ∀ {f₀ f₁} → f₀ ≃ f₁ → ⇒₀ {i₀}{j₀} f₀ ≃ ⇒₁ {i₁}{j₁} f₁)
       {id₀  : ∀ {i} → ⇒₀ (C₀.id {i}) ≡ D₀.id}
       {id₁  : ∀ {i} → ⇒₁ (C₁.id {i}) ≡ D₁.id}
       {∘₀   : ∀ {i j k}{f : j C₀.⇒ k}{g : i C₀.⇒ j} → ⇒₀ (f C₀.∘ g) ≡ ⇒₀ f D₀.∘ ⇒₀ g}
       {∘₁   : ∀ {i j k}{f : j C₁.⇒ k}{g : i C₁.⇒ j} → ⇒₁ (f C₁.∘ g) ≡ ⇒₁ f D₁.∘ ⇒₁ g}
       → mkSectionDisp {C₀}{D₀} Obj₀ ⇒₀ id₀ ∘₀ ≃ mkSectionDisp {C₁}{D₁} Obj₁ ⇒₁ id₁ ∘₁
    mkSectionDisp≃ {C₀}{C₀} refl {D₀}{D₀} refl̃ {Obj₀}{Obj₁} Obj₂ {⇒₀} {⇒₁} ⇒₂ {id₀} {id₁} {∘₀} {∘₁} =
      mkSectionDisp≡ (λ i → uñ (Obj₂ refl̃)) (λ i j f → ⇒₂ refl̃ refl̃ refl̃) ~

-- Natural transformations
--------------------------------------------------------------------------------

module _ {α β γ δ : Level} where
  record Nat {C : Cat}{D : Cat}(F G : Functor {α}{β}{γ}{δ} C D)
             : Set (α ⊔ β ⊔ γ ⊔ δ) where
    constructor mkNat
    private module F = Functor F; private module G = Functor G
    private module C = Cat C; private module D = Cat D
    field
      maps : ∀ i → F.Obj i D.⇒ G.Obj i
      nat  : ∀ {i j}(f : i C.⇒ j) → maps _ D.∘ F.⇒ f ≡ G.⇒ f D.∘ maps _
  -- open Nat public

  abstract
    mkNat≃ :
        {C₀ C₁ : Cat}(C₂ : C₀ ≡ C₁) {D₀ D₁ : Cat}(D₂ : D₀ ≡ D₁)
        {F₀ : Functor {α}{β}{γ}{δ} C₀ D₀}{F₁ : Functor {α}{β}{γ}{δ} C₁ D₁}(F₂ : F₀ ≃ F₁)
        {G₀ : Functor {α}{β}{γ}{δ} C₀ D₀}{G₁ : Functor {α}{β}{γ}{δ} C₁ D₁}(G₂ : G₀ ≃ G₁)
        → let
            module C₀ = Cat C₀; module C₁ = Cat C₁; module D₀ = Cat D₀; module D₁ = Cat D₁
            module F₀ = Functor F₀; module F₁ = Functor F₁
            module G₀ = Functor G₀; module G₁ = Functor G₁
          in
        {maps₀ : ∀ i → F₀.Obj i D₀.⇒ G₀.Obj i}
        {maps₁ : ∀ i → F₁.Obj i D₁.⇒ G₁.Obj i}
        (maps₂ : ∀ {i₀ : C₀.Obj}{i₁ : C₁.Obj} → i₀ ≃ i₁ → maps₀ i₀ ≃ maps₁ i₁)
        {nat₀ : ∀ {i j}(f : i C₀.⇒ j) → maps₀ _ D₀.∘ F₀.⇒ f ≡ G₀.⇒ f D₀.∘ maps₀ _}
        {nat₁ : ∀ {i j}(f : i C₁.⇒ j) → maps₁ _ D₁.∘ F₁.⇒ f ≡ G₁.⇒ f D₁.∘ maps₁ _}
        → mkNat {C₀}{D₀} {F₀} {G₀} maps₀ nat₀ ≃ mkNat {C₁} {D₁} {F₁} {G₁} maps₁ nat₁
    mkNat≃ refl refl refl̃ refl̃ {maps₀} {maps₁} maps₂ {nat₀} {nat₁}
      with maps₀ ≡ maps₁ ∋ ext (λ i → uñ (maps₂ refl̃))
    ... | refl = (mkNat maps₀ & exti λ _ → exti λ _ → ext λ _ → UIP _ _) ~

    mkNat≡ :
        {C : Cat} {D : Cat}
        {F : Functor {α}{β}{γ}{δ} C D}
        {G : Functor {α}{β}{γ}{δ} C D}
        → let
            module C = Cat C; module D = Cat D
            module F = Functor F; module G = Functor G
          in
        {maps₀ : ∀ i → F.Obj i D.⇒ G.Obj i}
        {maps₁ : ∀ i → F.Obj i D.⇒ G.Obj i}
        (maps₂ : ∀ i → maps₀ i ≡ maps₁ i)
        {nat₀ : ∀ {i j}(f : i C.⇒ j) → maps₀ _ D.∘ F.⇒ f ≡ G.⇒ f D.∘ maps₀ _}
        {nat₁ : ∀ {i j}(f : i C.⇒ j) → maps₁ _ D.∘ F.⇒ f ≡ G.⇒ f D.∘ maps₁ _}
        → mkNat {C}{D} {F} {G} maps₀ nat₀ ≡ mkNat {C} {D} {F} {G} maps₁ nat₁
    mkNat≡ {maps₀} {maps₁} maps₂ {nat₀} {nat₁} = uñ (mkNat≃ refl refl refl̃ refl̃ (λ {refl̃ → maps₂ _ ~}))

-- Functor categories
--------------------------------------------------------------------------------

module _ {α β γ δ} {A : Cat {α}{β}}{B : Cat {γ}{δ}} where
  private module A = Cat A; private module B = Cat B

  NatComp : {F G H : Functor A B} → Nat G H → Nat F G → Nat F H
  NatComp {F}{G}{H} M N =
    mkNat (λ i → M.maps i B.∘ N.maps i)
          (λ {i}{j} f → B.ass ⁻¹ ◾ (M.maps j B.∘_) & N.nat f ◾ B.ass ◾ (B._∘ N.maps i) & M.nat f ◾ B.ass ⁻¹)
    where module N = Nat N; module M = Nat M

  NatId : {F : Functor A B} → Nat F F
  NatId {F} = mkNat (λ i → B.id) (λ {i}{j} f → B.idl ◾ B.idr ⁻¹)

  NatIdl : {F G : Functor A B}{N : Nat F G} → NatComp NatId N ≡ N
  NatIdl {F}{G}{N} = mkNat≡ (λ i → B.idl)

  NatIdr : {F G : Functor A B}{N : Nat F G} → NatComp N NatId ≡ N
  NatIdr {F}{G}{N} = mkNat≡ (λ i → B.idr)

  NatAss : {F G H I : Functor A B}{N : Nat H I}{M : Nat G H}{K : Nat F G}
           → NatComp N (NatComp M K) ≡ NatComp (NatComp N M) K
  NatAss {F} {G} {H} {I} {N} {M} {K} = mkNat≡ (λ i → B.ass)

  𝔽unctor : Functor A B → Functor A B → Cat {α ⊔ β ⊔ γ ⊔ δ}{α ⊔ β ⊔ γ ⊔ δ}
  𝔽unctor F G = mkCat
    (Functor A B )
    Nat
    NatId
    NatComp
    NatIdl
    NatIdr
    (λ {i}{j}{k}{l}{f}{g}{h} → NatAss {i}{j}{k}{l}{f}{g}{h})

-- ℂat (category of small Cats)
--------------------------------------------------------------------------------

Comp : ∀ {α β γ δ ε ν}{C D E} → Functor {_}{_}{ε}{ν} D E → Functor {α}{β}{γ}{δ} C D → Functor C E
Comp {C}{D}{E} F G = record
  { Obj = λ i → F.Obj (G.Obj i)
  ; ⇒   = λ f → F.⇒ (G.⇒ f)
  ; id  = F.⇒ & G.id ◾ F.id
  ; ∘   = F.⇒ & G.∘ ◾ F.∘ }
  where module F = Functor F; module G = Functor G

Id : ∀ {α β C} → Functor {α}{β} C C
Id {C = C} = record
  { Obj = λ i → i
  ; ⇒   = λ f → f
  ; id  = refl
  ; ∘   = refl }
  where module C = Cat C

Idl : ∀ {α β γ δ C D}{F : Functor {α}{β}{γ}{δ} C D} → Comp Id F ≡ F
Idl {C = C}{D}{F} = mkFunctor≡ (λ _ → refl) (λ _ _ _ → refl̃)

Idr : ∀ {α β γ δ C D}{F : Functor {α}{β}{γ}{δ} C D} → Comp F Id ≡ F
Idr {C = C}{D}{F} = mkFunctor≡ (λ _ → refl) (λ _ _ _ → refl̃)

Ass : ∀ {α β γ δ ε ζ η θ C₀ C₁ C₂ C₃}
        {F : Functor {ε}{ζ}{η}{θ} C₂ C₃}{G : Functor C₁ C₂}{H : Functor {α}{β}{γ}{δ} C₀ C₁}
        → Comp F (Comp G H) ≡ Comp (Comp F G) H
Ass {F = F}{G}{H} = mkFunctor≡ (λ i → refl) (λ i j f → refl ~)

ℂat : ∀ {α β} → Cat {suc α ⊔ suc β}{α ⊔ β}
ℂat {α}{β} = mkCat
  (Cat {α}{β})
  Functor
  Id
  Comp
  Idl
  Idr
  (λ {i}{j}{k}{l}{f}{g}{h} → Ass {C₀ = i}{j}{k}{l}{f}{g}{h})

-- Category of sets
--------------------------------------------------------------------------------

𝕊et : ∀ {α} → Cat {suc α} {α}
𝕊et {α} = record
  { Obj = Set α
  ; _⇒_ = λ A B → A → B
  ; id  = λ x → x
  ; _∘_ = λ f g x → f (g x)
  ; idl = refl
  ; idr = refl
  ; ass = refl }

PSh : ∀ {α β} → Cat {suc α}{α} → Set (suc α ⊔ suc β)
PSh {α}{β} C = Functor (C ᵒᵖ) (𝕊et {β})

-- Discrete category
--------------------------------------------------------------------------------

Discrete : ∀ {α} → Set α → Cat
Discrete {α} A = mkCat A (λ i j → i ≡ j) refl (λ p q → q ◾ p) (UIP _ _) refl (UIP _ _)
