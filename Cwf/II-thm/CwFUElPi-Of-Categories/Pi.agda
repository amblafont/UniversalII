{-
Paper: section 7.4

Inductive Π type formation for categories.
-}

open import Level

module CwFUElPi-Of-Categories.Pi {α : Level} where

open import StrictLib hiding (id; _∘_)
open import CwFUElPi-Of-Categories.ElU {α} public

Π : {Γ : Con}(a : Tm {γ = suc α}{α} Γ U) → Ty (Γ ▶ El a) → Ty Γ
Π {Γ} a B = mkTy
  (λ i → (α : a.Obj i) → B.Obj (i , lift α))
  (λ {i}{j} ii f jj → (α : a.Obj i) → ii α B.⇒[ f , refl ] jj (a.⇒ f α))
  id
  (λ {i} {j} {k} {f} {g} {ii} {jj} {kk} → comp {i} {j} {k} {f} {g} {ii} {jj} {kk})
  (λ {i} {j} {f} {ii} {jj} {ff} → idl {i} {j} {f} {ii} {jj} {ff})
  (λ {i} {j} {f} {ii} {jj} {ff} → idr {i} {j} {f} {ii} {jj} {ff})
  (λ {i} {j} {k} {l} {f} {g} {h} {ii} {jj} {kk} {ll} {ff} {gg} {hh}
      → ass {i} {j} {k} {l} {f} {g} {h} {ii} {jj} {kk} {ll} {ff} {gg} {hh})
  where
  module B = Ty B; module a = Tm a; module Γ = Con Γ

  id : {i : Γ.Obj} {ii : (α₁ : a.Obj i) → B.Obj (i , lift α₁)}
        (α₁ : a.Obj i) →
        ii α₁ B.⇒[ Γ.id , refl ] ii (a.⇒ Γ.id α₁)
  id {i} {ii} α = J⁻¹ (λ α' eq → ii α B.⇒[ Γ.id , eq ] ii α') (happly a.id α)
                      (B.id {i , lift α}{ii α})

  comp :
      {i j k : Γ.Obj} {f : j Γ.⇒ k} {g : i Γ.⇒ j}
      {ii : (α₁ : a.Obj i) → B.Obj (i , lift α₁)}
      {jj : (α₁ : a.Obj j) → B.Obj (j , lift α₁)}
      {kk : (α₁ : a.Obj k) → B.Obj (k , lift α₁)} →
      ((α₁ : a.Obj j) → jj α₁ B.⇒[ f , refl ] kk (a.⇒ f α₁)) →
      ((α₁ : a.Obj i) → ii α₁ B.⇒[ g , refl ] jj (a.⇒ g α₁)) →
      (α₁ : a.Obj i) →
      ii α₁ B.⇒[ (f Γ.∘ g) , refl ] kk (a.⇒ (f Γ.∘ g) α₁)
  comp {i} {j} {k} {f} {g} {ii} {jj} {kk} ff gg α =
      J⁻¹ (λ α' eq → ii α B.⇒[ (f Γ.∘ g) , eq ] kk α')
           (happly a.∘ α ◾ refl)
           (B._∘_ (ff (a.⇒ g α)) (gg α))

  abstract
    idl : {i j : Γ.Obj} {f : i Γ.⇒ j}
        {ii : (α₁ : a.Obj i) → B.Obj (i , lift α₁)}
        {jj : (α₁ : a.Obj j) → B.Obj (j , lift α₁)}
        {ff : (α₁ : a.Obj i) → ii α₁ B.⇒[ f , refl ] jj (a.⇒ f α₁)} →
        comp {ii = ii}{jj = jj}{kk = jj}(id{i = j}{ii = jj}) ff ≃ ff
    idl {i} {j} {f} {ii} {jj} {ff} = ext̃ λ α →
        unJ⁻¹ (λ α' eq → ii α B.⇒[ (Γ.id Γ.∘ f) , eq ] jj α') (happly a.∘ α ◾ refl) _
      ◾̃ ap3̃̃
          (λ k' f' ff' →
             B._∘_ {i , lift α} {j , lift (a.⇒ f α)} {j , lift k'} {Γ.id , f'}
             {f , refl} {ii α} {jj (a.⇒ f α)} {jj k'} ff' (ff α))
          (happly a.id (a.⇒ f α))
          (uncoe (_≡_ & refl ⊗ happly a.id (a.⇒ f α)) refl ⁻¹̃ ◾̃ (UIP _ _ ~))
          (unJ⁻¹ _ _ _)
      ◾̃ B.idl

    idr : {i j : Γ.Obj} {f : i Γ.⇒ j}
          {ii : (α₁ : a.Obj i) → B.Obj (i , lift α₁)}
          {jj : (α₁ : a.Obj j) → B.Obj (j , lift α₁)}
          {ff : (α₁ : a.Obj i) → ii α₁ B.⇒[ f , refl ] jj (a.⇒ f α₁)} →
          comp {ii = ii}{ii}{jj} ff id ≃ ff
    idr {i} {j} {f} {ii} {jj} {ff} = ext̃ λ α →
        unJ⁻¹ (λ α' eq → ii α B.⇒[ (f Γ.∘ Γ.id) , eq ] jj α') (happly a.∘ α ◾ refl) _
      ◾̃ ap3̃̃
          (λ i' g' gg →
             B._∘_ {i , lift i'} {i , lift (a.⇒ Γ.id α)}
             {j , lift (a.⇒ f (a.⇒ Γ.id α))} {f , refl} {Γ.id , g'} {ii i'}
             {ii (a.⇒ Γ.id α)} {jj (a.⇒ f (a.⇒ Γ.id α))} (ff (a.⇒ Γ.id α)) gg)
          (happly a.id α ⁻¹)
          (uncoe (_≡_ & (happly a.id (a.⇒ Γ.id α) ⁻¹) ⊗ refl) refl ⁻¹̃
            ◾̃ (UIP _ _ ~))
          (unJ⁻¹ (λ α' eq → ii α B.⇒[ Γ.id , eq ] ii α') (happly a.id α) B.id
           ◾̃ ap2̃̃ (λ i' ii' → B.id {i , lift i'} {ii'}) (happly a.id α ⁻¹) (ap̃̃ ii (happly a.id α ⁻¹)))
      ◾̃ B.idr
      ◾̃ ap̃̃ ff (happly a.id α)

    ass :
        {i j k l : Γ.Obj} {f : k Γ.⇒ l} {g : j Γ.⇒ k} {h : i Γ.⇒ j}
        {ii : (α₁ : a.Obj i) → B.Obj (i , lift α₁)}
        {jj : (α₁ : a.Obj j) → B.Obj (j , lift α₁)}
        {kk : (α₁ : a.Obj k) → B.Obj (k , lift α₁)}
        {ll : (α₁ : a.Obj l) → B.Obj (l , lift α₁)}
        {ff : (α₁ : a.Obj k) → kk α₁ B.⇒[ f , refl ] ll (a.⇒ f α₁)}
        {gg : (α₁ : a.Obj j) → jj α₁ B.⇒[ g , refl ] kk (a.⇒ g α₁)}
        {hh : (α₁ : a.Obj i) → ii α₁ B.⇒[ h , refl ] jj (a.⇒ h α₁)} →
          comp {ii = ii} {kk}{ll} ff (comp {ii = ii}{jj}{kk} gg hh)
        ≃ comp {ii = ii} {jj}{ll} (comp {ii = jj}{kk}{ll} ff gg) hh
    ass {i} {j} {k} {l} {f} {g} {h} {ii} {jj} {kk} {ll} {ff} {gg} {hh} = ext̃ λ α →
        unJ⁻¹ (λ α' eq → ii α B.⇒[ (f Γ.∘ g Γ.∘ h) , eq ] ll α') (happly a.∘ α ◾ refl) _
      ◾̃ ap3̃̃
         (λ j' g' gg' →
            B._∘_ {i , lift α} {k , lift j'} {l , lift (a.⇒ f j')} {f , refl}
            {Γ._∘_ g h , g'} {ii α} {kk j'} {ll (a.⇒ f j')} (ff j') gg')
         (happly a.∘ α)
         ((UIP _ _ ~) ◾̃ uncoe (_≡_ & refl ⊗ (happly a.∘ α ⁻¹)) (happly a.∘ α ◾ refl))
         (unJ⁻¹ (λ α' eq → ii α B.⇒[ (g Γ.∘ h) , eq ] kk α')
                (happly a.∘ α ◾ refl) (gg (a.⇒ h α) B.∘ hh α))
      ◾̃ B.ass
      ◾̃ ap3̃̃
          (λ k' f' ff' →
             B._∘_ {i , lift α} {j , lift (a.⇒ h α)} {l , lift k'}
             {Γ._∘_ f g , f'} {h , refl} {ii α} {jj (a.⇒ h α)} {ll k'} ff'
             (hh α))
          (happly a.∘ (a.⇒ h α) ⁻¹)
          ((UIP _ _ ~) ◾̃ uncoe (_≡_ & refl ⊗ happly a.∘ (a.⇒ h α)) refl)
          (unJ⁻¹ _ _ _ ⁻¹̃)
      ◾̃ unJ⁻¹ (λ α' eq → ii α B.⇒[ ((f Γ.∘ g) Γ.∘ h) , eq ] ll α') (happly a.∘ α ◾ refl) _ ⁻¹̃
