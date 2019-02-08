
{-
Paper: section 4, section 6

This file defines algebras, displayed algebras and sections of displayed algebras for QIITs.
-}
-- copied from ADS.agda


{- Algebra-Displayed Algebra-Section model of the theory of signatures -}
import SyntaxIsModel as SM

module ACDS (Ω : SM.Con) where

-- infixl 9 ap
open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )
  hiding (_∘_ ; _⁻¹ ; Π ; _$_ ; Lift ; Ω)

open import monlib
-- import StrictLib hiding (id; _∘_)
open import SyntaxIsModel using (module Syn; ₁ ; ₂)

module AM where

private
  module S = Syn
open import ModelRecord

-- open import StrictLib hiding (id; _∘_)

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t

i : Level
i = suc (suc zero)

j : Level
j = suc zero


record Con : Set i where
  constructor mkCon
  field
    ⁱ : SM.Con
    ᴬ : Set₁
    ᴰ : ᴬ → Set₁
    ˢ : (γ : ᴬ) → ᴰ γ → Set
    ᶜ : (e : S.Sub Ω  ⁱ) → ᴬ
open Con public

record Ty (Γ : Con) : Set i where
  constructor mkTy
  field
    ⁱ : SM.Ty ((ⁱ Γ))
    ᴬ : Γ .ᴬ → Set₁
    ᴰ : (γ : Con.ᴬ Γ) → Con.ᴰ Γ γ → ᴬ γ → Set₁
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Γ .ˢ γ γᴰ)(α : ᴬ γ) → ᴰ γ γᴰ α → Set
    -- ᶜ : ∀ e → (t : S.Tm Ω (extendsT {Ω}{Con.ⁱ Γ} e ⁱ)) → ᴬ (Con.ᶜ Γ e)
    ᶜ : ∀ (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → (t : S.Tm Ω (ⁱ S.[ v ]T)) → ᴬ (Con.ᶜ Γ v)
open Ty public


record Tm (Γ : Con)(A : Ty Γ) : Set j where
  constructor mkTm
  field
    ⁱ : SM.Tm ( (ⁱ Γ)) ( (ⁱ A))
    ᴬ : (γ : Con.ᴬ Γ) → Ty.ᴬ A γ
    ᴰ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ) → Ty.ᴰ A γ γᴰ (ᴬ γ)
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Con.ˢ Γ γ γᴰ) → Ty.ˢ A γ γᴰ γˢ (ᴬ γ) (ᴰ γ γᴰ)
    ᶜ : (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → Ty.ᶜ A v (ⁱ S.[ v ]t) ≡ ᴬ (Con.ᶜ Γ v)
open Tm public

record Sub (Γ Δ : Con) : Set j where
  constructor mkSub
  field
    ⁱ : SM.Sub ( (ⁱ Γ))( (ⁱ Δ))
    ᴬ : Con.ᴬ Γ → Con.ᴬ Δ
    ᴰ : (γ : Con.ᴬ Γ) → Con.ᴰ Γ γ → Con.ᴰ Δ (ᴬ γ)
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Con.ˢ Γ γ γᴰ) → Con.ˢ Δ (ᴬ γ) (ᴰ γ γᴰ)
    ᶜ : (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → Con.ᶜ Δ (ⁱ S.∘ v) ≡ ᴬ (ᶜ Γ v)
    -- Ty.ᶜ A v (Ω ⊢ ⁱ [ v ]t) ≡ ᴬ (Con.ᶜ Γ v)
open Sub public

∙ : Con
∙ = mkCon
  (S.∙ )
  (Lift ⊤)
  (λ _ → Lift ⊤)
  (λ _ _ → Lift ⊤)
  λ e → lift tt

_▶_ : (Γ : Con) → Ty Γ → Con
(mkCon Γⁱ Γᴬ Γᴰ Γˢ Γᶜ) ▶ (mkTy Aⁱ Aᴬ Aᴰ Aˢ Aᶜ) = mkCon
  (Γⁱ S.▶ Aⁱ)
  (Σ Γᴬ Aᴬ)
  (λ {(γ , α) → Σ (Γᴰ γ) λ γᴰ → Aᴰ γ γᴰ α})
  (λ {(γ , α)(γᴰ , αᴰ) → Σ (Γˢ γ γᴰ) λ γˢ → Aˢ γ γᴰ γˢ α αᴰ})
  λ v  → (Γᶜ (S.π₁ v)) , Aᶜ (S.π₁ v) (S.π₂ v)

[]Tᶜ : ∀ {Γ}{Δ}(A : Ty Δ)(σ : Sub Γ Δ) → (v : S.Sub Ω (ⁱ Γ)) →
      S.Tm Ω (ⁱ A S.[ ⁱ σ ]T S.[ v ]T) → ᴬ A (ᴬ σ (ᶜ Γ v))

[]Tᶜ {Γ}{Δ}A σ v t =
    tr (ᴬ A) (ᶜ σ v) (ᶜ A (ⁱ σ S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) t))

-- I need composition of substitutions
_[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {Γ} {Δ}(mkTy Aⁱ Aᴬ Aᴰ Aˢ Aᶜ) (mkSub σⁱ σᴬ σᴰ σˢ σᶜ) = mkTy
   (Aⁱ S.[ σⁱ ]T)
  (λ γ → Aᴬ (σᴬ γ))
  (λ γ γᴰ α → Aᴰ (σᴬ γ) (σᴰ γ γᴰ) α)
  (λ γ γᴰ γˢ α αᴰ → Aˢ (σᴬ γ) (σᴰ γ γᴰ) (σˢ γ γᴰ γˢ) α αᴰ)
  ([]Tᶜ (mkTy Aⁱ Aᴬ Aᴰ Aˢ Aᶜ) (mkSub σⁱ σᴬ σᴰ σˢ σᶜ) )
  -- λ v t → tr Aᴬ (σᶜ v) (Aᶜ (σⁱ S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = Aⁱ}) t))
  

id : ∀{Γ} → Sub Γ Γ
id {mkCon Γⁱ Γᴬ Γᴰ Γˢ Γᶜ} = mkSub
  (S.id {Γ = Γⁱ})
  (λ γ → γ)
  (λ _ γᴰ → γᴰ)
  (λ _ _ γˢ → γˢ)
  λ v → ap Γᶜ S.idl

{-
_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
_∘_ {Γ}{Δ} (mkSub σⁱ σᴬ σᴰ σˢ σᶜ) (mkSub δⁱ δᴬ δᴰ δˢ δᶜ ) = mkSub
  (ⁱ Γ ⊢ σⁱ S∘ δⁱ  )
  (λ γ → σᴬ (δᴬ γ))
  (λ γ γᴰ → σᴰ (δᴬ γ) (δᴰ γ γᴰ))
  (λ γ γᴰ γˢ → σˢ (δᴬ γ) (δᴰ γ γᴰ) (δˢ γ γᴰ γˢ))
  λ v → _∙_ (_∙_ {!!}   (σᶜ (Ω ⊢ δⁱ S∘ v))) (ap σᴬ (δᶜ v))

ε : ∀{Γ} → Sub Γ ∙
ε {Γ} = mkSub
  (λ _ → lift tt)
  (λ _ _ → lift tt)
  (λ _ _ _ → lift tt)

_,s_ : ∀{Γ Δ}(σ : Sub Γ Δ){A : Ty Δ} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
_,s_ {Γ}{Δ} (mkSub σᴬ σᴰ σˢ) {A} (mkTm tᴬ tᴰ tˢ) = mkSub
  (λ γ → σᴬ γ , tᴬ γ)
  (λ γ γᴰ → σᴰ γ γᴰ , tᴰ γ γᴰ)
  (λ γ γᴰ γˢ → σˢ γ γᴰ γˢ , tˢ γ γᴰ γˢ)
  -}

π₁ : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {Δ = Δ}(mkSub σⁱ σᴬ σᴰ σˢ σᶜ) = mkSub
  (S.π₁ σⁱ)
  (λ γ → ₁ (σᴬ γ))
  (λ γ γᴰ → ₁ (σᴰ γ γᴰ))
  (λ γ γᴰ γˢ → ₁ (σˢ γ γᴰ γˢ))
  -- π₁ (σ ∘ δ) = (π₁ σ) ∘ δ
  -- λ v →  ap (ᶜ Δ) (S.π₁∘ σⁱ v) ◾ fst=  (σᶜ v)
  λ v →  ap (ᶜ Δ) ( ! (S.π₁∘ {σ = σⁱ}{δ = v}  )   ) ◾ fst=  (σᶜ v)

_[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {A = A}(mkTm tⁱ tᴬ tᴰ tˢ tᶜ) (mkSub σⁱ σᴬ σᴰ σˢ σᶜ) = mkTm
   (tⁱ S.[ σⁱ ]t)
  (λ γ → tᴬ (σᴬ γ))
  (λ γ γᴰ → tᴰ (σᴬ γ) (σᴰ γ γᴰ))
  (λ γ γᴰ γˢ → tˢ (σᴬ γ) (σᴰ γ γᴰ) (σˢ γ γᴰ γˢ))
  (λ v →
        ap (λ x → tr (ᴬ A) (σᶜ v) (ᶜ A (S._∘_ σⁱ v) x)) (to-transp (S.[][]t {t = tⁱ}{σ = v}{δ = σⁱ} )) 
     ◾ ap (tr _ (σᶜ v))(tᶜ (σⁱ S.∘ v))
     ◾ to-transp (apd tᴬ (σᶜ v) ))

π₂ : {Γ Δ : Con}
     {A : Ty Δ}
     (σ : Sub Γ (Δ ▶ A)) → Tm Γ (_[_]T {Γ} {Δ} A (π₁ {Γ} {Δ} {A} σ))
π₂ {Γ}{Δ = Δ}{A = A}(mkSub σⁱ σᴬ σᴰ σˢ σᶜ) = mkTm
   (S.π₂ σⁱ)
  (λ γ → ₂ (σᴬ γ))
  (λ γ γᴰ → ₂ (σᴰ γ γᴰ))
  (λ γ γᴰ γˢ → ₂ (σˢ γ γᴰ γˢ))
  --  π₁ σⁱ ∘ v ≡
  helper
  
    where
      π₁σ = (π₁ {Γ = Γ}{Δ = Δ}{A = A} (mkSub σⁱ σᴬ σᴰ σˢ σᶜ))
      xx : ∀ v → S.Tm Ω (ⁱ A S.[ S.π₁ (σⁱ S.∘ v) ]T)
      xx v = transport! (S.Tm Ω) (ap (λ s → S._[_]T (ⁱ A) s)
         (S.π₁∘ {A = ⁱ A}{σ = σⁱ}) ◾ ! (S.[][]T {A = ⁱ A})) (S.π₂ σⁱ S.[ v ]t) 

      helper : ∀ v →
        -- []Tᶜ A π₁σ v (S.π₂ σⁱ S.[ v ]t)
        -- tr (ᴬ A) (ᶜ π₁σ v) (ᶜ A (S.π₁ σⁱ  S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ σⁱ S.[ v ]t)))
        tr (ᴬ A) (ap (ᶜ Δ) ( ! (S.π₁∘ {σ = σⁱ}{δ = v}  )   ) ◾ fst=  (σᶜ v))
          (ᶜ A (S.π₁ σⁱ  S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ σⁱ S.[ v ]t)))

        -- ᶜ (A [ π₁ {A = A}(mkSub σⁱ σᴬ σᴰ σˢ σᶜ) ]T) v (S.π₂ σⁱ S.[ v ]t)
        ≡
            ₂ (σᴬ (ᶜ Γ v))
            -- ₂ (σᴬ (ᶜ Γ v))
      helper v =
       to-transp {B = ᴬ A}
         {p = ap (ᶜ Δ) (! (S.π₁∘ {σ = σⁱ} {δ = v})) ◾ fst= (σᶜ v)}
         -- uip for simplicty
          (≅↓
            (
            (ᶜ A (S.π₁ σⁱ  S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ σⁱ S.[ v ]t)))

              ≅⟨ ↓≅ (apd {A = ∃ (λ (v₁ : S.Sub Ω (ⁱ Δ)) → S.Tm Ω (ⁱ A S.[ v₁ ]T))}
                    (λ x → ᶜ A (₁ x)(₂ x))
                    {x = (S.π₁ σⁱ  S.∘ v) , tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ σⁱ S.[ v ]t)}
                    {y = (S.π₁ (σⁱ S.∘ v)) , xx v}
                    (pair= (! S.π₁∘)
                      (≅↓ (↓≅ ( (from-transp  (S.Tm Ω) (S.[][]T {A = ⁱ A}) refl) ) !≅
                       ∘≅ (↓≅ (from-transp! (S.Tm Ω) (ap (λ s → S._[_]T (ⁱ A) s) (S.π₁∘ {A = ⁱ A}{σ = σⁱ})
                                  ◾ ! (S.[][]T {A = ⁱ A})) refl) !≅)))
                      ))
                ⟩
              -- ≅⟨ {!ᶜ Aap {A = Σ _ _}(λ x → ᶜ A (₁ x)(₂ x))!} ⟩
            ᶜ A (S.π₁ (σⁱ S.∘ v)) (xx v)
            -- ᶜ A (S.π₁ (σⁱ S.∘ v)) (tr (S.Tm Ω) {!ap (λ s → _ S.[ s ]T) S.π₁∘ ◾ ! S.[][]T!} (S.π₂ σⁱ S.[ v ]t))

              ≅⟨ =≅ ( ap (ᶜ A (S.π₁ (σⁱ S.∘ v))) ( ! (to-transp! ( (S.π₂∘ {σ = σⁱ}{δ = v})))) ) ⟩
            ᶜ A (S.π₁ (σⁱ S.∘ v)) (S.π₂ (σⁱ S.∘ v))

              ≅⟨ ↓≅ (apd ₂ (σᶜ v)) ⟩
            ₂ (σᴬ (ᶜ Γ v))
            ≅∎
            )
            )


{- 
[id]T : ∀{Γ}{A : Ty Γ} → A [ id ]T ≡ A
[id]T = refl

[][]T : {Γ Δ : Con} {Σ : Con} {A : Ty Σ} {σ : Sub Γ Δ}
    {δ : Sub Δ Σ} →
    _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (_[_]T {Δ} {Σ} A δ) σ)
    (_[_]T {Γ} {Σ} A (_∘_ {Γ} {Δ} {Σ} δ σ))
[][]T = refl

idl   : {Γ Δ : Con} {σ : Sub Γ Δ} → _≡_ {j} {Sub Γ Δ} (_∘_ {Γ} {Δ} {Δ} (id {Δ}) σ) σ
idl = refl

idr   : {Γ Δ : Con} {σ : Sub Γ Δ} → _≡_ {j} {Sub Γ Δ} (_∘_ {Γ} {Γ} {Δ} σ (id {Γ})) σ
idr = refl

ass   : {Γ Δ : Con} {Σ : Con} {Ω : Con} {σ : Sub Σ Ω} {δ : Sub Δ Σ}
  {ν : Sub Γ Δ} →
  _≡_ {_} {Sub Γ Ω} (_∘_ {Γ} {Δ} {Ω} (_∘_ {Δ} {Σ} {Ω} σ δ) ν)
  (_∘_ {Γ} {Σ} {Ω} σ (_∘_ {Γ} {Δ} {Σ} δ ν))
ass = refl

,∘    :
  {Γ Δ : Con} {Σ : Con} {δ : Sub Γ Δ} {σ : Sub Σ Γ} {A : Ty Δ}
  {t : Tm Γ (_[_]T {Γ} {Δ} A δ)} →
  _≡_ {_} {Sub Σ (Δ ▶ A)}
  (_∘_ {Σ} {Γ} {Δ ▶ A} (_,s_ {Γ} {Δ} δ {A} t) σ)
  (_,s_ {Σ} {Δ} (_∘_ {Σ} {Γ} {Δ} δ σ) {A}
   (tr {_} {_} {Ty Σ} (Tm Σ)
    {_[_]T {Σ} {Γ} (_[_]T {Γ} {Δ} A δ) σ}
    {_[_]T {Σ} {Δ} A (_∘_ {Σ} {Γ} {Δ} δ σ)}
    ([][]T {Σ} {Γ} {Δ} {A} {σ} {δ})
    (_[_]t {Σ} {Γ} {_[_]T {Γ} {Δ} A δ} t σ)))
,∘ = refl

π₁β   : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ}
   {t : Tm Γ (_[_]T {Γ} {Δ} A σ)} →
   _≡_ {_} {Sub Γ Δ} (π₁ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)) σ
π₁β = refl

πη    : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ (Δ ▶ A)} →
  _≡_ {_} {Sub Γ (Δ ▶ A)}
  (_,s_ {Γ} {Δ} (π₁ {Γ} {Δ} {A} σ) {A} (π₂ {Γ} {Δ} {A} σ)) σ
πη = refl

εη    : {Γ : Con} {σ : Sub Γ ∙} → _≡_ {_} {Sub Γ ∙} σ (ε {Γ})
εη = refl

-}



-- celui la peut se déduire des autres, non ?
wk : ∀{Γ}{A : Ty Γ} → Sub (Γ ▶ A) Γ
wk {Γ} {A} =
  -- mkSub (S.wk (ⁱ Γ) (ⁱ A))
  mkSub (S.wk  )
   ₁ (λ γ → ₁) (λ γ γᴰ → ₁)
   -- wk ∘ v ≡ π₁ v
   λ v → ap (ᶜ Γ)  S.wk∘  
   -- λ v → ap (ᶜ Γ) {! S.wk∘ (ⁱ Γ)(ⁱ A) v ) !}
{-

{-
vz : ∀{Γ}{A : Ty Γ} → Tm (Γ ▶ A) (A [ wk ]T)
vz {z} {z₁} = mkTm ₂ (λ γ → ₂) (λ γ γᴰ → ₂)

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs {z} {z₁} {z₂} x =
  _[_]t {z ▶ z₂} {z} {z₁} x (π₁ {z ▶ z₂} {z} {z₂} (id {z ▶ z₂}))

<_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▶ A)
<_> {z} {z₁} t =
  mkSub (λ γ → γ , ᴬ t γ) (λ γ γᴰ → γᴰ , ᴰ t γ γᴰ)
        (λ γ γᴰ γˢ → γˢ , ˢ t γ γᴰ γˢ)


-}

infix 4 <_>

_^_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {Γ} {Δ} σ A = mkSub
  (S.keep (ⁱ σ) (ⁱ A))
  (λ γ → ᴬ σ (₁ γ) , ₂ γ) (λ γ γᴰ → ᴰ σ (₁ γ) (₁ γᴰ) , ₂ γᴰ)
  (λ γ γᴰ γˢ → ˢ σ (₁ γ) (₁ γᴰ) (₁ γˢ) , ₂ γˢ)
  λ v → pair= ({!!} ◾ ᶜ σ (S.π₁ v) ) {!!}
  -- λ v → {! ᶜ σ (S.π₁ v) !}

infixl 5 _^_
{-
-}
-- infixl 5 _^_




-- Universe
--------------------------------------------------------------------------------

U : ∀{Γ} → Ty Γ
U {mkCon Γⁱ Γᴬ Γᴰ Γˢ Γᶜ} = mkTy
   (S.U Γⁱ)
  (λ _ → Set)
  (λ _ _ T → T → Set)
  (λ _ _ _ T Tᴰ → (α : T) → Tᴰ α)
  λ e t → S.Tm (₁ Ω) (S.Elp (₁ t))


El : ∀{Γ}(a : Tm Γ U) → Ty Γ
El {Γ} (mkTm aⁱ aᴬ aᴰ aˢ aᶜ) = mkTy
  (S.El (ⁱ Γ) aⁱ )
  (λ γ → Lift (aᴬ γ))
  (λ {γ γᴰ (lift α) → Lift (aᴰ γ γᴰ α)})
  (λ {γ γᴰ γˢ (lift α) (lift αᴰ) → aˢ γ γᴰ γˢ α ≡ αᴰ})
  λ v t → coe (ap Lift (aᶜ v )) (lift t)

-- -}
{- 

-- Inductive function
--------------------------------------------------------------------------------

Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ
Π {mkCon Γᴬ Γᴰ Γˢ}(mkTm aᴬ aᴰ aˢ) (mkTy Bᴬ Bᴰ Bˢ)
  = mkTy
      (λ γ → (α : aᴬ γ) → Bᴬ (γ , lift α))
      (λ γ γᴰ f → (x : aᴬ γ)(xᴰ : aᴰ γ γᴰ x) → Bᴰ _ (γᴰ , (lift xᴰ)) (f x))
      (λ γ γᴰ γˢ f fᴰ → (x : aᴬ γ) → Bˢ _ (γᴰ , lift (aˢ γ γᴰ γˢ x)) (γˢ , refl) (f x)
                                             (fᴰ x (aˢ γ γᴰ γˢ x)))


app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
app {mkCon Γᴬ Γᴰ Γˢ}{mkTm aᴬ aᴰ aˢ}{mkTy Bᴬ Bᴰ Bˢ}(mkTm tᴬ tᴰ tˢ) =
  mkTm
    (λ {(γ , lift α) → tᴬ γ α})
    (λ {(γ , lift α) (γᴰ , lift αᴰ) → tᴰ γ γᴰ α αᴰ})
    (λ {(γ , lift α) (γᴰ , lift αᴰ)(γˢ , αˢ) →
      J (λ αᴰ αˢ → Bˢ _ (γᴰ , lift αᴰ) (γˢ , αˢ) (tᴬ γ α) (tᴰ γ γᴰ α αᴰ))
         (tˢ γ γᴰ γˢ α)
         αˢ})



-- -}



