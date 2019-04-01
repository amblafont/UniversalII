{-
Paper: section 4, section 6

This file defines algebras, displayed algebras and sections of displayed algebras for QIITs.
-}

{-# OPTIONS --rewriting #-}

{- Algebra-Displayed Algebra-Section model of the theory of signatures -}

module ADS where

import StrictLib hiding (id; _∘_)

module AM where

import Syntax as S
open import StrictLib hiding (id; _∘_)

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
    ᴬ : Set₁
    ᴰ : ᴬ → Set₁
    ˢ : (γ : ᴬ) → ᴰ γ → Set
open Con public

record Ty (Γ : Con) : Set i where
  constructor mkTy
  field
    ᴬ : Γ .ᴬ → Set₁
    ᴰ : (γ : Con.ᴬ Γ) → Con.ᴰ Γ γ → ᴬ γ → Set₁
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Γ .ˢ γ γᴰ)(α : ᴬ γ) → ᴰ γ γᴰ α → Set
open Ty public

record Tm (Γ : Con)(A : Ty Γ) : Set j where
  constructor mkTm
  field
    ᴬ : (γ : Con.ᴬ Γ) → Ty.ᴬ A γ
    ᴰ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ) → Ty.ᴰ A γ γᴰ (ᴬ γ)
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Con.ˢ Γ γ γᴰ) → Ty.ˢ A γ γᴰ γˢ (ᴬ γ) (ᴰ γ γᴰ)
open Tm public

record Sub (Γ Δ : Con) : Set j where
  constructor mkSub
  field
    ᴬ : Con.ᴬ Γ → Con.ᴬ Δ
    ᴰ : (γ : Con.ᴬ Γ) → Con.ᴰ Γ γ → Con.ᴰ Δ (ᴬ γ)
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Con.ˢ Γ γ γᴰ) → Con.ˢ Δ (ᴬ γ) (ᴰ γ γᴰ)
open Sub public

∙ : Con
∙ = mkCon
  (Lift ⊤)
  (λ _ → Lift ⊤)
  (λ _ _ → Lift ⊤)

_▶_ : (Γ : Con) → Ty Γ → Con
(mkCon Γᴬ Γᴰ Γˢ) ▶ (mkTy Aᴬ Aᴰ Aˢ) = mkCon
  (Σ Γᴬ Aᴬ)
  (λ {(γ , α) → Σ (Γᴰ γ) λ γᴰ → Aᴰ γ γᴰ α})
  (λ {(γ , α)(γᴰ , αᴰ) → Σ (Γˢ γ γᴰ) λ γˢ → Aˢ γ γᴰ γˢ α αᴰ})

_[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T (mkTy Aᴬ Aᴰ Aˢ) (mkSub σᴬ σᴰ σˢ) = mkTy
  (λ γ → Aᴬ (σᴬ γ))
  (λ γ γᴰ α → Aᴰ (σᴬ γ) (σᴰ γ γᴰ) α)
  (λ γ γᴰ γˢ α αᴰ → Aˢ (σᴬ γ) (σᴰ γ γᴰ) (σˢ γ γᴰ γˢ) α αᴰ)

id : ∀{Γ} → Sub Γ Γ
id {mkCon Γᴬ Γᴰ Γˢ} = mkSub
  (λ γ → γ)
  (λ _ γᴰ → γᴰ)
  (λ _ _ γˢ → γˢ)

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
(mkSub σᴬ σᴰ σˢ) ∘ (mkSub δᴬ δᴰ δˢ) = mkSub
  (λ γ → σᴬ (δᴬ γ))
  (λ γ γᴰ → σᴰ (δᴬ γ) (δᴰ γ γᴰ))
  (λ γ γᴰ γˢ → σˢ (δᴬ γ) (δᴰ γ γᴰ) (δˢ γ γᴰ γˢ))

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

π₁ : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ (mkSub σᴬ σᴰ σˢ) = mkSub
  (λ γ → ₁ (σᴬ γ))
  (λ γ γᴰ → ₁ (σᴰ γ γᴰ))
  (λ γ γᴰ γˢ → ₁ (σˢ γ γᴰ γˢ))

_[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t (mkTm tᴬ tᴰ tˢ) (mkSub σᴬ σᴰ σˢ) = mkTm
  (λ γ → tᴬ (σᴬ γ))
  (λ γ γᴰ → tᴰ (σᴬ γ) (σᴰ γ γᴰ))
  (λ γ γᴰ γˢ → tˢ (σᴬ γ) (σᴰ γ γᴰ) (σˢ γ γᴰ γˢ))

π₂ : {Γ Δ : Con}
     {A : Ty Δ}
     (σ : Sub Γ (Δ ▶ A)) → Tm Γ (_[_]T {Γ} {Δ} A (π₁ {Γ} {Δ} {A} σ))
π₂ (mkSub σᴬ σᴰ σˢ) = mkTm
  (λ γ → ₂ (σᴬ γ))
  (λ γ γᴰ → ₂ (σᴰ γ γᴰ))
  (λ γ γᴰ γˢ → ₂ (σˢ γ γᴰ γˢ))

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

π₂β   : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ}
  {t : Tm Γ (_[_]T {Γ} {Δ} A σ)} →
  _≡_ {_}
  {Tm Γ (_[_]T {Γ} {Δ} A (π₁ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)))}
  (π₂ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t))
  (tr {_} {_} {Sub Γ Δ} (λ σ₁ → Tm Γ (_[_]T {Γ} {Δ} A σ₁)) {σ}
   {π₁ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)}
   (_⁻¹ {_} {Sub Γ Δ} {π₁ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)} {σ}
    (π₁β {Γ} {Δ} {A} {σ} {t}))
   t)
π₂β = refl

wk : ∀{Γ}{A : Ty Γ} → Sub (Γ ▶ A) Γ
wk {z} {z₁} = mkSub ₁ (λ γ → ₁) (λ γ γᴰ → ₁)

vz : ∀{Γ}{A : Ty Γ} → Tm (Γ ▶ A) (A [ wk ]T)
vz {z} {z₁} = mkTm ₂ (λ γ → ₂) (λ γ γᴰ → ₂)

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs {z} {z₁} {z₂} x =
  _[_]t {z ▶ z₂} {z} {z₁} x (π₁ {z ▶ z₂} {z} {z₂} (id {z ▶ z₂}))

<_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▶ A)
<_> {z} {z₁} t =
  mkSub (λ γ → γ , ᴬ t γ) (λ γ γᴰ → γᴰ , ᴰ t γ γᴰ)
        (λ γ γᴰ γˢ → γˢ , ˢ t γ γᴰ γˢ)

infix 4 <_>

_^_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {Γ} {Δ} σ A = mkSub
  (λ γ → ᴬ σ (₁ γ) , ₂ γ) (λ γ γᴰ → ᴰ σ (₁ γ) (₁ γᴰ) , ₂ γᴰ)
  (λ γ γᴰ γˢ → ˢ σ (₁ γ) (₁ γᴰ) (₁ γˢ) , ₂ γˢ)

infixl 5 _^_

-- Universe
--------------------------------------------------------------------------------

U : ∀{Γ} → Ty Γ
U {mkCon Γᴬ Γᴰ Γˢ} = mkTy
  (λ _ → Set)
  (λ _ _ T → T → Set)
  (λ _ _ _ T Tᴰ → (α : T) → Tᴰ α)

U[] : ∀{Γ Δ}{σ : Sub Γ Δ} → _[_]T {Γ}{Δ} U σ ≡ U
U[] = refl

El : ∀{Γ}(a : Tm Γ U) → Ty Γ
El (mkTm aᴬ aᴰ aˢ) = mkTy
  (λ γ → Lift (aᴬ γ))
  (λ {γ γᴰ (lift α) → Lift (aᴰ γ γᴰ α)})
  (λ {γ γᴰ γˢ (lift α) (lift αᴰ) → aˢ γ γᴰ γˢ α ≡ αᴰ})

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
     → El a [ σ ]T ≡ El (tr (Tm Γ) (U[] {Γ}{Δ}{σ}) (_[_]t {Γ}{Δ}{U} a σ))
El[] = refl

-- Identity
--------------------------------------------------------------------------------

Id : ∀ {Γ}(a : Tm Γ U) → Tm Γ (El a) → Tm Γ (El a) → Ty Γ
Id {mkCon Γᴬ Γᴰ Γˢ}(mkTm aᴬ aᴰ aˢ) (mkTm tᴬ tᴰ tˢ) (mkTm uᴬ uᴰ uˢ) =
  mkTy
    (λ γ → tᴬ γ ≡ uᴬ γ)
    (λ γ γᴰ e → coe ((λ x → Lift (aᴰ γ γᴰ (lower x))) & e)
                    (tᴰ γ γᴰ) ≡ uᴰ γ γᴰ)
    (λ γ γᴰ γˢ e eᴰ → ⊤)

Id[] :
     {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {t u : Tm Δ (El {Δ}
     a)} → _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (Id {Δ} a t u) σ) (Id {Γ}
     (coe {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_
     {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ}
     {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a σ)) (coe
     {_} {Tm Γ (_[_]T {Γ} {Δ} (El {Δ} a) σ)} {Tm Γ (El {Γ} (coe
     {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_
     {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ}
     {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a σ)))} (_&_
     {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (El {Δ} a)
     σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U
     {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ}
     (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a
     σ))} (El[] {Γ} {Δ} {σ} {a})) (_[_]t {Γ} {Δ} {El {Δ} a} t σ)) (coe
     {_} {Tm Γ (_[_]T {Γ} {Δ} (El {Δ} a) σ)} {Tm Γ (El {Γ} (coe
     {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_
     {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ}
     {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a σ)))} (_&_
     {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (El {Δ} a)
     σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U
     {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ}
     (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a
     σ))} (El[] {Γ} {Δ} {σ} {a})) (_[_]t {Γ} {Δ} {El {Δ} a} u σ)))
Id[] = refl

Reflect :
  ∀ {Γ}{a : Tm Γ (U {Γ})}{t u : Tm Γ (El a)} → Tm Γ (Id a t u) → t ≡ u
Reflect {mkCon Γᴬ Γᴰ Γˢ}{mkTm aᴬ aᴰ aˢ}
        {mkTm tᴬ tᴰ tˢ}{mkTm uᴬ uᴰ uˢ}(mkTm eᴬ eᴰ eˢ)
  with ext eᴬ
... | refl with (tᴰ ≡ uᴰ) ∋ ext λ γ → ext λ γᴰ → coe-refl _ (tᴰ γ γᴰ) ⁻¹ ◾ eᴰ γ γᴰ
... | refl with (tˢ ≡ uˢ) ∋ ext λ _ → ext λ _ → ext λ _ → UIP _ _
... | refl = refl

-- Inductive function
--------------------------------------------------------------------------------

Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ
Π {mkCon Γᴬ Γᴰ Γˢ}(mkTm aᴬ aᴰ aˢ) (mkTy Bᴬ Bᴰ Bˢ)
  = mkTy
      (λ γ → (α : aᴬ γ) → Bᴬ (γ , lift α))
      (λ γ γᴰ f → (x : aᴬ γ)(xᴰ : aᴰ γ γᴰ x) → Bᴰ _ (γᴰ , (lift xᴰ)) (f x))
      (λ γ γᴰ γˢ f fᴰ → (x : aᴬ γ) → Bˢ _ (γᴰ , lift (aˢ γ γᴰ γˢ x)) (γˢ , refl) (f x)
                                             (fᴰ x (aˢ γ γᴰ γˢ x)))

Π[] :
  {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)} →
  _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (Π {Δ} a B) σ) (Π {Γ} (tr {_}
  {_} {Ty Γ} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ}
  {σ}) (_[_]t {Γ} {Δ} {U {Δ}} a σ)) (tr {_} {_} {Ty Γ} (λ x → Ty
  (Γ ▶ x)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (tr {_} {_} {Ty Γ}
  (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}) (_[_]t {Γ}
  {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ}
  (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a)))))
Π[] = refl

app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
app {mkCon Γᴬ Γᴰ Γˢ}{mkTm aᴬ aᴰ aˢ}{mkTy Bᴬ Bᴰ Bˢ}(mkTm tᴬ tᴰ tˢ) =
  mkTm
    (λ {(γ , lift α) → tᴬ γ α})
    (λ {(γ , lift α) (γᴰ , lift αᴰ) → tᴰ γ γᴰ α αᴰ})
    (λ {(γ , lift α) (γᴰ , lift αᴰ)(γˢ , αˢ) →
      J (λ αᴰ αˢ → Bˢ _ (γᴰ , lift αᴰ) (γˢ , αˢ) (tᴬ γ α) (tᴰ γ γᴰ α αᴰ))
         (tˢ γ γᴰ γˢ α)
         αˢ})

app[] :
  {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)}
  {t : Tm Δ (Π {Δ} a B)} → _≡_ {_} {Tm (Γ ▶ El {Γ} (coe {_} {Tm Γ
  (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty
  Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
  (_[_]t {Γ} {Δ} {U {Δ}} a σ))) (tr {_} {_} {Ty Γ} (λ z → Ty (Γ ▶
  z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ}
  {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm
  Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ}
  {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El
  {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a))))} (tr2 {_}
  {_} {_} {Ty Γ} {λ z → Ty (Γ ▶ z)} (λ A → Tm (Γ ▶ A)) {_[_]T {Γ}
  {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)}
  {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ}
  {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a
  σ))} (El[] {Γ} {Δ} {σ} {a}) {_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El {Δ} a) σ} {Δ
  ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a))} {tr {_} {_} {Ty Γ} (λ
  z → Ty (Γ ▶ z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ
  (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty
  Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
  (_[_]t {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T
  {Γ} {Δ} (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a)))}
  refl (_[_]t {Γ ▶ _[_]T {Γ} {Δ} (El {Δ} a) σ} {Δ ▶ El {Δ} a} {B} (app
  {Δ} {a} {B} t) (_^_ {Γ} {Δ} σ (El {Δ} a)))) (app {Γ} {coe {_} {Tm Γ
  (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty
  Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
  (_[_]t {Γ} {Δ} {U {Δ}} a σ)} {tr {_} {_} {Ty Γ} (λ z → Ty (Γ ▶
  z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ}
  {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm
  Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ}
  {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El
  {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a)))} (tr {_}
  {_} {Ty Γ} (Tm Γ) {_[_]T {Γ} {Δ} (Π {Δ} a B) σ} {Π {Γ} (coe {_}
  {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _}
  {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ}
  {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a σ)) (tr {_} {_} {Ty Γ} (λ z → Ty
  (Γ ▶ z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T
  {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_}
  (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ}
  {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ}
  (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a))))} (Π[] {Γ}
  {Δ} {σ} {a} {B}) (_[_]t {Γ} {Δ} {Π {Δ} a B} t σ)))
app[] = refl

-- Non-inductive function
--------------------------------------------------------------------------------

ΠNI : ∀ {Γ}(A : Set) → (A → Ty Γ) → Ty Γ
ΠNI {mkCon Γᴬ Γᴰ Γˢ} A B = mkTy
  (λ γ            → (α : A) → B α .ᴬ γ)
  (λ γ γᴰ f       → (α : A) → B α .ᴰ γ γᴰ (f α))
  (λ γ γᴰ γˢ f fᴰ → (α : A) → B α .ˢ γ γᴰ γˢ (f α) (fᴰ α))

ΠNI[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A : Set}{B : A → Ty Δ}
        → ΠNI A B [ σ ]T ≡ ΠNI A (λ α → B α [ σ ]T)
ΠNI[] = refl

appNI : ∀ {Γ}{A}{B : A → Ty Γ} → Tm Γ (ΠNI A B) → (∀ α → Tm Γ (B α))
appNI t α = mkTm
  (λ γ → t .ᴬ γ α)
  (λ γ γᴰ → t .ᴰ γ γᴰ α)
  (λ γ γᴰ γˢ → t .ˢ γ γᴰ γˢ α)

appNI[] :
  {Γ Δ : Con} {σ : Sub Γ Δ} {A : Set} {B : A → Ty Δ}
  (t : Tm Δ (ΠNI {Δ} A B)) (α : A) →
  _≡_ {_} {Tm Γ (_[_]T {Γ} {Δ} (B α) σ)}
  (_[_]t {Γ} {Δ} {B α} (appNI {Δ} {A} {B} t α) σ)
  (appNI {Γ} {A} {λ α₁ → _[_]T {Γ} {Δ} (B α₁) σ}
   (tr {_} {_} {Ty Γ} (Tm Γ) {_[_]T {Γ} {Δ} (ΠNI {Δ} A B) σ}
    {ΠNI {Γ} A (λ α₁ → _[_]T {Γ} {Δ} (B α₁) σ)}
    (ΠNI[] {Γ} {Δ} {σ} {A} {B}) (_[_]t {Γ} {Δ} {ΠNI {Δ} A B} t σ))
   α)
appNI[] t α = refl

-- Recursors
--------------------------------------------------------------------------------

postulate
  Conʳ : S.Con → Con
  Tyʳ  : ∀ {Γ} → S.Ty Γ → Ty (Conʳ Γ)
  Tmʳ  : ∀ {Γ A} → S.Tm Γ A → Tm (Conʳ Γ) (Tyʳ A)
  Subʳ : ∀ {Γ Δ} → S.Sub Γ Δ → Sub (Conʳ Γ) (Conʳ Δ)

postulate
  ∙ʳ   : Conʳ S.∙ ≡ ∙
  ,ʳ   : ∀ Γ A → Conʳ (Γ S.▶ A) ≡ Conʳ Γ ▶ Tyʳ A
  []Tʳ : (Γ Δ : S.Con) (A : S.Ty Δ) (σ : S.Sub Γ Δ) →
          _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S._[_]T {Γ} {Δ} A σ))
          (_[_]T {Conʳ Γ} {Conʳ Δ} (Tyʳ {Δ} A) (Subʳ {Γ} {Δ} σ))
{-# REWRITE ∙ʳ ,ʳ []Tʳ #-}

postulate
  []tʳ : {Γ Δ : S.Con} {A : S.Ty Δ} (t : S.Tm Δ A) (σ : S.Sub Γ Δ) →
           _≡_ {j}
           {Tm (Conʳ Γ)
            (_[_]T {Conʳ Γ} {Conʳ Δ} (Tyʳ {Δ} A) (Subʳ {Γ} {Δ} σ))}
           (Tmʳ {Γ} {S._[_]T {Γ} {Δ} A σ} (S._[_]t {Γ} {Δ} {A} t σ))
           (_[_]t {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Tmʳ {Δ} {A} t)
            (Subʳ {Γ} {Δ} σ))

  idʳ  : {Γ : S.Con} →
           _≡_ {j} {Sub (Conʳ Γ) (Conʳ Γ)} (Subʳ {Γ} {Γ} (S.id {Γ}))
           (id {Conʳ Γ})

  ∘ʳ   : {Γ Δ : S.Con} {Σ : S.Con} {σ : S.Sub Δ Σ} {δ : S.Sub Γ Δ} →
           _≡_ {j} {Sub (Conʳ Γ) (Conʳ Σ)}
           (Subʳ {Γ} {Σ} (S._∘_ {Γ} {Δ} {Σ} σ δ))
           (_∘_ {Conʳ Γ} {Conʳ Δ} {Conʳ Σ} (Subʳ {Δ} {Σ} σ)
            (Subʳ {Γ} {Δ} δ))

  εʳ   : {Γ : S.Con} → _≡_ {j} {Sub (Conʳ Γ) ∙} (Subʳ {Γ} {S.∙} (S.ε {Γ})) (ε {Conʳ Γ})

  ,sʳ  : {Γ Δ : S.Con} (σ : S.Sub Γ Δ) {A : S.Ty Δ}
         (t : S.Tm Γ (S._[_]T {Γ} {Δ} A σ)) →
         _≡_ {j} {Sub (Conʳ Γ) (Conʳ Δ ▶ Tyʳ {Δ} A)}
         (Subʳ {Γ} {Δ S.▶ A} (S._,s_ {Γ} {Δ} σ {A} t))
         (_,s_ {Conʳ Γ} {Conʳ Δ} (Subʳ {Γ} {Δ} σ) {Tyʳ {Δ} A}
          (Tmʳ {Γ} {S._[_]T {Γ} {Δ} A σ} t))

  π₁ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} (σ : S.Sub Γ (Δ S.▶ A)) →
          _≡_ {j} {Sub (Conʳ Γ) (Conʳ Δ)} (Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))
          (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))

{-# REWRITE []tʳ idʳ ∘ʳ εʳ ,sʳ π₁ʳ #-}

postulate
  π₂ʳ : {Γ Δ : S.Con} {A : S.Ty Δ} (σ : S.Sub Γ (Δ S.▶ A)) →
          _≡_ {j}
          {Tm (Conʳ Γ)
           (_[_]T {Conʳ Γ} {Conʳ Δ} (Tyʳ {Δ} A)
            (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ)))}
          (Tmʳ {Γ} {S._[_]T {Γ} {Δ} A (S.π₁ {Γ} {Δ} {A} σ)}
           (S.π₂ {Γ} {Δ} {A} σ))
          (π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (Subʳ {Γ} {Δ S.▶ A} σ))

  Uʳ  : {Γ : S.Con} → _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S.U {Γ})) (U {Conʳ Γ})
{-# REWRITE π₂ʳ Uʳ #-}

postulate
  Elʳ : {Γ : S.Con} {a : S.Tm Γ (S.U {Γ})} → _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S.El {Γ} a))
                                                 (El {Conʳ Γ} (Tmʳ {Γ} {S.U {Γ}} a))
{-# REWRITE Elʳ #-}

postulate
  Πʳ : {Γ : S.Con} (a : S.Tm Γ (S.U {Γ})) (B : S.Ty (Γ S.▶ S.El {Γ} a)) →
        _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S.Π {Γ} a B))
        (Π {Conʳ Γ} (Tmʳ {Γ} {S.U {Γ}} a) (Tyʳ {Γ S.▶ S.El {Γ} a} B))
{-# REWRITE Πʳ #-}

postulate
  appʳ : {Γ : S.Con} {a : S.Tm Γ (S.U {Γ})} {B : S.Ty (Γ S.▶ S.El {Γ} a)}
          (t : S.Tm Γ (S.Π {Γ} a B)) →
          _≡_ {j}
          {Tm (Conʳ Γ ▶ El {Conʳ Γ} (Tmʳ {Γ} {S.U {Γ}} a))
           (Tyʳ {Γ S.▶ S.El {Γ} a} B)}
          (Tmʳ {Γ S.▶ S.El {Γ} a} {B} (S.app {Γ} {a} {B} t))
          (app {Conʳ Γ} {Tmʳ {Γ} {S.U {Γ}} a} {Tyʳ {Γ S.▶ S.El {Γ} a} B}
           (Tmʳ {Γ} {S.Π {Γ} a B} t))
{-# REWRITE appʳ #-}

postulate
  Idʳ : {Γ : S.Con} (a : S.Tm Γ S.U)(t u : S.Tm Γ (S.El a)) →
        Tyʳ (S.Id a t u) ≡ Id {Conʳ Γ}(Tmʳ a)(Tmʳ t)(Tmʳ u)
{-# REWRITE Idʳ #-}

postulate
  ΠNIʳ : {Γ : S.Con} (A : Set) → (B : A → S.Ty Γ)
       → Tyʳ (S.ΠNI A B) ≡ ΠNI A (λ α → Tyʳ (B α))
{-# REWRITE ΠNIʳ #-}

postulate
  appNIʳ :
    ∀ {Γ : S.Con} (A : Set) (B : A → S.Ty Γ)(t : S.Tm Γ (S.ΠNI A B)) α
    → Tmʳ (S.appNI t α) ≡ appNI {Conʳ Γ}{A} {λ α → Tyʳ (B α)}(Tmʳ t) α
{-# REWRITE appNIʳ #-}

postulate
  []tʳU : {Γ Δ : S.Con}{a : S.Tm Δ S.U}(σ : S.Sub Γ Δ) →
           Tmʳ {Γ} {S.U {Γ}} (S._[_]t {Γ} {Δ} {S.U {Δ}} a σ)
           ≡ _[_]t {Conʳ Γ}{Conʳ Δ}{U}(Tmʳ a) (Subʳ σ)
{-# REWRITE []tʳU #-}

postulate
  []tʳEl : {Γ Δ : S.Con}{a : S.Tm Δ S.U}(σ : S.Sub Γ Δ)
           (t : S.Tm Δ (S.El a)) → Tmʳ (t S.[ σ ]t) ≡
           _[_]t {Conʳ Γ}{Conʳ Δ}{El (Tmʳ a)}(Tmʳ t) (Subʳ σ)
{-# REWRITE []tʳEl #-}
