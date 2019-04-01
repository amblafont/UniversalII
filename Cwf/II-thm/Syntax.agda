{-
Paper: section 3.1.

This file postulates the syntax of the theory of QIIT signatures, plus
REWRITE rules to reflect computation rules to definitional equalities.

The derived equalities at the end of the file are not proven
here. This is a TODO; nonetheless these are either admissible
equations (which are easily seen to be admissible, and also proven in
Ambrus Kaposi's PhD thesis), or just specializations of other rules to
particular arguments.
-}

{-# OPTIONS --rewriting #-}

module Syntax where

open import Lib hiding (id; _∘_)

infixl 7 _[_]T
infixl 5 _,s_
infixr 6 _∘_
infixl 8 _[_]t
infixl 3 _▶_
infixl 8 _$_

postulate
  Con : Set
  Ty  : Con → Set
  Tm  : ∀ Γ → Ty Γ → Set
  Sub : Con → Con → Set

  ∙     : Con
  _▶_   : (Γ : Con) → Ty Γ → Con

  _[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

  id    : ∀{Γ} → Sub Γ Γ
  _∘_   : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  ε     : ∀{Γ} → Sub Γ ∙
  _,s_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : Ty Δ} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
  π₁    : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (Δ ▶ A) → Sub Γ Δ

  _[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  π₂    : ∀{Γ Δ}{A : Ty Δ}(σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)

  [id]T : ∀{Γ}{A : Ty Γ} → A [ id ]T ≡ A
  [][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Sub Γ Δ}{δ : Sub Δ Σ}
          → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T

  idl   : ∀{Γ Δ}{σ : Sub Γ Δ} → (id ∘ σ) ≡ σ
  idr   : ∀{Γ Δ}{σ : Sub Γ Δ} → (σ ∘ id) ≡ σ
  ass   : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
        → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

  ,∘    : ∀{Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ}{t : Tm Γ (A [ δ ]T)}
        → ((δ ,s t) ∘ σ) ≡ ((δ ∘ σ) ,s tr (Tm Σ) [][]T (t [ σ ]t))
  π₁β   : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
        → (π₁ (σ ,s t)) ≡ σ
  πη    : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ (Δ ▶ A)}
        → (π₁ σ ,s π₂ σ) ≡ σ
  εη    : ∀{Γ}{σ : Sub Γ ∙}
        → σ ≡ ε
  π₂β   : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
        → π₂ (σ ,s t) ≡ tr (λ σ → Tm Γ (A [ σ ]T)) (π₁β ⁻¹) t

wk : ∀{Γ}{A : Ty Γ} → Sub (Γ ▶ A) Γ
wk = π₁ id

vz : ∀{Γ}{A : Ty Γ} → Tm (Γ ▶ A) (A [ wk ]T)
vz = π₂ id

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs x = x [ wk ]t

<_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▶ A)
< t > = id ,s tr (Tm _) ([id]T ⁻¹) t

infix 4 <_>

_^_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {Γ} {Δ} σ A = σ ∘ wk ,s coe (Tm _ & [][]T) (vz {Γ}{A [ σ ]T})

infixl 5 _^_


-- Universe
--------------------------------------------------------------------------------

postulate
  U    : ∀{Γ} → Ty Γ
  U[]  : ∀{Γ Δ}{σ : Sub Γ Δ} → (U [ σ ]T) ≡ U
  El   : ∀{Γ}(a : Tm Γ U) → Ty Γ
  El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (coe (Tm Γ & U[]) (a [ σ ]t)))

-- Identity
--------------------------------------------------------------------------------

-- postulate
--   Id   : ∀ {Γ}(a : Tm Γ U) → Tm Γ (El a) → Tm Γ (El a) → Ty Γ
--   Id[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{t u : Tm Δ (El a)}
--         → Id a t u [ σ ]T ≡ Id (coe (Tm Γ & U[]) (a [ σ ]t))
--                                (coe (Tm Γ & El[]) (t [ σ ]t))
--                                (coe (Tm Γ & El[]) (u [ σ ]t))

--   Reflect : ∀ {Γ a}{t u : Tm Γ (El a)} → Tm Γ (Id a t u) → t ≡ u

-- Inductive functions
--------------------------------------------------------------------------------
postulate
  Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ

  Π[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a)}
      → (Π a B) [ σ ]T ≡ Π (tr (Tm Γ) U[] (a [ σ ]t))
                           (tr (λ x → Ty (Γ ▶ x)) El[] (B [ σ ^ El a ]T))

  app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B

  app[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a)}{t : Tm Δ (Π a B)}
          → tr2 (λ A → Tm (Γ ▶ A)) El[] refl (app t [ σ ^ El a ]t)
          ≡ app (tr (Tm _) Π[] (t [ σ ]t))

_$_ : ∀ {Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}(t : Tm Γ (Π a B))(u : Tm Γ (El a)) → Tm Γ (B [ < u > ]T)
t $ u = (app t) [ < u > ]t


-- Non-inductive functions
--------------------------------------------------------------------------------
postulate
  ΠNI : ∀ {Γ}(A : Set) → (A → Ty Γ) → Ty Γ

  ΠNI[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A : Set}{B : A → Ty Δ}
          → ΠNI A B [ σ ]T ≡ ΠNI A (λ α → B α [ σ ]T)

  appNI : ∀ {Γ}{A}{B : A → Ty Γ} → Tm Γ (ΠNI A B) → (∀ α → Tm Γ (B α))

  appNI[] :  ∀ {Γ Δ}{σ : Sub Γ Δ}{A}{B : A → Ty Δ}(t : Tm Δ (ΠNI A B)) α
             → appNI t α [ σ ]t ≡ appNI (tr (Tm Γ) ΠNI[] (t [ σ ]t)) α

--------------------------------------------------------------------------------
-- Syntax rewrite rules & derived equalities
--------------------------------------------------------------------------------

  -- [id]T [][]T idl idr ass U[] El[] Π[] Id[] ΠNI[] ,∘ π₁β π₂β
{-# REWRITE
  [id]T [][]T idl idr ass U[] El[] Π[]  ΠNI[] ,∘ π₁β π₂β
#-}
-- {-# REWRITE Πₙᵢ[] #-} -  - not accepted by Agda

postulate
  [id]Trefl : ∀{Γ}{A : Ty Γ} → [id]T {Γ}{A} ≡ refl
  [][]Trefl : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Sub Γ Δ}{δ : Sub Δ Σ} → [][]T {Γ}{Δ}{Σ}{A}{σ}{δ} ≡ refl
  idlrefl   : {Γ Δ : Con} {σ : Sub Γ Δ} → idl {σ = σ} ≡ refl
  idrrefl   : {Γ Δ : Con} {σ : Sub Γ Δ} → idr {σ = σ} ≡ refl
  assrefl   : {Γ Δ : Con} {Σ : Con} {Ω : Con} {σ : Sub Σ Ω} {δ : Sub Δ Σ}{ν : Sub Γ Δ} → ass {σ = σ}{δ}{ν} ≡ refl
  U[]refl   : {Γ Δ : Con} {σ : Sub Γ Δ} → U[] {σ = σ} ≡ refl
  El[]refl  : {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ U} → El[] {σ = σ}{a} ≡ refl
  Π[]refl   : {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ U} {B : Ty (Δ ▶ El a)} → Π[] {σ = σ}{a}{B} ≡ refl
  -- Id[]refl  : {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ U} {t u : Tm Δ (El a)} → Id[] {σ = σ}{a}{t}{u} ≡ refl
  ΠNI[]refl : {Γ Δ : Con} {σ : Sub Γ Δ} {A : Set} {B : A → Ty Δ} → ΠNI[] {σ = σ}{A}{B} ≡ refl
  ,∘refl    : ∀{Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ}{t : Tm Γ (A [ δ ]T)}
              → ,∘ {δ = δ}{σ}{A}{t} ≡ refl
  π₁βrefl   : ∀{Γ Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} → π₁β{A = A}{σ}{t} ≡ refl
  π₂βrefl   : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ]T)} → π₂β {A = A}{σ}{t} ≡ refl

  -- [id]Trefl [][]Trefl idlrefl idrrefl assrefl U[]refl El[]refl Π[]refl
  -- Id[]refl ΠNI[]refl ,∘refl π₁βrefl π₂βrefl
{-# REWRITE
   [][]Trefl idlrefl idrrefl assrefl U[]refl El[]refl Π[]refl
   ΠNI[]refl ,∘refl π₁βrefl π₂βrefl
#-}

-- Derived equalities (TODO: prove them).
-- We need a bunch of specializations for term subst laws to placate Agda's weak
-- REWRITE LHS matching.
postulate
  π₁∘   : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ} → π₁ σ ∘ δ ≡ π₁ (σ ∘ δ)
{-# REWRITE π₁∘ #-}

postulate
  π₂∘Ne   : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Sub Δ (Σ ▶ A)}{δ : Sub Γ Δ}
        → π₂ σ [ δ ]t ≡ π₂ (σ ∘ δ)
{-# REWRITE π₂∘Ne #-}

postulate
  [id]t : ∀ {Γ}{A}{t : Tm Γ A} → t [ id ]t ≡ t
{-# REWRITE [id]t #-}

postulate
  [][]tU  : ∀ {Γ Δ Σ : Con}{σ : Sub Γ Δ} {δ : Sub Δ Σ}(t : Tm Σ U)
          → t [ δ ]t [ σ ]t ≡ t [ δ ∘ σ ]t
{-# REWRITE [][]tU #-}

postulate
  [][]tEl : ∀ {Γ Δ Σ : Con}{σ : Sub Γ Δ} {δ : Sub Δ Σ}{a : Tm Σ U}(t : Tm Σ (El a))
          → t [ δ ]t [ σ ]t ≡ t [ δ ∘ σ ]t
  [][]tNe : {Γ Δ : Con} {Σ₁ : Con} {A : Ty Σ₁} {σ : Sub Γ Δ} {δ : Sub Δ Σ₁}
           {t : Tm Σ₁ A} →
           t [ δ ]t [ σ ]t ≡ t [ δ ∘ σ ]t
{-# REWRITE [][]tEl [][]tNe #-}

postulate
  vz<>Elσ : ∀ {Γ Δ}{a}{t : Tm Γ (El a)}{σ : Sub Δ Γ}
        → vz [ < t [ σ ]t > ]t ≡ t [ σ ]t
{-# REWRITE vz<>Elσ #-}

postulate
  π₂∘U  : ∀{Γ Δ Σ}{σ : Sub Δ (Σ ▶ U)}{δ : Sub Γ Δ}
        → _[_]t {Γ}{Δ}{U}(π₂ σ) δ ≡ π₂ (σ ∘ δ)
{-# REWRITE π₂∘U #-}
postulate
  π₂∘El : ∀{Γ Δ Σ}{a}{σ : Sub Δ (Σ ▶ El a)}{δ : Sub Γ Δ}
        → _[_]t {Γ}{Δ}{El (a [ π₁ σ ]t)} (π₂ σ) δ ≡ π₂ (σ ∘ δ)
{-# REWRITE π₂∘El #-}

{-# REWRITE appNI[] #-}
