-- components of the set model
open import monlib
import Level 
open import HoTT renaming (_==_ to _≡_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂ ;
  _,_ to _Σ,_ ; _∘_ to _h∘_ ; Π to Πh
  )
-- copy of DeepCME, from Ambrus' repo

{-
Definition of the -ᶜ, -ᴹ and -ᴱ translations on the syntax.e

All three operations are defined in a single model, i.e. with
non-dependent recursion on the syntax. This is for technical reasons;
it is much easier in current Agda to define a single model with
multiple components than to define multiple models possibly depending
on each other.

So, if you look at the interpretation of contexts below, you see

  Con : Set i
  Con =
     ∃ λ (Γᶜ : Set₁) →
     ∃ λ (Γᴹ : Γᶜ → Set (suc ℓ)) →
         ((γ : Γᶜ) → Γᴹ γ → Set ℓ)

which is a Σ with three components, one for algebras (constructors),
one for dependent algebras (methods) and one for sections
(eliminators).

Likewise, we interpret the other sorts as Σ-s of the three components.

You can find some unreadable large type signatures here. Don't try to
read them, just look at the DeepSourceSyntax.agda file for the short
and comprehensible types. The large garbled types are just the
DeepSourceSyntax.agda types with printing of implicit arguments turned
on. We use these types because Agda can't reliably infer the implicit
arguments, and it's easier to just print out the whole explicit type
than to try and annotate manually.

-}

module SetModelComponents {ℓ : Level.Level} where


∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (lmax a b)
∃ = Σ _

infixl 5 _,_
infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t

-- Universe level we eliminate into
--------------------------------------------------------------------------------

i : Level.Level
i = Level.suc (Level.suc ℓ)

j : Level.Level
j = Level.suc ℓ

-- Base CwF (category with families), i.e. the explicit substitution calculus
--------------------------------------------------------------------------------

Con : Set i
Con =
   ∃ λ (Γᶜ : Set₁) →
   ∃ λ (Γᴹ : Γᶜ → Set (Level.suc ℓ)) →
       ((γ : Γᶜ) → Γᴹ γ → Set ℓ)

InCon : Con → Set _
InCon Γ = ∃ λ (γ : ₁ Γ) →  Σ _ ( ₂ (₂ Γ)  γ)
    

Ty : Con → Set i
Ty (Γᶜ Σ, Γᴹ Σ, Γᴱ) =
   ∃ λ (Aᶜ : Γᶜ → Set₁) →
   ∃ λ (Aᴹ : (γ : Γᶜ) → Γᴹ γ → Aᶜ γ → Set (Level.suc ℓ)) →
             (γ : Γᶜ)(γᴹ : Γᴹ γ)(γᴱ : Γᴱ γ γᴹ)(α : Aᶜ γ) → Aᴹ γ γᴹ α → Set ℓ

-- Tm : ∀ Γ → Ty Γ → Set j
Tm : ∀ Γ → Ty Γ → Set j
Tm (Γᶜ Σ, Γᴹ Σ, Γᴱ) (Aᶜ Σ, Aᴹ Σ, Aᴱ) =
  ∃ λ (tᶜ : (γ : Γᶜ) → Aᶜ γ) →
  ∃ λ (tᴹ : (γ : Γᶜ)(γᴹ : Γᴹ γ) → Aᴹ γ γᴹ (tᶜ γ)) →
            (γ : Γᶜ)(γᴹ : Γᴹ γ)(γᴱ : Γᴱ γ γᴹ) → Aᴱ γ γᴹ γᴱ (tᶜ γ) (tᴹ γ γᴹ)

Tms : Con → Con → Set j
Tms (Γᶜ Σ, Γᴹ Σ, Γᴱ) (Δᶜ Σ, Δᴹ Σ, Δᴱ) =
  ∃ λ (σᶜ : Γᶜ → Δᶜ) →
  ∃ λ (σᴹ : (γ : Γᶜ) → Γᴹ γ → Δᴹ (σᶜ γ)) →
            (γ : Γᶜ)(γᴹ : Γᴹ γ)(γᴱ : Γᴱ γ γᴹ) → Δᴱ (σᶜ γ) (σᴹ γ γᴹ)

_[_]T : ∀{Γ Δ} → Ty Δ → Tms Γ Δ → Ty Γ
_[_]T (Aᶜ Σ, Aᴹ Σ, Aᴱ) (σᶜ Σ, σᴹ Σ, σᴱ) =
  (λ γ → Aᶜ (σᶜ γ)) Σ,
  (λ γ γᴹ α → Aᴹ (σᶜ γ) (σᴹ γ γᴹ) α) Σ,
  (λ γ γᴹ γᴱ α αᴹ → Aᴱ (σᶜ γ) (σᴹ γ γᴹ) (σᴱ γ γᴹ γᴱ) α αᴹ)


∙ : Con
∙ =
  Lift ⊤ Σ,
  (λ _ → Lift ⊤) Σ,
  (λ _ _ → Lift ⊤)

_,_ : (Γ : Con) → Ty Γ → Con
(Γᶜ Σ, Γᴹ Σ, Γᴱ) , (Aᶜ Σ, Aᴹ Σ, Aᴱ) =
  Σ Γᶜ Aᶜ Σ,
  (λ {(γ Σ, α) → Σ (Γᴹ γ) λ γᴹ → Aᴹ γ γᴹ α}) Σ,
  (λ {(γ Σ, α)(γᴹ Σ, αᴹ) → Σ (Γᴱ γ γᴹ) λ γᴱ → Aᴱ γ γᴹ γᴱ α αᴹ})




id : ∀{Γ} → Tms Γ Γ
id {Γᶜ Σ, Γᴹ Σ, Γᴱ} =
  (λ γ → γ) Σ,
  (λ _ γᴹ → γᴹ) Σ,
  (λ _ _ γᴱ → γᴱ)

_∘_ : ∀{Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
(σᶜ Σ, σᴹ Σ, σᴱ) ∘ (δᶜ Σ, δᴹ Σ, δᴱ) =
  (λ γ → σᶜ (δᶜ γ)) Σ,
  (λ γ γᴹ → σᴹ (δᶜ γ) (δᴹ γ γᴹ)) Σ,
  (λ γ γᴹ γᴱ → σᴱ (δᶜ γ) (δᴹ γ γᴹ) (δᴱ γ γᴹ γᴱ))

ε : ∀{Γ} → Tms Γ ∙
ε {Γ} =
  (λ _ → lift tt) Σ,
  (λ _ _ → lift tt) Σ,
  (λ _ _ _ → lift tt)
  

_,s_ : ∀{Γ Δ A}(σ : Tms Γ Δ) → Tm Γ (A [ σ ]T) → Tms Γ (Δ , A)
_,s_ {Γ}{Δ}{A} (σᶜ Σ, σᴹ Σ, σᴱ) (tᶜ Σ, tᴹ Σ, tᴱ) =
  (λ γ → σᶜ γ Σ, tᶜ γ) Σ,
  (λ γ γᴹ → σᴹ γ γᴹ Σ, tᴹ γ γᴹ) Σ,
  (λ γ γᴹ γᴱ → σᴱ γ γᴹ γᴱ Σ, tᴱ γ γᴹ γᴱ)

π₁ : ∀{Γ Δ}{A : Ty Δ} → Tms Γ (Δ , A) →  Tms Γ Δ
π₁ (σᶜ Σ, σᴹ Σ, σᴱ) =
  (λ γ → ₁ (σᶜ γ)) Σ,
  (λ γ γᴹ → ₁ (σᴹ γ γᴹ)) Σ,
  (λ γ γᴹ γᴱ → ₁ (σᴱ γ γᴹ γᴱ))

_[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t (tᶜ Σ, tᴹ Σ, tᴱ) (σᶜ Σ, σᴹ Σ, σᴱ) =
  (λ γ → tᶜ (σᶜ γ)) Σ,
  (λ γ γᴹ → tᴹ (σᶜ γ) (σᴹ γ γᴹ)) Σ,
  (λ γ γᴹ γᴱ → tᴱ (σᶜ γ) (σᴹ γ γᴹ) (σᴱ γ γᴹ γᴱ))

π₂ : ∀{Γ Δ}{A : Ty Δ}(σ : Tms Γ (Δ , A))
   → Tm Γ (_[_]T {Γ} {Δ} A (π₁ {Γ} {Δ} {A} σ))
π₂ (σᶜ Σ, σᴹ Σ, σᴱ) =
  (λ γ → ₂ (σᶜ γ)) Σ,
  (λ γ γᴹ → ₂ (σᴹ γ γᴹ)) Σ,
  (λ γ γᴹ γᴱ → ₂ (σᴱ γ γᴹ γᴱ))

[id]T : ∀{Γ}{A : Ty Γ} → (A [ id ]T) ≡ A
[id]T = refl

[][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Tms Γ Δ}{δ : Tms Δ Σ}
        → (_[_]T {Γ} {Δ} (_[_]T {Δ} {Σ} A δ) σ)
          ≡
          (_[_]T {Γ} {Σ} A (_∘_ {Γ} {Δ} {Σ} δ σ))
[][]T {Γ} {Δ} {Σ} {A} {σ} {δ} = refl

idl : {Γ Δ : Con} {δ : Tms Γ Δ} → (_∘_ {Γ} {Δ} {Δ} (id {Δ}) δ) ≡ δ
idl = refl

idr : {Γ Δ : Con} {δ : Tms Γ Δ} → (_∘_ {Γ} {Γ} {Δ} δ (id {Γ})) ≡ δ
idr = refl

ass : ∀{Γ Δ Σ Ω}{σ : Tms Σ Ω}{δ : Tms Δ Σ}{ν : Tms Γ Δ}
      → (_∘_ {Γ} {Δ} {Ω} (_∘_ {Δ} {Σ} {Ω} σ δ) ν)
        ≡
        (_∘_ {Γ} {Σ} {Ω} σ (_∘_ {Γ} {Δ} {Σ} δ ν))
ass = refl

,∘ : ∀{Γ Δ Σ}{δ : Tms Γ Δ}{σ : Tms Σ Γ}{A : Ty Δ}{t : Tm Γ (A [ δ ]T)}
      → (_∘_ {Σ}{Γ}{Δ , A} (_,s_ {Γ}{Δ}{A} δ t) σ) ≡
        (_,s_ {Σ}{Δ}{A}(_∘_ {Σ}{Γ}{Δ} δ σ)(tr (Tm Σ) ([][]T {Σ}{Γ}{Δ}{A}{σ}{δ}) (_[_]t {Σ}{Γ}{A [ δ ]T} t σ)))
,∘ = refl

π₁β : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ Δ}{a : Tm Γ (A [ δ ]T)}
      → (π₁ {Γ}{Δ}{A}(_,s_ {Γ}{Δ}{A} δ a)) ≡ δ
π₁β = refl

πη : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ (Δ , A)}
      → _,s_ {Γ}{Δ}{A}(π₁ {Γ}{Δ}{A} δ)(π₂ {Γ}{Δ}{A} δ) ≡ δ
πη = refl

εη : ∀{Γ}{σ : Tms Γ ∙}
      → σ ≡ ε
εη = refl

π₂β : ∀{Γ Δ}{A : Ty Δ}{δ : Tms Γ Δ}{a : Tm Γ (A [ δ ]T)}
      → tr (λ x → Tm Γ (A [ x ]T)) (π₁β {Γ}{Δ}{A}{δ}{a}) (π₂ {Γ}{Δ}{A}(_,s_ {Γ}{Δ}{A} δ a)) ≡ a
π₂β = refl

wk : ∀{Γ}{A : Ty Γ} → Tms (Γ , A) Γ
wk {Γ}{A} = π₁ {Γ , A}{Γ}{A} id

vz : ∀{Γ}{A : Ty Γ} → Tm (Γ , A) (A [ wk ]T)
vz {Γ}{A} = π₂ {Γ , A}{Γ}{A} id

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ , B) (A [ wk ]T)
vs {Γ}{A}{B} x = _[_]t {Γ , B}{Γ}{A} x (wk {Γ}{B})

<_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Tms Γ (Γ , A)
<_> {Γ}{A} t = _,s_ {Γ}{Γ}{A} id (tr (Tm Γ) (! ([id]T {Γ}{A}) ) t)

infix 4 <_>

_^_ : {Γ Δ : Con}(σ : Tms Γ Δ)(A : Ty Δ) → Tms (Γ , A [ σ ]T) (Δ , A)
_^_ {Γ}{Δ} σ A =
  _,s_ {Γ , A [ σ ]T}{Δ}{A}
       (_∘_ {Γ , A [ σ ]T}{Γ}{Δ} σ wk)
       (tr (Tm (Γ , A [ σ ]T)) ([][]T {Γ , A [ σ ]T}{Γ}{Δ}{A}{wk{Γ}{A [ σ ]T}}{σ}) vz)

infixl 5 _^_
data isTelescope  (Γ : Con) : (Δ : Con) → Set i where
  is∙t : isTelescope Γ Γ
  is▶t : ∀ Δ → isTelescope Γ Δ → (A : Ty Δ) → isTelescope Γ (Δ , A)



Tel : Con → Set i
Tel Γ = Σ _ (isTelescope Γ)


_^^_ : (Γ : Con) (Δ : Tel Γ) → Con
_^^_ Γ Δ = ₁ Δ

∙t : (Γ : Con) → Tel Γ
∙t Γ = _ Σ, is∙t 


_▶t_  : ∀ {Γ}(Δ : Tel Γ) → Ty (Γ ^^ Δ) → Tel Γ
_▶t_ {Γ} Δ A = (₁ Δ , A) Σ, is▶t  _ (₂ Δ) A

^^∙t : (Γ : Con) → (Γ ^^ ∙t Γ) ≡ Γ
^^∙t Γ = refl

^^▶t : (Γ : Con)(Δ : Tel Γ)(A : Ty (Γ ^^ Δ)) →
  (Γ ^^ (Δ ▶t A)) ≡ ((Γ ^^ Δ) , A)
^^▶t Γ Δ A = refl


Telₛ : {Γ Δ : Con} → ∀ {T}(iT : isTelescope Δ T) (s : Tms Γ Δ)  → Σ (Tel Γ) (λ x → Tms (Γ ^^ x) (Δ ^^ (_ Σ, iT)))
Telₛ {_} {Δ} is∙t s  = ( _ Σ, is∙t ) Σ, s
Telₛ {Γ} {Δ} {.(Σ (₁ T) (₁ A) Σ, _ Σ, _)}  (is▶t T iT A) s  =
  (_ Σ, (is▶t (₁ (₁ (Telₛ iT s))) (₂ (₁ (Telₛ iT s))) (A [ ₂ (Telₛ iT s) ]T))) Σ,
  ((₂ (Telₛ iT s)) ^ A)

_[_]Te  : {Γ Δ : Con} → ∀ (T : Tel Δ) (s : Tms Γ Δ)  → Tel Γ
T [ s ]Te = ₁ (Telₛ (₂ T) s)

longₛ : {Γ Δ : Con} → ∀ (T : Tel Δ) (s : Tms Γ Δ)  → Tms (Γ ^^ (T [ s ]Te)) (Δ ^^ T)
longₛ T s = ₂ (Telₛ (₂ T) s)

longWk : ∀{Γ}{E : Ty Γ}(Δ : Tel Γ) → Tms ((Γ , E) ^^ (Δ [ wk ]Te)) (Γ ^^ Δ)
longWk {Γ}{E} Δ = longₛ Δ wk


wkC : (Γ : Con)(E : Ty Γ)(Δ : Tel Γ) → Tel (Γ , E)
wkC Γ E Δ = Δ [ wk ]Te

wk∙t : {Γ : Con}{Ex : Ty Γ} → wkC Γ Ex (∙t _) ≡ ∙t _
wk∙t = refl

liftT : (Γ : Con)(Δ : Tel Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ)) → Ty ((Γ , Ex) ^^ wkC Γ Ex Δ)
liftT Γ Δ Ex A = A [ longWk Δ ]T

liftt : (Γ : Con)(Δ : Tel Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ))(t : Tm (Γ ^^ Δ) A) →
  Tm ((Γ , Ex) ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A)
liftt Γ Δ Ex A t = _[_]t
   -- {Γ = (Γ , Ex) ^^ wkC Γ Ex Δ}
   -- {Δ = Γ ^^ Δ}
   {A = A}
   t
   -- (longWk {Γ = Γ}{E = Ex} Δ)
   (longWk  Δ)


wkT : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ) → Ty (Γ , Ex)
wkT Γ Ex A = liftT Γ (∙t Γ) Ex A

wkt : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ)(t : Tm Γ A) → Tm (Γ , Ex) (wkT Γ Ex A)
wkt Γ Ex A t = liftt Γ (∙t Γ) Ex A t

V0 : (Γ : Con)(A : Ty Γ) → Tm (Γ , A) (wkT Γ A A)
V0 Γ A = vz

subTel : {Γ : Con}(Ex : Ty Γ)(Δ : Tel (Γ , Ex)) (z : Tm Γ Ex) → Tel Γ
subTel {Γ}Ex Δ z = Δ [ <_> {A = Ex} z  ]Te


l-subT : {Γ : Con}(E : Ty Γ)(Δ : Tel (Γ , E)) (z : Tm Γ E)
  (A : Ty ((Γ , E) ^^ Δ)) → Ty (Γ ^^ subTel E Δ z)
l-subT {Γ} E Δ z A = A [ longₛ Δ (<_> {A = E} z) ]T


subT : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → Ty (Γ , Ex) → Ty Γ
subT Γ Ex = l-subT Ex (∙t _)

l-subt : {Γ : Con}(Ex : Ty Γ)(Δ : Tel (Γ , Ex))(t : Tm Γ Ex) →
  (A : Ty ((Γ , Ex) ^^ Δ) ) (u : Tm _ A )→
  Tm (Γ ^^ (subTel Ex Δ t)) (l-subT Ex Δ  t A)
l-subt {Γ} E Δ z A t = _[_]t {A = A} t ( longₛ Δ (<_> {A = E} z) )
 
subt : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → (A : Ty (Γ , Ex) ) (u : Tm _ A )→
  Tm (Γ ^^ (∙t Γ)) (l-subT Ex (∙t _)  t A)
subt Γ Ex t A u = l-subt Ex (∙t _) t A u

-- Universe
--------------------------------------------------------------------------------

U : ∀{Γ} → Ty Γ
U {Γᶜ Σ, Γᴹ Σ, Γᴱ} =
  (λ _ → Set) Σ,
  (λ _ _ T → T → Set ℓ) Σ,
  λ _ _ _ T Tᴹ → (α : T) → Tᴹ α


El : ∀{Γ}(a : Tm Γ U) → Ty Γ
El (aᶜ Σ, aᴹ Σ, aᴱ) =
  (λ γ → Lift (aᶜ γ)) Σ,
  (λ {γ γᴹ (lift α) → Lift (aᴹ γ γᴹ α)}) Σ,
  (λ {γ γᴹ γᴱ (lift α) (lift αᴹ) → aᴱ γ γᴹ γᴱ α ≡ αᴹ})


-- Inductive functions
--------------------------------------------------------------------------------

Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ , El a)) → Ty Γ
Π (aᶜ Σ, aᴹ Σ, aᴱ) (Bᶜ Σ, Bᴹ Σ, Bᴱ) =
  (λ γ → (α : aᶜ γ) → Bᶜ (γ Σ, lift α)) Σ,
  (λ γ γᴹ f → (α : aᶜ γ)(αᴹ : aᴹ γ γᴹ α) → Bᴹ (γ Σ, lift α) (γᴹ Σ, lift αᴹ) (f α)) Σ,
  (λ γ γᴹ γᴱ f fᴹ → (α : aᶜ γ) → Bᴱ _ (γᴹ Σ, lift (aᴱ γ γᴹ γᴱ α)) (γᴱ Σ, refl)
                                      (f α) (fᴹ α (aᴱ γ γᴹ γᴱ α)))


app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ , El a)} → Tm Γ (Π a B) → Tm (Γ , El a) B
app {Γᶜ Σ, Γᴹ Σ, Γᴱ}{aᶜ Σ, aᴹ Σ, aᴱ}{Bᶜ Σ, Bᴹ Σ, Bᴱ}(tᶜ Σ, tᴹ Σ, tᴱ) =
  (λ {(γ Σ, lift α) → tᶜ γ α}) Σ,
  (λ {(γ Σ, lift α) (γᴹ Σ, lift αᴹ) → tᴹ γ γᴹ α αᴹ}) Σ,
  (λ {(γ Σ, lift α) (γᴹ Σ, lift αᴹ)(γᴱ Σ, αᴱ) →
    J (λ αᴹ αᴱ → Bᴱ _ (γᴹ Σ, lift αᴹ) (γᴱ Σ, αᴱ) (tᶜ γ α) (tᴹ γ γᴹ α αᴹ))
       (tᴱ γ γᴹ γᴱ α)
       αᴱ})

app' : (Γ : Con)(A : Tm Γ U )(B : Ty (Γ , El A)) (t : Tm Γ (Π A B)) (u : Tm Γ (El A)) →
       Tm Γ (subT Γ (El A) u B)
app' Γ A B t u =
  _[_]t
  {A = B}
  (app {Γ}{A}{B} t)
   ( <_> {A = El A} u  )
