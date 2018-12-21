-- components of the set model
open import monlib
import Level 
import Syntax as S
open import SyntaxIsRecord
open import SyntaxIsRecord2
open import HoTT renaming (_==_ to _≡_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂ )
  hiding ( _∘_ ; Π )

open import ModelRecord
  
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

module SetModelComponentsACDS (Ω : S1.Con) where

open import Composition as C


∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (lmax a b)
∃ = Σ _

SSub : ∀ Γ Δ → Set
SSub Γ Δ = ∃ (S.Subw Γ Δ)

_⊢_S∘_ : ∀ (Y : S1.Con){Γ}{Δ}(σ : SSub Γ Δ)(δ : SSub (₁ Y) Γ) → SSub (₁ Y) Δ
Y ⊢ σ S∘ δ = _ , ∘w (₂ σ) (₂ Y) (₂ δ)



-- infixl 5 _,_
-- infixl 40 _[_]T
-- infixl 8 _[_]t

_⊢_[_]T : (Γ : S1.Con){Δ : S.Conp} (A : ∃ (S.Tyw Δ)) (σ : SSub (₁ Γ) Δ) → S1.Ty Γ
_⊢_[_]T  Γ A  σ  = _ , (S.Tywₛ (₂ A) (₂ Γ) (₂ σ))

_⊢_[_]t : (Γ : S1.Con){Δ : S.Conp} → ∀ {A}(t : ∃ (S.Tmw Δ A)) (σ : SSub (₁ Γ) Δ) → ∃ (S.Tmw (₁ Γ) (A S.[ ₁ σ ]T))
_⊢_[_]t  Γ t  σ  = _ , (S.Tmwₛ (₂ t) (₂ Γ) (₂ σ))

-- [∘]T : ∀ (Γ : S1.Con)(A : S1.Ty Γ) (σ : SSub (₁ Γ) Δ)

Sπ₁ : ∀ {Γ Δ A} (v  : SSub Γ (Δ S.▶p A)) → SSub Γ Δ
Sπ₁ (_ , S.,sw vw Aw tw) = _ , vw

Sπ₂ : ∀ {Γ Δ A} (v  : SSub Γ (Δ S.▶p A)) → ∃ (S.Tmw  Γ (A S.[ ₁ (Sπ₁ v) ]T))
Sπ₂ (_ , S.,sw vw Aw tw) = _ , tw

-- infixl 5 _,s_
-- infix  6 _∘_
-- 4e tentative: full substitution


-- data SynSub (Γ : S.Conp) : S.Conp → Set
--   | nilₛ :  SynSub Γ S.∙p
--   | extₛ : 

-- 3e tentative
-- de extends (₁ Ω) (₁ Γⁱ S.▶p ₁ Aⁱ) je veux pouvoir extraire une variable du bon type
{-
extends : S.Conp → S.Conp → Set
extends Γ₁ Γ₂ = ∃ λ Δ → Γ₁ ≡ (Γ₂ S.^^ Δ)

extTyp :  (n : ℕ) → S.Typ → S.Typ
extTmp : (n : ℕ)  → S.Tmp → S.Tmp
-- extTy {Γ₁}{Γ₂} e A = {!!}
extTyp n S.Up = S.Up
extTyp n (S.Elp x) = S.Elp (extTmp n x)
extTyp n (S.ΠΠp A B) = {!!}

extTmp n t = {!!}
-}



{- 
-- 2e tentative
-- the _▶_ computes well, but
-- not satisfactory because U does not computes well
data extends (Γ : S.Conp) : S.Conp → Set where
  ext-id : extends Γ Γ
  ext-▶ : ∀ Γ' A → S.Tyw Γ' A → extends Γ (Γ' S.▶p A) → extends Γ Γ'

extendsΔT : ∀ (Γ : S1.Con) {Γ'} (e : extends (₁ Γ) Γ') → (A : ∃ (S.Tyw Γ')) → S1.Ty Γ
-- extendsΔT {Γ} {Γ'} e A = {!e!}
extendsΔT Γ  ext-id A = A
extendsΔT Γ {Γ''} (ext-▶ Γ'' B Bw e) A = _ , ₂ (extendsΔT Γ e (_ , S.wkTw Bw (₂ A)))

extendsΔt : ∀ (Γ : S1.Con) {Γ'} (e : extends (₁ Γ) Γ') →  (A : ∃ (S.Tyw Γ'))(t : ∃ (S.Tmw Γ' (₁ A))) → S1.Tm Γ (extendsΔT Γ e A)
-- extendsΔt Γ {Γ'} e A t = {!e!}
extendsΔt Γ {.(₁ Γ)} ext-id A t = t
extendsΔt Γ {Γ''} (ext-▶ Γ'' B Bw e) A t = _ , ₂ (extendsΔt Γ e(_ , S.wkTw Bw (₂ A))
   (_ , S.lifttw Bw (S.∙p )(₂ t)) )
-- -}

{-
-- 1e tentative

extends : S1.Con → S1.Con → Set
extends Γ₁ Γ₂ = ∃ λ Δ → ₁ Γ₁ ≡ (₁ Γ₂ S.^^ Δ)

extendsΔT : ∀ Γ (Δ : S1.Telescope Γ) (A : S1.Ty Γ) → S1.Ty (Γ S1.^^ Δ)
extendsΔT Γ (S.∙p , Δw) A = A
extendsΔT Γ ((Δ S.▶p x) , S.▶w Δw Aw) B = S1.wkT (_ , Δw) (_ , Aw) (extendsΔT Γ (_ , Δw) B)

extendsΔt : ∀ Γ (Δ : S1.Telescope Γ) (A : S1.Ty Γ)( t : S1.Tm Γ A) → S1.Tm (Γ S1.^^ Δ) (extendsΔT Γ Δ A)
-- extendsΔt Γ (Δp , Δw) A t = {!!}
extendsΔt Γ (S.∙p , Δw) A t = t
extendsΔt Γ ((Δp S.▶p x) , S.▶w Δw Aw) B t = S1.wkt (_ , Δw) (_ , Aw) (extendsΔT Γ (_ , Δw) B)
   (extendsΔt Γ (_ , Δw) B t)

extendsT : ∀ {Γ₁ Γ₂ : S1.Con} → extends Γ₁  Γ₂ → (A : S1.Ty Γ₂) → S1.Ty Γ₁
extendsT {Γ1 , Γ1w} {Γ2 , Γ2w} (Δ , refl)  = extendsΔT (Γ2 , Γ2w) (Δ , Γ1w) 

extendst : ∀ {Γ₁ Γ₂ : S1.Con} → (e : extends Γ₁  Γ₂) → (A : S1.Ty Γ₂)( t : S1.Tm Γ₂ A) →
  S1.Tm Γ₁ (extendsT {Γ₁}{Γ₂} e A)
extendst {Γ1 , Γ1w} {Γ2 , Γ2w} (Δ , refl)  =  extendsΔt (Γ2 , Γ2w) (Δ , Γ1w)  
  
-}


i : Level.Level
i = Level.suc (Level.suc Level.zero)

j : Level.Level
j = Level.suc Level.zero

record Con : Set i where
  constructor mkCon
  field
    ⁱ : S1.Con
    ᴬ : Set₁
    ᴰ : ᴬ → Set₁
    ˢ : (γ : ᴬ) → ᴰ γ → Set
    -- ᶜ : (e : extends Ω ⁱ) → ᴬ
    ᶜ : (e : SSub (₁ Ω ) (₁ ⁱ)) → ᴬ
open Con public

record Ty (Γ : Con) : Set i where
  constructor mkTy
  field
    ⁱ : S1.Ty (ⁱ Γ)
    ᴬ : Γ .ᴬ → Set₁
    ᴰ : (γ : Con.ᴬ Γ) → Con.ᴰ Γ γ → ᴬ γ → Set₁
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Γ .ˢ γ γᴰ)(α : ᴬ γ) → ᴰ γ γᴰ α → Set
    -- ᶜ : ∀ e → (t : S1.Tm Ω (extendsT {Ω}{Con.ⁱ Γ} e ⁱ)) → ᴬ (Con.ᶜ Γ e)
    ᶜ : ∀ (v : SSub (₁ Ω) (₁ (Con.ⁱ Γ))) → (t : S1.Tm Ω (Ω ⊢ ⁱ [ v ]T)) → ᴬ (Con.ᶜ Γ v)
open Ty public


record Tm (Γ : Con)(A : Ty Γ) : Set j where
  constructor mkTm
  field
    ⁱ : S1.Tm (ⁱ Γ) (ⁱ A)
    ᴬ : (γ : Con.ᴬ Γ) → Ty.ᴬ A γ
    ᴰ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ) → Ty.ᴰ A γ γᴰ (ᴬ γ)
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Con.ˢ Γ γ γᴰ) → Ty.ˢ A γ γᴰ γˢ (ᴬ γ) (ᴰ γ γᴰ)
    ᶜ : (v : SSub (₁ Ω) (₁ (Con.ⁱ Γ))) → Ty.ᶜ A v (Ω ⊢ ⁱ [ v ]t) ≡ ᴬ (Con.ᶜ Γ v)
open Tm public

record Sub (Γ Δ : Con) : Set j where
  constructor mkSub
  field
    ⁱ : SSub (₁ (ⁱ Γ))(₁ (ⁱ Δ))
    ᴬ : Con.ᴬ Γ → Con.ᴬ Δ
    ᴰ : (γ : Con.ᴬ Γ) → Con.ᴰ Γ γ → Con.ᴰ Δ (ᴬ γ)
    ˢ : (γ : Con.ᴬ Γ)(γᴰ : Con.ᴰ Γ γ)(γˢ : Con.ˢ Γ γ γᴰ) → Con.ˢ Δ (ᴬ γ) (ᴰ γ γᴰ)
    ᶜ : (v : SSub (₁ Ω) (₁ (Con.ⁱ Γ))) → Con.ᶜ Δ (Ω ⊢ ⁱ S∘ v) ≡ ᴬ (ᶜ Γ v)
    -- Ty.ᶜ A v (Ω ⊢ ⁱ [ v ]t) ≡ ᴬ (Con.ᶜ Γ v)
open Sub public

∙ : Con
∙ = mkCon
  (S1.∙ )
  (Lift ⊤)
  (λ _ → Lift ⊤)
  (λ _ _ → Lift ⊤)
  λ e → lift tt

_▶_ : (Γ : Con) → Ty Γ → Con
(mkCon Γⁱ Γᴬ Γᴰ Γˢ Γᶜ) ▶ (mkTy Aⁱ Aᴬ Aᴰ Aˢ Aᶜ) = mkCon
  (Γⁱ S1.▶ Aⁱ)
  (Σ Γᴬ Aᴬ)
  (λ {(γ , α) → Σ (Γᴰ γ) λ γᴰ → Aᴰ γ γᴰ α})
  (λ {(γ , α)(γᴰ , αᴰ) → Σ (Γˢ γ γᴰ) λ γˢ → Aˢ γ γᴰ γˢ α αᴰ})
  λ v  → (Γᶜ (Sπ₁ v)) , Aᶜ (Sπ₁ v) (Sπ₂ v)

-- I need composition of substitutions
_[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {Γ} {Δ}(mkTy Aⁱ Aᴬ Aᴰ Aˢ Aᶜ) (mkSub σⁱ σᴬ σᴰ σˢ σᶜ) = mkTy
   (ⁱ Γ ⊢ Aⁱ [ σⁱ ]T)
  (λ γ → Aᴬ (σᴬ γ))
  (λ γ γᴰ α → Aᴰ (σᴬ γ) (σᴰ γ γᴰ) α)
  (λ γ γᴰ γˢ α αᴰ → Aˢ (σᴬ γ) (σᴰ γ γᴰ) (σˢ γ γᴰ γˢ) α αᴰ)
  λ v t → tr Aᴬ (σᶜ v)  (Aᶜ (Ω ⊢ σⁱ S∘ v)
    (tr {A = S1.Ty Ω }
     (S1.Tm Ω )
     {x = Ω ⊢ ⁱ Γ ⊢ Aⁱ [ σⁱ ]T [ v ]T}
     {y = Ω ⊢ Aⁱ [ Ω ⊢ σⁱ S∘ v ]T}
     (Subtype=-out (S.Tyw (₁ Ω) , (λ a → S.TywP (₁ Ω) a)) (! ([∘]T (₁ Aⁱ) _ _))) 
     t)
     )

-- id : ∀{Γ} → Sub Γ Γ
-- id {mkCon Γⁱ Γᴬ Γᴰ Γˢ Γᶜ} = mkSub
--   {!!}
--   (λ γ → γ)
--   (λ _ γᴰ → γᴰ)
--   (λ _ _ γˢ → γˢ)
--   {!!}

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


-}

infix 4 <_>

_^_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {Γ} {Δ} σ A = mkSub
  (S.keep (₁ (ⁱ σ)) , S.keepw (₂ (ⁱ Γ)) (₂ (ⁱ σ)) (₂ (ⁱ A)))
  (λ γ → ᴬ σ (₁ γ) , ₂ γ) (λ γ γᴰ → ᴰ σ (₁ γ) (₁ γᴰ) , ₂ γᴰ)
  (λ γ γᴰ γˢ → ˢ σ (₁ γ) (₁ γᴰ) (₁ γˢ) , ₂ γˢ)
  λ v → {!ᶜ σ (Sπ₁ v)!}

infixl 5 _^_
-- infixl 5 _^_




-- Universe
--------------------------------------------------------------------------------

{- 
U : ∀{Γ} → Ty Γ
U {mkCon Γⁱ Γᴬ Γᴰ Γˢ Γᶜ} = mkTy
   (S1.U Γⁱ)
  (λ _ → Set)
  (λ _ _ T → T → Set)
  (λ _ _ _ T Tᴰ → (α : T) → Tᴰ α)
  λ e t → {!!}


El : ∀{Γ}(a : Tm Γ U) → Ty Γ
El (mkTm aᴬ aᴰ aˢ) = mkTy
  (λ γ → Lift (aᴬ γ))
  (λ {γ γᴰ (lift α) → Lift (aᴰ γ γᴰ α)})
  (λ {γ γᴰ γˢ (lift α) (lift αᴰ) → aˢ γ γᴰ γˢ α ≡ αᴰ})


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

-- Telescopes
data isTelescope  (Γ : Con) : (Δ : Con) → Set i where
  is∙t : isTelescope Γ Γ
  is▶t : ∀ Δ → isTelescope Γ Δ → (A : Ty Δ) → isTelescope Γ (Δ ▶ A)



Tel : Con → Set i
Tel Γ = Σ _ (isTelescope Γ)


_^^_ : (Γ : Con) (Δ : Tel Γ) → Con
_^^_ Γ Δ = ₁ Δ

∙t : (Γ : Con) → Tel Γ
∙t Γ = _ , is∙t 


_▶t_  : ∀ {Γ}(Δ : Tel Γ) → Ty (Γ ^^ Δ) → Tel Γ
_▶t_ {Γ} Δ A = (₁ Δ ▶ A) , is▶t  _ (₂ Δ) A

^^∙t : (Γ : Con) → (Γ ^^ ∙t Γ) ≡ Γ
^^∙t Γ = refl

^^▶t : (Γ : Con)(Δ : Tel Γ)(A : Ty (Γ ^^ Δ)) →
  (Γ ^^ (Δ ▶t A)) ≡ ((Γ ^^ Δ) ▶ A)
^^▶t Γ Δ A = refl


Telₛ : {Γ Δ : Con} → ∀ {T}(iT : isTelescope Δ T) (s : Sub Γ Δ)  → Σ (Tel Γ) (λ x → Sub (Γ ^^ x) (Δ ^^ (_ , iT)))
Telₛ {_} {Δ} is∙t s  = ( _ , is∙t ) , s
-- Telₛ {Γ} {Δ} {.(Σ (₁ T) (₁ A) , _ , _)}  (is▶t T iT A) s  =
Telₛ {Γ} {Δ}   (is▶t T iT A) s  =
  (_ , (is▶t (₁ (₁ (Telₛ iT s))) (₂ (₁ (Telₛ iT s))) (A [ ₂ (Telₛ iT s) ]T))) ,
  ((₂ (Telₛ iT s)) ^ A)

{- 

_[_]Te  : {Γ Δ : Con} → ∀ (T : Tel Δ) (s : Sub Γ Δ)  → Tel Γ
T [ s ]Te = ₁ (Telₛ (₂ T) s)

longₛ : {Γ Δ : Con} → ∀ (T : Tel Δ) (s : Sub Γ Δ)  → Sub (Γ ^^ (T [ s ]Te)) (Δ ^^ T)
longₛ T s = ₂ (Telₛ (₂ T) s)

longWk : ∀{Γ}{E : Ty Γ}(Δ : Tel Γ) → Sub ((Γ ▶ E) ^^ (Δ [ wk ]Te)) (Γ ^^ Δ)
longWk {Γ}{E} Δ = longₛ Δ wk


wkC : (Γ : Con)(E : Ty Γ)(Δ : Tel Γ) → Tel (Γ ▶ E)
wkC Γ E Δ = Δ [ wk ]Te

wk∙t : {Γ : Con}{Ex : Ty Γ} → wkC Γ Ex (∙t _) ≡ ∙t _
wk∙t = refl

liftT : (Γ : Con)(Δ : Tel Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ)) → Ty ((Γ ▶ Ex) ^^ wkC Γ Ex Δ)
liftT Γ Δ Ex A = A [ longWk Δ ]T

liftt : (Γ : Con)(Δ : Tel Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ))(t : Tm (Γ ^^ Δ) A) →
  Tm ((Γ ▶ Ex) ^^ wkC Γ Ex Δ) (liftT Γ Δ Ex A)
liftt Γ Δ Ex A t = _[_]t
   -- {Γ = (Γ , Ex) ^^ wkC Γ Ex Δ}
   -- {Δ = Γ ^^ Δ}
   {A = A}
   t
   -- (longWk {Γ = Γ}{E = Ex} Δ)
   (longWk  Δ)


wkT : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ) → Ty (Γ ▶ Ex)
wkT Γ Ex A = liftT Γ (∙t Γ) Ex A

wkt : (Γ : Con)(Ex : Ty Γ)(A : Ty Γ)(t : Tm Γ A) → Tm (Γ ▶ Ex) (wkT Γ Ex A)
wkt Γ Ex A t = liftt Γ (∙t Γ) Ex A t

V0 : (Γ : Con)(A : Ty Γ) → Tm (Γ ▶ A) (wkT Γ A A)
V0 Γ A = vz

subTel : {Γ : Con}(Ex : Ty Γ)(Δ : Tel (Γ ▶ Ex)) (z : Tm Γ Ex) → Tel Γ
subTel {Γ}Ex Δ z = Δ [ <_> {A = Ex} z  ]Te


l-subT : {Γ : Con}(E : Ty Γ)(Δ : Tel (Γ ▶ E)) (z : Tm Γ E)
  (A : Ty ((Γ ▶ E) ^^ Δ)) → Ty (Γ ^^ subTel E Δ z)
l-subT {Γ} E Δ z A = A [ longₛ Δ (<_> {A = E} z) ]T


subT : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → Ty (Γ ▶ Ex) → Ty Γ
subT Γ Ex = l-subT Ex (∙t _)

l-subt : {Γ : Con}(Ex : Ty Γ)(Δ : Tel (Γ ▶ Ex))(t : Tm Γ Ex) →
  (A : Ty ((Γ ▶ Ex) ^^ Δ) ) (u : Tm _ A )→
  Tm (Γ ^^ (subTel Ex Δ t)) (l-subT Ex Δ  t A)
l-subt {Γ} E Δ z A t = _[_]t {A = A} t ( longₛ Δ (<_> {A = E} z) )
 
subt : (Γ : Con)(Ex : Ty Γ)(t : Tm Γ Ex) → (A : Ty (Γ ▶ Ex) ) (u : Tm _ A )→
  Tm (Γ ^^ (∙t Γ)) (l-subT Ex (∙t _)  t A)
subt Γ Ex t A u = l-subt Ex (∙t _) t A u


app' : (Γ : Con)(A : Tm Γ U )(B : Ty (Γ ▶ El A)) (t : Tm Γ (Π A B)) (u : Tm Γ (El A)) →
  Tm Γ (subT Γ (El A) u B)
app' Γ A B t u =
  _[_]t
  {A = B}
  (app {Γ}{A}{B} t)
  ( <_> {A = El A} u  )






-- -}


