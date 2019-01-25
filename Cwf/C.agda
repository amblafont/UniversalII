{-
Paper: section 4

CwF part of the initial algebra construction.
-}

-- C-j pour revenir à la ligne
-- M/C-fb
-- C-o pour faire une commande en mode edit


-- copied from InitialAlg/


open import SyntaxIsModel using (module Syn)
import SyntaxIsModel as SM
open import monlib

module C (funext : ∀ {i}{j} → funext-statment {i}{j})(Ω : Syn.Con) where






private
  module S = Syn

-- infixl 9 ap
open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )
  hiding (_∘_ ; _⁻¹ ; Π ; _$_ ; Lift ; Ω)



import ADS as ADS
-- open import ADS using ( mkCon; mkTy; mkTm; mkSub ; i ; j)
open import ADS using ( i ; j ; ᴬ ; ᴰ ; ˢ)
-- open import ADS using ( i ; j )
-- import StrictLib hiding (id; _∘_)


open import ModelRecord

-- open import StrictLib hiding (id; _∘_)

infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 4 _▶_



record Con : Set i where
  field
    ⁱ : S.Con
    ᴬᴰˢ : ADS.Con
    ᶜ : (e : S.Sub Ω  ⁱ) → ᴬ ᴬᴰˢ 

  -- open ADS.Con ᴬᴰˢ public


mkCon : (ⁱ₁ : SyntaxIsModel.Con) (ᴬ₁ : Set₁) (ᴰ₁ : ᴬ₁ → Set₁)
        (ˢ₁ : (γ : ᴬ₁) → ᴰ₁ γ → Set) (ᶜ₁ : Syn.Sub Ω ⁱ₁ → ᴬ₁) →
    Con
mkCon = λ ⁱ₁ ᴬ₁ ᴰ₁ ˢ₁ ᶜ₁ → record { ᴬᴰˢ = ADS.mkCon ᴬ₁ ᴰ₁ ˢ₁ ; ⁱ = ⁱ₁ ; ᶜ = ᶜ₁ }

open Con public hiding (ᴬᴰˢ)
    
record Ty (Γ : Con) : Set i where
  constructor mkTy
  field
    ⁱ : SM.Ty ((ⁱ Γ))
    ᴬᴰˢ : ADS.Ty (Con.ᴬᴰˢ Γ)
    -- need funext!
    ᶜ : ∀ (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → (t : S.Tm Ω (ⁱ S.[ v ]T)) →  ᴬ ᴬᴰˢ (ᶜ Γ v)
  open ADS.Ty ᴬᴰˢ public
open Ty public hiding (ᴬᴰˢ)

Ty= : ∀ {Γ : Con}{A B : Ty Γ}(e : ⁱ A ≡ ⁱ B)(e2 : Ty.ᴬᴰˢ A ≡ Ty.ᴬᴰˢ B )
   (e3 : ᶜ A == ᶜ B
   [ (λ x → ∀ (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → (t : S.Tm Ω ((₁ x) S.[ v ]T)) →  ᴬ (₂ x) (ᶜ Γ v))
     ↓ pair×= e e2 ]) → A ≡ B

-- Ty= {Γ}{A}{B}e e2 e3 = {!!}
Ty= {Γ}   refl refl e3 = 
  ap (mkTy _ _) e3

{- 
Ty=' : ∀ {Γ : Con}{Aⁱ Bⁱ : S.Ty (ⁱ Γ)}(e : Aⁱ ≡  Bⁱ)
   {ABᴬᴰˢ : ADS.Ty (Con.ᴬᴰˢ Γ)}
   {Aᶜ Bᶜ}
   (e3 : Aᶜ  ==  Bᶜ  
    [ (λ x → ∀ (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → (t : S.Tm Ω ( x S.[ v ]T)) →  ᴬ ABᴬᴰˢ (ᶜ Γ v))
      ↓ e  ]) 
      →
     mkTy Aⁱ ABᴬᴰˢ Aᶜ ≡  mkTy Bⁱ ABᴬᴰˢ Bᶜ 

Ty=' {Γ}{Aⁱ}{Bⁱ} refl {ABᴬᴰˢ} e3 = ap (mkTy Aⁱ ABᴬᴰˢ) e3
-}

{-
Ty=-funext' : ∀ {Γ : Con}{Aⁱ Bⁱ : S.Ty (ⁱ Γ)}(e : Aⁱ ≡  Bⁱ)
   {ABᴬᴰˢ : ADS.Ty (Con.ᴬᴰˢ Γ)}
   {Aᶜ Bᶜ}
   (e3 : (v : _) → Aᶜ v  ==  Bᶜ v 
    [ (λ x → (t : S.Tm Ω (x S.[ v ]T)) →  ᴬ ABᴬᴰˢ (ᶜ Γ v))
      ↓ e  ]) 
        
        →
     mkTy Aⁱ ABᴬᴰˢ Aᶜ ≡  mkTy Bⁱ ABᴬᴰˢ Bᶜ 

Ty=-funext' {Γ}{Aⁱ}{Bⁱ} refl {ABᴬᴰˢ} e3 = {!!}
-}

Ty=-funext₁ : ∀ {Γ : Con}{A B : Ty Γ}(e : ⁱ A ≡ ⁱ B)(e2 : Ty.ᴬᴰˢ A ≡ Ty.ᴬᴰˢ B )
   (e3 : (v : _) → ᶜ A v  == ᶜ B v 
   [ (λ x →  (t : S.Tm Ω ((₁ x) S.[ v ]T)) →  ᴬ (₂ x) (ᶜ Γ v))
     ↓ pair×= e e2 ]) → A ≡ B

Ty=-funext₁ {Γ} refl refl e3 = ap (mkTy _ _) (funext e3)

-- {mkTy _ _ A}{mkTy _ _ B }refl refl e3 =
--   ap (mkTy _ _) (funext e3)

{-
Ty=-funext : ∀ {Γ : Con}{A B : Ty Γ}(e : ⁱ A ≡ ⁱ B)(e2 : Ty.ᴬᴰˢ A ≡ Ty.ᴬᴰˢ B )
   (e3 : (v : _) (t : S.Tm Ω (_ S.[ v ]T)) → ᶜ A v t == ᶜ B v (tr (λ x → S.Tm Ω (x S.[ v ]T)) e t)
      [ (λ x →  ᴬ x (ᶜ Γ v)) ↓ e2 ]) →
      A ≡ B

Ty=-funext {Γ}{mkTy _ _ A}{mkTy _ _ B }refl refl e3 =
  ap (mkTy _ _) (funext (λ v → funext (e3 v)))
  -}


record Tm (Γ : Con)(A : Ty Γ) : Set j where
  constructor mkTm
  field
    ⁱ : SM.Tm ( (ⁱ Γ)) ( (ⁱ A))
    ᴬᴰˢ : ADS.Tm (Con.ᴬᴰˢ Γ) (Ty.ᴬᴰˢ A)
    ᶜ : (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → Ty.ᶜ A v (ⁱ S.[ v ]t) ≡  ᴬ ᴬᴰˢ ( Con.ᶜ Γ v)
  open ADS.Tm ᴬᴰˢ public

open Tm public hiding ( ᴬᴰˢ)

Tm=-funext : ∀ {Γ : Con}{A : Ty Γ}{t u : Tm Γ A}(e : ⁱ t ≡ ⁱ u)(e2 : Tm.ᴬᴰˢ t ≡ Tm.ᴬᴰˢ u )
      → t ≡ u

Tm=-funext refl refl = ap (mkTm _ _) (funext (λ a → uip _ _))

Tm=[]-funext : ∀ {Γ : Con}{A B : Ty Γ}(e : ⁱ A ≡ ⁱ B)(e2 : Ty.ᴬᴰˢ A ≡ Ty.ᴬᴰˢ B )
   (e3 : ᶜ A  == ᶜ B [ (λ x →  (v : _) →(t : S.Tm Ω ((₁ x) S.[ v ]T)) →  ᴬ (₂ x) (ᶜ Γ v))
          ↓ pair×= e e2 ] ) 
   {t : Tm Γ A}{u : Tm Γ B}
   (e' : ⁱ t == ⁱ u [ S.Tm _ ↓ e ])
   (e2' : (Tm.ᴬᴰˢ t) == Tm.ᴬᴰˢ u [ ADS.Tm _ ↓ e2 ] )
    →
     t == u [ Tm Γ ↓ Ty= e e2 e3 ]

Tm=[]-funext refl refl refl {t}{u} = Tm=-funext

-- this uses uip
Tm=[]-funext' : ∀ {Γ : Con}{A B : Ty Γ}{e : ⁱ A ≡ ⁱ B}(e2 : Ty.ᴬᴰˢ A ≡ Ty.ᴬᴰˢ B )
   {e3 : A ≡ B} 
   {t : Tm Γ A}{u : Tm Γ B}
   (e' : ⁱ t == ⁱ u [ S.Tm _ ↓ e ])
   (e2' : (Tm.ᴬᴰˢ t) == Tm.ᴬᴰˢ u [ ADS.Tm _ ↓ e2 ] )
    →
     t == u [ Tm Γ ↓ e3 ]

Tm=[]-funext' {e = refl} refl {refl} {t}{u} = Tm=-funext

record Sub (Γ Δ : Con) : Set j where
  constructor mkSub
  field
    ⁱ : SM.Sub ( (ⁱ Γ)) ( (ⁱ Δ))
    ᴬᴰˢ : ADS.Sub (Con.ᴬᴰˢ Γ) (Con.ᴬᴰˢ Δ)
    ᶜ : (v : S.Sub ( Ω) ( (Con.ⁱ Γ))) → Con.ᶜ Δ (ⁱ S.∘ v) ≡ ᴬ ᴬᴰˢ (ᶜ Γ v)
  open ADS.Sub ᴬᴰˢ public



open Sub public

Sub=-funext : ∀ {Γ : Con}{Δ : Con}{σ δ : Sub Γ Δ}(e : ⁱ σ ≡ ⁱ δ)(e2 : Sub.ᴬᴰˢ σ ≡ Sub.ᴬᴰˢ δ )
      → σ ≡ δ

Sub=-funext refl refl = ap (mkSub _ _) (funext (λ a → uip _ _))

open Con public
open Ty public
open Tm public

∙ : Con
∙ = record { ⁱ = S.∙ ; ᴬᴰˢ = ADS.∙ ; ᶜ = λ e → lift tt }

_▶_ : (Γ : Con) → Ty Γ → Con
Γ ▶ A = record { ⁱ = ⁱ Γ S.▶ ⁱ A ; ᴬᴰˢ = ᴬᴰˢ Γ ADS.▶ ᴬᴰˢ A ;
  ᶜ = λ v  → (ᶜ Γ (S.π₁ v)) , ᶜ A (S.π₁ v) (S.π₂ v) }

[]Tᶜ : ∀ {Γ}{Δ}(A : Ty Δ)(σ : Sub Γ Δ) → (v : S.Sub Ω (ⁱ Γ)) →
      S.Tm Ω (ⁱ A S.[ ⁱ σ ]T S.[ v ]T) → ᴬ A (ᴬ σ (ᶜ Γ v))

[]Tᶜ {Γ}{Δ}A σ v t =
    tr (ᴬ A) (ᶜ σ v) (ᶜ A (ⁱ σ S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) t))

_[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {Γ} {Δ} A σ = record { ⁱ = ⁱ A S.[ ⁱ σ ]T ; ᴬᴰˢ = ᴬᴰˢ A ADS.[ ᴬᴰˢ σ ]T ;
  ᶜ = []Tᶜ A σ }

id : ∀{Γ} → Sub Γ Γ
id {Γ} = record { ⁱ = S.id ; ᴬᴰˢ = ADS.id ; ᶜ = λ v → ap (ᶜ Γ) S.idl }

π₁ : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (Δ ▶ A) → Sub Γ Δ
π₁ {Δ = Δ}σ = record { ⁱ = S.π₁ (ⁱ σ) ; ᴬᴰˢ = ADS.π₁ (ᴬᴰˢ σ) ;
  ᶜ = λ v →  ap (ᶜ Δ) ( ! (S.π₁∘ {σ = ⁱ σ}{δ = v}  )   ) ◾ fst=  (ᶜ σ v) }

_[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_]t {A = A}t σ = record { ⁱ = ⁱ t S.[ ⁱ σ ]t ; ᴬᴰˢ = ᴬᴰˢ t ADS.[ ᴬᴰˢ σ ]t ;
  ᶜ = λ v →
        ap (λ x → tr (ᴬ A) (ᶜ σ v) (ᶜ A (S._∘_ (ⁱ σ) v) x)) (to-transp (S.[][]t {t = ⁱ t}{σ = v}{δ = ⁱ σ} )) 
     ◾ ap (tr _ (ᶜ σ v))(ᶜ t (ⁱ σ S.∘ v))
     ◾ to-transp (apd (ᴬ t) (ᶜ σ v) ) }

π₂ : {Γ Δ : Con}
     {A : Ty Δ}
     (σ : Sub Γ (Δ ▶ A)) → Tm Γ (_[_]T {Γ} {Δ} A (π₁ {Γ} {Δ} {A} σ))
π₂ {Γ}{Δ}{A}σ = record { ⁱ = S.π₂ (ⁱ σ) ; ᴬᴰˢ = ADS.π₂ (ᴬᴰˢ σ) ;
  ᶜ = helper }
  -- {! helper !} }
  
-- comment because it is too slow
  
   where
      π₁σ = (π₁ {Γ = Γ}{Δ = Δ}{A = A} σ)
      xx : ∀ v → S.Tm Ω (ⁱ A S.[ S.π₁ ((ⁱ σ) S.∘ v) ]T)
      xx v = transport! (S.Tm Ω) (ap (λ s → S._[_]T (ⁱ A) s)
         (S.π₁∘ {A = ⁱ A}{σ = (ⁱ σ)}) ◾ ! (S.[][]T {A = ⁱ A})) (S.π₂ (ⁱ σ) S.[ v ]t) 

      helper : ∀ v →
        -- []Tᶜ A π₁σ v (S.π₂ (ⁱ σ) S.[ v ]t)
        -- tr (ᴬ A) (ᶜ π₁σ v) (ᶜ A (S.π₁ (ⁱ σ)  S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ (ⁱ σ) S.[ v ]t)))
        tr (ᴬ A) (ap (ᶜ Δ) ( ! (S.π₁∘ {σ = (ⁱ σ)}{δ = v}  )   ) ◾ fst=  ((ᶜ σ) v))
          (ᶜ A (S.π₁ (ⁱ σ)  S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ (ⁱ σ) S.[ v ]t)))

        -- ᶜ (A [ π₁ {A = A}(mkSub (ⁱ σ) (ᴬ σ) (ᴰ σ) (ˢ σ) (ᶜ σ)) ]T) v (S.π₂ (ⁱ σ) S.[ v ]t)
        ≡
            ₂ ((ᴬ σ) (ᶜ Γ v))
            -- ₂ ((ᴬ σ) (ᶜ Γ v))
      helper v =
       to-transp {B = ᴬ A}
         {p = ap (ᶜ Δ) (! (S.π₁∘ {σ = (ⁱ σ)} {δ = v})) ◾ fst= ((ᶜ σ) v)}
         -- uip for simplicty
          (≅↓
            (
            (ᶜ A (S.π₁ (ⁱ σ)  S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ (ⁱ σ) S.[ v ]t)))

              ≅⟨ ↓≅ (apd {A = ∃ (λ (v₁ : S.Sub Ω (ⁱ Δ)) → S.Tm Ω (ⁱ A S.[ v₁ ]T))}
                    (λ x → ᶜ A (₁ x)(₂ x))
                    {x = (S.π₁ (ⁱ σ)  S.∘ v) , tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (S.π₂ (ⁱ σ) S.[ v ]t)}
                    {y = (S.π₁ ((ⁱ σ) S.∘ v)) , xx v}
                    (pair= (! S.π₁∘)
                      (≅↓ (↓≅ ( (from-transp  (S.Tm Ω) (S.[][]T {A = ⁱ A}) refl) ) !≅
                       ∘≅ (↓≅ (from-transp! (S.Tm Ω) (ap (λ s → S._[_]T (ⁱ A) s) (S.π₁∘ {A = ⁱ A}{σ = (ⁱ σ)})
                                  ◾ ! (S.[][]T {A = ⁱ A})) refl) !≅)))
                      ))
                ⟩
              -- ≅⟨ {!ᶜ Aap {A = Σ _ _}(λ x → ᶜ A (₁ x)(₂ x))!} ⟩
            ᶜ A (S.π₁ ((ⁱ σ) S.∘ v)) (xx v)
            -- ᶜ A (S.π₁ ((ⁱ σ) S.∘ v)) (tr (S.Tm Ω) {!ap (λ s → _ S.[ s ]T) S.π₁∘ ◾ ! S.[][]T!} (S.π₂ (ⁱ σ) S.[ v ]t))

              ≅⟨ =≅ ( ap (ᶜ A (S.π₁ ((ⁱ σ) S.∘ v))) ( ! (to-transp! ( (S.π₂∘ {σ = (ⁱ σ)}{δ = v})))) ) ⟩
            ᶜ A (S.π₁ ((ⁱ σ) S.∘ v)) (S.π₂ ((ⁱ σ) S.∘ v))

              ≅⟨ ↓≅ (apd ₂ ((ᶜ σ) v)) ⟩
            ₂ ((ᴬ σ) (ᶜ Γ v))
            ≅∎
            )
            )

[id]T : ∀{Γ}{A : Ty Γ} → A [ id ]T ≡ A
-- need funext !
[id]T {Γ}{A} =
  Ty=-funext₁ S.[id]T refl
   (λ v →
     ≅↓
      (helper' v
      (S.[][]T {A = ⁱ A}{σ = v}{δ = ⁱ (id {Γ})})
      (ᶜ (id {Γ}) v))
      )
  where
    helper' : ∀ v e p →
           (λ (t : _) →  (tr (ᴬ A) p (ᶜ A (ⁱ (id {Γ}) S.∘ v) (tr (S.Tm Ω) e t))) )
       ≅ (ᶜ A v)
        -- [ (λ x → (t : S.Tm Ω (₁ x S.[ v ]T)) → ᴬ (₂ x) (ᶜ Γ v)) ↓ (pair×= S.[id]T refl) ]
    
    helper' v e p = 
    -- comment because it is too slow
      J' 
          (λ T z →
            (λ t →
                tr (ᴬ A) p (ᶜ A (S._∘_ (ⁱ (id {Γ})) v) (tr (S.Tm Ω) z t)))
              ≅ ᶜ A v)
          (J' (λ T z → ∀ (q : ᶜ Γ T == ᶜ Γ v) → (λ t → tr (ᴬ (ᴬᴰˢ A)) q (ᶜ A T t)) ≅ ᶜ A v)
            (λ q →
              J (λ T z → (λ t → tr (ᴬ (ᴬᴰˢ A)) z (ᶜ A v t)) ≅ ᶜ A v) refl≅ q
              )
            (S.idl {σ = v})
             p)
        e

∘ᶜ : ∀{Γ Δ Y} → (σ : Sub Δ Y) → (δ : Sub Γ Δ) → (v : S.Sub Ω (ⁱ Γ)) →
      ᶜ Y ((ⁱ σ S.∘ ⁱ δ) S.∘ v) ≡ ᴬ (ᴬᴰˢ σ ADS.∘ ᴬᴰˢ δ) (ᶜ Γ v)
∘ᶜ {Γ}{Δ}{Y} σ δ v =
  ap (ᶜ Y) (S.ass {σ = ⁱ σ}{δ = ⁱ δ}) ◾ ᶜ σ (ⁱ δ S.∘  v) ◾ ap (ᴬ (ᴬᴰˢ σ)) (ᶜ δ v) 

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
_∘_ {Γ}{Δ}{Y} σ δ = record { ⁱ = ⁱ σ S.∘ ⁱ δ ; ᴬᴰˢ = ᴬᴰˢ σ ADS.∘ ᴬᴰˢ δ ; ᶜ =
  ∘ᶜ σ δ }

ε : ∀{Γ} → Sub Γ ∙
ε {Γ} = record { ⁱ = S.ε ; ᴬᴰˢ = ADS.ε ; ᶜ = λ v → refl }

_,s_ : ∀{Γ Δ}(σ : Sub Γ Δ){A : Ty Δ} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)

,sᶜ : ∀{Γ Δ}(σ : Sub Γ Δ){A : Ty Δ} → (t : Tm Γ (A [ σ ]T)) 
     (v : S.Sub Ω (ⁱ Γ)) →
     let ΔA : ∃ (ᴬ (ᴬᴰˢ A) )
         ΔA = ᶜ Δ (S.π₁ ((ⁱ σ S.,s ⁱ t) S.∘ v)) ,
          ᶜ A (S.π₁ ((ⁱ σ S.,s ⁱ t) S.∘ v)) (S.π₂ ((ⁱ σ S.,s ⁱ t) S.∘ v))
     in
     let ΔA' : ∃ (ᴬ (ᴬᴰˢ A) )
         ΔA' = ᴬ (ADS._,s_ (ᴬᴰˢ σ) {A = ᴬᴰˢ A } (ᴬᴰˢ t)) (ᶜ Γ v)
     in
     ΔA ≡ ΔA'

,sᶜ {Γ}{Δ} σ {A} t v =
   pair= (ᶜ σ v) ( _▹_ {p' = refl} (_◃_ {p = refl} helper (from-transp _ _ refl))  (ᶜ t v) )
 -- (from-transp _ _ ({!refl!} ◾ ᶜ t v))
  where
    helper :
        ᶜ A (ⁱ σ S.∘ v)
              (S.π₂ ((ⁱ σ S.,s ⁱ t) S.∘ v))
              ≡ ᶜ A (ⁱ σ S.∘ v) (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (ⁱ t S.[ v ]t))
    helper =
       ap (ᶜ A (S._∘_ (ⁱ σ) v)) (! (to-transp {B = S.Tm Ω}{p = S.[][]T {A = ⁱ A}}
         ( !ᵈ' (S.π₂,∘ {Γ = ⁱ Γ}{Δ = ⁱ Δ}{t = ⁱ t }))))

_,s_ {Γ}{Δ} σ {A} t = record { ⁱ = ⁱ σ S.,s ⁱ t  ; ᴬᴰˢ = ᴬᴰˢ σ ADS.,s ᴬᴰˢ t ; ᶜ = ,sᶜ σ {A = A}t  }

[][]T : {Γ Δ : Con} {Σ : Con} {A : Ty Σ} {σ : Sub Γ Δ}
    {δ : Sub Δ Σ} →
    _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (_[_]T {Δ} {Σ} A δ) σ)
    (_[_]T {Γ} {Σ} A (_∘_ {Γ} {Δ} {Σ} δ σ))
[][]T {Γ}{Δ}{Y}{A}{σ}{δ} =
   Ty=-funext₁ (S.[][]T {A = ⁱ A}) refl λ v → ≅↓ (helper v)
   where
     lhs-f = λ v t → tr (λ γ → ᴬ A (ᴬ δ γ)) (ᶜ σ v) (tr (ᴬ A) (ᶜ δ (ⁱ σ S.∘ v)) (ᶜ A (ⁱ δ S.∘ (ⁱ σ S.∘ v)) t))
     rhs-f = λ v t → tr (ᴬ A) (∘ᶜ δ σ v) (ᶜ A ((ⁱ δ S.∘ ⁱ σ) S.∘ v) t) 
     -- rhs = λ v t → rhs-f v (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) t)

     lrhs-f= : ∀ v → ((lhs-f v) ≅ (rhs-f v))

     lrhs-f= v =
       J (λ s e → lhs-f v ≅ (λ t → tr (ᴬ A) e (ᶜ A ((ⁱ δ S.∘ ⁱ σ) S.∘ v) t)))
       (J (λ s e → lhs-f v ≅ (λ t → ᶜ A s t))
       (J
          (λ s e →
             (λ t →
                tr (λ γ → ᴬ A (ᴬ δ γ)) e
                (tr (ᴬ A) (ᶜ δ (S._∘_ (ⁱ σ) v))
                 (ᶜ A (S._∘_ (ⁱ δ) (S._∘_ (ⁱ σ) v)) t)))
             ≅ ᶜ A (S._∘_ (ⁱ δ) (S._∘_ (ⁱ σ) v)))
          (J
             (λ s e →
                (λ t → tr (ᴬ A) e (ᶜ A (S._∘_ (ⁱ δ) (S._∘_ (ⁱ σ) v)) t)) ≅
                ᶜ A (S._∘_ (ⁱ δ) (S._∘_ (ⁱ σ) v)))
             refl≅
             (ᶜ δ (ⁱ σ S.∘ v)))
          (ᶜ σ v))
       (! (S.ass {σ = ⁱ δ}{δ = ⁱ σ}{ν = v})))
       -- (S.ass {σ = ⁱ δ}{δ = ⁱ σ}{ν = v})
       (∘ᶜ δ σ v)
      

     helper :  ∀ v
        --  (lhs :  (t : SyntaxIsModel.Tm Ω (ⁱ A S.[ ⁱ δ S.∘ (ⁱ σ S.∘ v) ]T)) →
        --     ᴬ (ᴬᴰˢ A) (ᴬ (ᴬᴰˢ δ) (ᴬ (ᴬᴰˢ σ) (ᶜ Γ v))))
        -- (rhs : (t : SyntaxIsModel.Tm Ω (ⁱ A S.[ (ⁱ δ S.∘ ⁱ σ) S.∘ v ]T)) →
        --     ᴬ (ᴬᴰˢ A) (ᴬ (ᴬᴰˢ δ ADS.∘ ᴬᴰˢ σ) (ᶜ Γ v)))
        -- (rhs= : rhs ≅ lhs )
        →
      -- ([]Tᶜ (A [ δ ]T) σ) ==
      -- ([]Tᶜ A (δ ∘ σ))
      (λ t →
              -- lhs-f v
              lhs-f v (tr (S.Tm Ω) (S.[][]T {A = ⁱ A})
                (tr (S.Tm Ω) (S.[][]T {A = ⁱ A S.[ ⁱ δ ]T}{σ = v}) t))
              
        )
        ≅
        (λ t → rhs-f v (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}{σ = v}) t))
     helper v =
       J'
         (λ T e →
            (λ t → lhs-f v (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) (tr (S.Tm Ω) e t))) ≅
            (λ t → rhs-f v (tr (S.Tm Ω) (S.[][]T {A = ⁱ A} {σ = v}) t)))
         (J'
            (λ T e →
               (λ t → lhs-f v (tr (S.Tm Ω) e t)) ≅
               (λ t → rhs-f v (tr (S.Tm Ω) (S.[][]T {A = ⁱ A} {σ = v}) t)))
            (J' (λ T e → (λ t → lhs-f v t) ≅ (λ t → rhs-f v (tr (S.Tm Ω) e t)))
            (lrhs-f= v)
            ((S.[][]T {A = ⁱ A} {σ = v})))
            (S.[][]T {A = ⁱ A}))
         (S.[][]T {A = ⁱ A S.[ ⁱ δ ]T}{σ = v})
       
     
idl   : {Γ Δ : Con} {σ : Sub Γ Δ} →  (id ∘ σ) ≡ σ
idl {Γ}{Δ}{σ} = Sub=-funext S.idl refl

idr   : {Γ Δ : Con} {σ : Sub Γ Δ} →  (σ ∘ id) ≡ σ
idr {Γ}{Δ}{σ} = Sub=-funext S.idr refl

ass   : {Γ Δ : Con} {Σ : Con} {Ω : Con} {σ : Sub Σ Ω} {δ : Sub Δ Σ}
    {ν : Sub Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass {σ = σ}{δ}{ν}= Sub=-funext (S.ass {σ = ⁱ σ}{δ = ⁱ δ}) refl

π₁,∘ : {Γ Δ : Con} {Σ₁ : Con} {δ : Sub Γ Δ} {σ : Sub Σ₁ Γ}
      {A : Ty Δ} {t : Tm Γ (A [ δ ]T)} →
      π₁ {A = A} ((_,s_  δ {A = A} t) ∘ σ) ≡ δ ∘ σ

π₁,∘ = Sub=-funext refl refl


π₂,∘ :  {Γ Δ : Con} {Σ₁ : Con} {δ : Sub Γ Δ} {σ : Sub Σ₁ Γ}
 {A : Ty Δ} {t : Tm Γ (A [ δ ]T)} →
      (π₂ {Γ = Σ₁}{Δ}{A = A}((_,s_ δ {A} t) ∘ σ)) ==
      (_[_]t {A = A [ δ ]T} t σ)
      [ (Tm Σ₁) ↓ (ap (_[_]T A) (π₁,∘ {δ = δ} {σ}{A = A}{t}) ◾ ! ([][]T {A = A}{σ}{δ}) ) ]
π₂,∘ {Γ}{Δ}{Y}{δ}{σ}{A}{t} =
  Tm=[]-funext' refl (S.π₂,∘ {δ = ⁱ δ} {ⁱ σ}{A = ⁱ A}{ⁱ t}) refl
  --   (Tm=-funext ( to-transp! (S.π₂,∘ {δ = ⁱ δ}{ⁱ σ}{ⁱ A}{ⁱ t}) ) refl
  --  ◾ {!!} 
  --   )

  -- tr (PathOver _ _ _) {!!} {!!}

π₁β : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ]T)} →
      π₁ {A = A}(_,s_  σ {A = A} t) ≡ σ
π₁β {Γ}{Δ}{A}{σ}{t} = Sub=-funext refl refl 

π₂β :  {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ]T)} →
         (π₂ {A = A}(_,s_  σ {A = A} t)) == t
        [ (λ σ₁ → Tm Γ (A [ σ₁ ]T)) ↓ π₁β {Γ}{Δ}{A}{σ}{t}  ]
π₂β {Γ}{Δ}{A}{σ}{t} =
   ≅↓ (↓≅ (Tm=[]-funext' refl {e3 = ap (λ s → (A [ s ]T)) (π₁β {Γ}{Δ}{A}{σ}{t}  )}
   refl  refl))  

cCwF : CwF
cCwF = record {
  basecwf = record { Con = Con ; Ty = Ty ; Tm = Tm ; Sub = Sub } ;
  nextcwf = record
              { ∙ = ∙ 
              ; _▶_ = _▶_
              ; _[_]T = _[_]T
              ; id = id
              ; _∘_ = _∘_
              ; ε = ε
              ; _,s_ = _,s_
              ; π₁ = λ {Γ}{A}{Δ} → π₁ {Γ}{A}{Δ}
              ; _[_]t = _[_]t
              ; π₂ = λ {Γ}{A}{Δ} → π₂ {Γ}{A}{Δ}
              ; [id]T = [id]T
              ; [][]T = λ {Γ}{Δ}{Y}{A}{σ}{δ} → [][]T {Γ}{Δ}{Y}{A}{σ}{δ}
              ; idl = idl
              ; idr = idr
              ; ass = λ {Γ}{Δ}{Y}{C}{σ }{δ}{v} → ass{σ = σ}{δ}{v}
              ; π₁,∘ = λ {Γ}{Δ}{Y}{δ}{σ}{A}{t} → π₁,∘  {δ = δ}{σ}{A = A}{t = t}
              -- Sub=-funext refl refl
              ; π₂,∘ = λ {Γ}{Δ}{Y}{δ}{σ}{A}{t} → π₂,∘{δ = δ}{σ}{A = A}{t = t}
              ; π₁β = λ {Γ}{Δ}{A}{σ}{t} → π₁β {Γ}{Δ}{A}{σ}{t}
              ; πη = Sub=-funext S.πη refl
              ; εη = Sub=-funext S.εη refl
              ; π₂β =  λ {Γ}{Δ}{A}{σ}{t} → π₂β {Γ}{Δ}{A}{σ}{t}
              } }

U : {Γ : Con} → Ty Γ
U {Γ} = mkTy S.U ADS.U (λ v a → S.Tm Ω (S.El a))

U[] :  {Γ Δ : Con } {σ : Sub Γ Δ} → (U [ σ ]T)  ≡ U
U[] {Γ}{Δ}{σ} = ap (mkTy _ _) (funext helper)
  where
    helper : ∀ v → 
    -- []Tᶜ U σ == 
      -- (λ v a → tr (ᴬ (U {Γ = Δ})) (ᶜ σ v)
      -- (tr (S.Tm Ω) (S.[][]T {A = ⁱ A}) t)
      (λ  a → tr (λ _ → Set) (ᶜ σ v)
        (
         S.Tm Ω (S.El (tr (S.Tm Ω) (S.[][]T {Γ = Ω}{ⁱ Γ}{ⁱ Δ}{A = ⁱ (U {Γ = Δ})}{v}{ⁱ σ}) a))
      ))
      ≡ (λ a → S.Tm Ω (S.El a))
  -- use uip
    helper v
       =
       ap2 (λ p q →
         (λ  a → coe p 
        (S.Tm Ω (S.El (tr (S.Tm Ω) q a))
        ))
      )
      {y = refl}
      {z = refl}
      (ap-cst Set (ᶜ σ v))
      (uip _ _)

Tm-tr= : ∀ {Γ : Con}{Aⁱ : S.Ty (ⁱ Γ)}{Aᴬᴰˢ : ADS.Ty (ᴬᴰˢ Γ)}
   {Aᶜ A'ᶜ } (e : Aᶜ ≡ A'ᶜ)(t : Tm Γ (mkTy Aⁱ Aᴬᴰˢ Aᶜ)) →
    tr (Tm Γ) (ap (mkTy Aⁱ Aᴬᴰˢ) e) t ≡ mkTm (ⁱ t) (ᴬᴰˢ t)
      (tr
         (λ X →
            (v : S.Sub Ω (ⁱ Γ)) → X v (S._[_]t (ⁱ t) v) ≡ ᴬ (ᴬᴰˢ t) (ᶜ Γ v))
         e (ᶜ t))
Tm-tr= {Γ} {Aⁱ} {Aᴬᴰˢ} {Aᶜ} {.Aᶜ} refl t = refl
    
El : {Γ : Con} → (a : Tm Γ U) → Ty Γ
El {Γ} a = mkTy (S.El (ⁱ a)) (ADS.El (ᴬᴰˢ a))
  (λ v t → lift (coe (ᶜ a v) t))

El[] : {Γ Δ : Con} {σ : Sub  Γ Δ}
      {a : Tm  Δ U} →
      ( (El  a) [ σ ]T)  ≡
      El (coe (ap (Tm  Γ) (U[] {σ = σ})) ((a [ σ ]t) ))



El[]{Γ}{Δ}{σ}{a} =
  
      ((El  a) [ σ ]T)
        =⟨ ap (mkTy _ _) {!!} ⟩
      El (mkTm (ⁱ a S.[ ⁱ σ ]t)(ᴬᴰˢ a ADS.[ ᴬᴰˢ σ ]t ) _
         -- (tr
         -- (λ X →
         --    (v : S.Sub Ω (ⁱ Γ)) → X v (S._[_]t (ⁱ a S.[ ⁱ σ ]t) v) ≡ ᴬ (ᴬᴰˢ a ADS.[ ᴬᴰˢ σ ]t ) (ᶜ Γ v))
         -- {!!} (ᶜ (a [ σ ]t )))
         )
        =⟨ ap El (! (Tm-tr= (funext _) (a [ σ ]t))) ⟩
      El (coe (ap (Tm  Γ) (U[] {σ = σ})) ((a [ σ ]t) ))
      =∎
  
Π : {Γ : Con} (a : Tm Γ U) →
      Ty ( Γ ▶ (El a)) → Ty Γ

Π {Γ}a B = mkTy (S.Π (ⁱ a) (ⁱ B)) (ADS.Π (ᴬᴰˢ a) (ᴬᴰˢ B))
             (λ v t α → 
               tr (ᴬ B) {!!}
               (ᶜ B (v S.,s coe {!!} α)(coe {!!} (t S.$ coe {!!} α))))

  -- rewrite Tm-tr= (funext _)(a [ σ ]t)  = {!!}

cUnivΠ : UnivΠ cCwF
cUnivΠ = record
           { U = U
           ; U[] = λ {Γ}{Δ}{σ} → U[]{Γ}{Δ}{σ}
           ; El = El
           ; El[] = λ {Γ}{Δ}{σ}{a} → El[]{Γ}{Δ}{σ}{a}
           ; Π = {!!}
           ; Π[] = {!!}
           ; _$_ = {!!}
           ; $[] = {!!}
           }
