{-# OPTIONS  --rewriting  #-}
{- 
TODO: réfélchir à de meilleures preuves

This file postulates a model which enjoys some rewrite rule for some equalities, in order
to simplify the construction of the recursor from the syntax.

Note that agda does not allow (yet?) to define a record with rewrite rules. That's why we postulate it.

The postulated rewrite rules are actually satisfied for the syntax seen as a model.

It would be nice if we later only use the recursor for models which actually satisifies
these equations definitionally.

At the end, I define telescopes as it seems I need them to take into account the weakening
whose definition precedes the one of full substitutions in the syntax (becaseu of the Π A B case:
indeed B is in an extended context)


-}



open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr)
  hiding (_∘_ ; _⁻¹ ; Π ; _$_)

-- open import HoTT using (ap)

open import monlib hiding (tr2)
-- open import Lib2 hiding (id; _∘_ )



module ModelCwf   where


infixl 7 _[_]T
infixl 5 _,s_
infix  6 _∘_
infixl 8 _[_]t
infixl 4 _▶_

postulate
  i : Level
  j : Level

  Con : Set i
  Ty  : Con → Set i
  Tm  : ∀ Γ → Ty Γ → Set j
  Sub : Con → Con → Set j

  ∙     : Con
  _▶_   : (Γ : Con) → Ty Γ → Con

  _[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ

  id    : ∀{Γ} → Sub Γ Γ
  _∘_   : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
  ε     : ∀{Γ} → Sub Γ ∙
  _,s_  : ∀{Γ Δ}(σ : Sub Γ Δ){A : Ty Δ} → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
  π₁    : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (Δ ▶ A) → Sub Γ Δ

  _[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  π₂    : {Γ Δ : Con} {A : Ty Δ} (σ : Sub Γ (Δ ▶ A)) → Tm Γ (_[_]T {Γ} {Δ} A (π₁ {Γ} {Δ} {A} σ))

  [id]T : ∀{Γ}{A : Ty Γ} → (A [ id ]T) ≡ A

  [][]T : {Γ Δ : Con} {Σ : Con} {A : Ty Σ} {σ : Sub Γ Δ}
      {δ : Sub Δ Σ} →
      _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (_[_]T {Δ} {Σ} A δ) σ)
      (_[_]T {Γ} {Σ} A (_∘_ {Γ} {Δ} {Σ} δ σ))

  idl   : {Γ Δ : Con} {σ : Sub Γ Δ} → _≡_ {j} {Sub Γ Δ} (_∘_ {Γ} {Δ} {Δ} (id {Δ}) σ) σ
  idr   : {Γ Δ : Con} {σ : Sub Γ Δ} → _≡_ {j} {Sub Γ Δ} (_∘_ {Γ} {Γ} {Δ} σ (id {Γ})) σ

  ass   : {Γ Δ : Con} {Σ : Con} {Ω : Con} {σ : Sub Σ Ω} {δ : Sub Δ Σ}
    {ν : Sub Γ Δ} →
    _≡_ {_} {Sub Γ Ω} (_∘_ {Γ} {Δ} {Ω} (_∘_ {Δ} {Σ} {Ω} σ δ) ν)
    (_∘_ {Γ} {Σ} {Ω} σ (_∘_ {Γ} {Δ} {Σ} δ ν))

{- 
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
      -}
  ,∘    :
      {Γ Δ : Con} {Σ : Con} {δ : Sub Γ Δ} {σ : Sub Σ Γ} {A : Ty Δ}
      {t : Tm Γ (_[_]T {Γ} {Δ} A δ)}
      {ts : Tm Σ (A [ δ ∘ σ ]T)}
      (et : (t [ σ ]t) == ts [ Tm Σ ↓  [][]T ])
      →
      ((δ ,s t) ∘ σ)
      ≡ δ ∘ σ ,s ts

  π₁β   : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ}
     {t : Tm Γ (_[_]T {Γ} {Δ} A σ)} →
     _≡_ {_} {Sub Γ Δ} (π₁ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)) σ

  πη    : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ (Δ ▶ A)} →
    _≡_ {_} {Sub Γ (Δ ▶ A)}
    (_,s_ {Γ} {Δ} (π₁ {Γ} {Δ} {A} σ) {A} (π₂ {Γ} {Δ} {A} σ)) σ

  εη    : {Γ : Con} {σ : Sub Γ ∙} → _≡_ {_} {Sub Γ ∙} σ (ε {Γ})

-- (π₁ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t))
-- ==
  π₂β   : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ}
    {t : Tm Γ (_[_]T {Γ} {Δ} A σ)} →
    π₂ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)
    ==
    t
    [ (λ σ₁ → Tm Γ (_[_]T {Γ} {Δ} A σ₁)) ↓ (π₁β {Γ} {Δ} {A} {σ} {t})
        ]

{- 

t[id] = π₂ (id , t[id])
  = π₂ (id ∘ id , t[id])
  = π₂ ((id , t) ∘ id)
  = π₂ (id , t)
  = t

-}
[id]t : {Γ : Con}{A : Ty Γ}{t : Tm Γ A} →
   (t [ id ]t) == t [ Tm Γ ↓ [id]T ]
[id]t {Γ}{A}{t} =
  ≅↓ (helper _ _ (from-transp _ _ refl) (from-transp! _ _ refl))
  where
    eq :
      ∀ {t'}
      {t₂} (et₂ : (t₂ [ id ]t) == t' [ Tm _ ↓ [][]T ])
      (et₃ : t₂  == t [ Tm _ ↓ [id]T ]) →
      (id ∘ id ,s t') == (id ,s t [ id ]t)
    eq {t'}{t2 }et2 et3 =
      ap (λ su → ₁ su ,s ₂ su)
      (pair= idr
       (≅↓
         ( ( ↓≅ et2 !≅)
         ∘≅
         ↓≅ (ap↓ (λ t → t [ _ ]t) et3)
         )))
    helper : ∀ t'
      t₂ (et₂ : (t₂ [ id ]t) == t' [ Tm _ ↓ [][]T ])
       (et₃ : (t₂ ) == t [ Tm _ ↓ [id]T ])
      → t [ id ]t ≅ t 
    helper t' t₂ et₂ et₃ =
      
      (t [ id ]t)

        ≅⟨ (↓≅ π₂β) !≅ ⟩
      π₂ (id ,s t [ id ]t)

        ≅⟨
          (↓≅ (HoTT.apd π₂ {x = (id ∘ id) ,s t'} {y = id ,s t [ id ]t} (eq et₂ et₃)))
          !≅ ⟩
      π₂ ((id ∘ id) ,s t')

        ≅⟨ ↓≅ (HoTT.apd π₂ (,∘ {t = t₂}{ts = t'} et₂)) !≅ ⟩
      π₂ ((id ,s t₂) ∘ id)

        ≅⟨ ↓≅ (HoTT.apd π₂ idr) ⟩
      π₂ (id ,s t₂)
      
        ≅⟨ ↓≅ π₂β ⟩
      t₂

        ≅⟨ ↓≅ et₃ ⟩
      t
        ≅∎
      
     



     
{-
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
     -}

-- t=π₂ : {Δ}{A : Ty Δ}{t : Tm Δ A} →
--     π₂ ((id ,s t [ id ]t) ∘ σ)
--     == 
--     (t [ σ ]t)
  

-- TODO: utiliser ce lemme après
t[]=π₂∘ : ∀ {Γ}{Δ}{σ : Sub Γ Δ}{A : Ty Δ}{t : Tm Δ A}
  →
    π₂ ((id ,s t [ id ]t) ∘ σ)
    == 
    (t [ σ ]t)
    [ (λ s → Tm _ (A [ s ]T)) ↓
    ap π₁ (,∘ (from-transp _ _ refl )) ◾ π₁β ◾ idl
     ]

t[]=π₂∘ {Γ}{Δ}{σ}{A}{t} =
    helper(from-transp _ _ refl )
   
   where
    helper :
      {t'' : Tm Γ (A [ id ∘ σ ]T)}
      (et' : (t [ id ]t [ σ ]t) == t'' [ Tm Γ ↓ [][]T ])
      →
      π₂ ((id ,s t [ id ]t) ∘ σ)
      == 
      (t [ σ ]t)
      [ (λ s → Tm _ (A [ s ]T)) ↓
      ap π₁ (,∘ et') ◾ π₁β ◾ idl ]
    helper {t''} et' =
    
      ≅↓
      (
      π₂ ((id ,s t [ id ]t) ∘ σ)

        ≅⟨ ↓≅ (HoTT.apd π₂ (,∘ et')) ⟩
      π₂ (id ∘ σ ,s t'' )

        ≅⟨ ↓≅ π₂β ⟩
      t''

        ≅⟨ ↓≅ et' !≅ ⟩
      (t [ id ]t [ σ ]t)

        ≅⟨ ↓≅ (HoTT.ap↓ (λ z → z [ σ ]t) [id]t) ⟩
      (t [ σ ]t)
        ≅∎
      )
    


      
  



   
 


wk : ∀{Γ}{A : Ty Γ} → Sub (Γ ▶ A) Γ
wk {z} {z₁} = π₁ {z ▶ z₁} {z} {z₁} (id {z ▶ z₁})


     


vz : ∀{Γ}{A : Ty Γ} → Tm (Γ ▶ A) (A [ wk ]T)
vz {z} {z₁} = π₂ {z ▶ z₁} {z} {z₁} (id {z ▶ z₁})

wk∘, : ∀ {Γ Δ} {σ : Sub Γ Δ}{A : Ty Δ} {t : Tm Γ (A [ σ ]T)} →
  wk ∘ (σ ,s t) ≡ σ
wk∘, {Γ = Γ}{σ = σ} {A = A}{t = t} =
  helper _ (from-transp _ _ refl)
  where
  helper :
    ∀ (u : Tm Γ (A [ π₁ id ∘ (σ ,s t) ]T))
    (e : (vz [ σ ,s t ]t) == u [ Tm _ ↓ [][]T ])
    → wk ∘ (σ ,s t) ≡ σ

  helper u e = 
    (wk ∘ (σ ,s t)) =⟨ ! π₁β ⟩
    π₁ (((π₁ id) ∘ (σ ,s t)) ,s u) =⟨ ap π₁ (! (,∘ e)) ⟩
    π₁ ((π₁ id ,s π₂ id) ∘ (σ ,s t))   =⟨ ap (λ x → π₁ (x ∘ (σ ,s t)))  πη  ⟩
    π₁ (id ∘ (σ ,s t))   =⟨ ap π₁ idl ⟩
    π₁ (σ ,s t) =⟨ π₁β ⟩
    σ
    ∎

wk[]T : ∀ {Γ}{Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
  {B : Ty Δ}
  → (B [ wk ]T [ σ ,s t ]T ) ≡  B [ σ ]T
wk[]T = [][]T ◾ ap (_ [_]T) wk∘,


vz[,] : ∀ {Γ Δ} (σ : Sub Γ Δ)(A : Ty Δ) (t : Tm Γ (A [ σ ]T)) →
  (vz [ σ ,s t ]t) == t
  [ Tm Γ ↓ wk[]T ]
vz[,] {Γ}{Δ}σ A t = ≅↓
   (helper2 _ (from-transp (Tm Γ) [][]T refl))
  where
    helper2 : 
      ∀ (vz' : Tm Γ (A [ π₁ id ∘ (σ ,s t) ]T))
      (ez : (vz [ σ ,s t ]t) == vz' [ Tm _ ↓ [][]T ])
       →
       (vz [ σ ,s t ]t) ≅ t

    helper2 vz' ez  =
      (vz [ σ ,s t ]t)

          ≅⟨ ↓≅ ez ⟩
      vz'

          ≅⟨ (↓≅ π₂β)  !≅ ⟩
      π₂ ( (π₁ id ∘ (σ ,s t)) ,s vz')

          ≅⟨ ↓≅ (HoTT.apd π₂ (! (,∘ ez))) ⟩
      π₂ ( (π₁ id ,s π₂ id) ∘ (σ ,s t))

          ≅⟨ ↓≅ (HoTT.apd (λ s → π₂ (s ∘ (σ ,s t))) πη) ⟩
      π₂ ( id ∘ (σ ,s t))

          ≅⟨ ↓≅ (HoTT.apd π₂ idl) ⟩
      π₂ ( σ ,s t)

          ≅⟨ ↓≅ π₂β ⟩
      t
      ≅∎
      

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs {z} {z₁} {z₂} x =
  _[_]t {z ▶ z₂} {z} {z₁} x (π₁ {z ▶ z₂} {z} {z₂} (id {z ▶ z₂}))

-- todo utiliser ça pour faire les autres du genre [][]t, [id]t
<_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▶ A)
<_> {z} {z₁} t =
  id ,s transport! (Tm _) [id]T t

wk∘<> : ∀{Γ}{A : Ty Γ} → {t : Tm Γ A} → (wk ∘ < t >) ≡ id
wk∘<> {Γ}{A}{t} = wk∘,

vz<>  : ∀{Γ}{A : Ty Γ} → {t : Tm Γ A} → (vz [ < t > ]t) == t [ Tm Γ ↓
  -- [][]T ◾ ap (_ [_]T)  wk∘<>
    wk[]T  ◾ [id]T ]
vz<> {Γ}{A}{t} = ≅↓ helper
  where
  -- extensive use of UIP (don't know whether it is really necessary)
  helper : (vz [ < t > ]t) ≅ t 
  helper =
    ↓≅ (vz[,] id A (transport! (Tm _) [id]T t))
    ∘≅
    ↓≅ (from-transp! _ [id]T refl) 


-- simple first case (first step)
[id][]t : {Γ Δ : Con}  {A : Ty Δ} {t : Tm Δ A}{σ : Sub Γ Δ} →
  (t [ id ]t [ σ ]t) == t [ id ∘ σ ]t [ Tm Γ ↓ [][]T ]
[id][]t {Γ}{Δ}{A}{t}{σ} =
  ≅↓ helper
  where
    helper :
      (t [ id ]t [ σ ]t) ≅ t [ id ∘ σ ]t 
    helper =
      
      (t [ id ]t [ σ ]t)

        ≅⟨ ↓≅ (ap↓ (_[ σ ]t) [id]t) ⟩
      (t [  σ ]t )

        ≅⟨ ↓≅ (HoTT.apd (t [_]t) idl) !≅ ⟩
      (t [ id ∘ σ ]t)

      ≅∎
-- this is deduced of [id][]t
-- (looks like yoneda-like reasoning, isn't it ?)
[][]t : {Γ Δ : Con} {Σ : Con} {A : Ty Σ} {t : Tm Σ A}{σ : Sub Γ Δ}
  {δ : Sub Δ Σ} →
    (t [ δ ]t [ σ ]t) == t [ δ ∘ σ ]t [ Tm Γ ↓ [][]T ]

[][]t {Γ}{Δ}{Σ}{A}{t}{σ}{δ}=
  ≅↓ (helper (from-transp _ _ refl))
 where
 helper :
 
   ∀ {tδσ} (etδσ : (t [ id ∘ δ ]t [ σ ]t) == tδσ [ Tm Γ ↓ [][]T ])
    → (t [ δ ]t [ σ ]t) ≅ t [ δ ∘ σ ]t
 helper {tδσ} etδσ = 
  (t [ δ ]t [ σ ]t)

    ≅⟨ ↓≅
      (HoTT.apd (λ s → t [ s ]t [ σ ]t) idl)
       !≅ ⟩
  (t [ id ∘ δ ]t [ σ ]t)

    ≅⟨ ↓≅ etδσ ⟩
  tδσ
  
    ≅⟨ ↓≅ (π₂β {t = tδσ}) !≅ ⟩
  π₂ ((id ∘ δ) ∘ σ ,s tδσ) 

    ≅⟨ ↓≅ (HoTT.apd π₂ {x = ((id ∘ δ ,s t [ id ∘ δ ]t) ) ∘ σ}
      {y =  (id ∘ δ) ∘ σ ,s tδσ}
       (,∘ etδσ)) !≅ ⟩
  π₂ (((id ∘ δ ,s t [ id ∘ δ ]t) ) ∘ σ)

    ≅⟨ ↓≅ (HoTT.apd (λ s → π₂ (s ∘ σ)) (,∘ [id][]t)) !≅ ⟩
  π₂ (((id ,s t [ id ]t) ∘ δ) ∘ σ)
  
    ≅⟨ ↓≅ (HoTT.apd π₂ ass) ⟩
  π₂ ((id ,s t [ id ]t) ∘ (δ ∘ σ))

    ≅⟨ ↓≅ t[]=π₂∘ ⟩
  (t [ δ ∘ σ ]t)

    ≅∎

infix 4 <_>

wk[]t : ∀ {Γ}{Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
  {B : Ty Δ}{b : Tm Δ B}
  → (b [ wk ]t [ σ ,s t ]t) == b [ σ ]t [ Tm Γ ↓ wk[]T ]
wk[]t {Γ}{Δ}{A}{σ}{t}{B}{b} =
   ≅↓ helper
  where
    helper : 
      (b [ wk ]t [ σ ,s t ]t) ≅ b [ σ ]t
    helper =
      (b [ wk ]t [ σ ,s t ]t)

        ≅⟨ ↓≅ [][]t ⟩
      (b [ wk ∘ (σ ,s t)]t)

        ≅⟨ ↓≅ (HoTT.apd (b [_]t) wk∘,) ⟩
      (b [ σ ]t)
      ≅∎

-- In the syntax, this is keep
_^_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
_^_ {Γ} {Δ} σ A =
  σ ∘ wk ,s tr (Tm _) [][]T vz
  {- 
  _,s_ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Δ} (_∘_ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ}
  {Δ} σ (π₁ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ} {_[_]T {Γ} {Δ} A σ} (id {Γ ▶
  _[_]T {Γ} {Δ} A σ}))) {A} (coe {_} {Tm (Γ ▶ _[_]T {Γ} {Δ} A σ)
  (_[_]T {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ} (_[_]T {Γ} {Δ} A σ) (π₁ {Γ ▶
  _[_]T {Γ} {Δ} A σ} {Γ} {_[_]T {Γ} {Δ} A σ} (id {Γ ▶ _[_]T {Γ} {Δ} A
  σ})))} {Tm (Γ ▶ _[_]T {Γ} {Δ} A σ) (_[_]T {Γ ▶ _[_]T {Γ} {Δ} A σ}
  {Δ} A (_∘_ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ} {Δ} σ (π₁ {Γ ▶ _[_]T {Γ} {Δ}
  A σ} {Γ} {_[_]T {Γ} {Δ} A σ} (id {Γ ▶ _[_]T {Γ} {Δ} A σ}))))} (_&_
  {_} {suc _} {Ty (Γ ▶ _[_]T {Γ} {Δ} A σ)} {_} (Tm (Γ ▶ _[_]T
  {Γ} {Δ} A σ)) {_[_]T {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ} (_[_]T {Γ} {Δ} A σ)
  (π₁ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ} {_[_]T {Γ} {Δ} A σ} (id {Γ ▶ _[_]T
  {Γ} {Δ} A σ}))} {_[_]T {Γ ▶ _[_]T {Γ} {Δ} A σ} {Δ} A (_∘_ {Γ ▶ _[_]T
  {Γ} {Δ} A σ} {Γ} {Δ} σ (π₁ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ} {_[_]T {Γ}
  {Δ} A σ} (id {Γ ▶ _[_]T {Γ} {Δ} A σ})))} ([][]T {Γ ▶ _[_]T {Γ} {Δ} A
  σ} {Γ} {Δ} {A} {π₁ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ} {_[_]T {Γ} {Δ} A σ}
  (id {Γ ▶ _[_]T {Γ} {Δ} A σ})} {σ})) (π₂ {Γ ▶ _[_]T {Γ} {Δ} A σ} {Γ}
  {_[_]T {Γ} {Δ} A σ} (id {Γ ▶ _[_]T {Γ} {Δ} A σ})))
  -}

infixl 5 _^_

-- utile pour wk∘longWk
wk∘^ : {Γ : Con}{Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ} → wk ∘ (σ ^ A) ≡ σ ∘ wk
wk∘^ = wk∘,

-- utile pour liftV0

vz[^] : {Γ : Con}{Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ} →
   (vz [ (σ ^ A) ]t) == vz [ Tm _ ↓ [][]T ◾  ap (A [_]T) wk∘^ ◾ ! [][]T  ]

vz[^] {Γ}{Δ}{A}{σ} =
  ≅↓
    (
    (vz [ (σ ^ A) ]t)
    
      ≅⟨  ↓≅ (vz[,] (σ ∘ π₁ id) A _) ⟩

    tr (Tm _) [][]T vz

      ≅⟨  ↓≅ (from-transp (Tm _) [][]T refl) !≅ ⟩
    vz
    ≅∎
    )

^∘, : {Γ : Con}{Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ}{Y : Con}
    -- {δ : Sub Y (Γ ▶ A [ σ ]T)}
    {δ : Sub Y Γ}
    {t : Tm Y (A [ σ ]T [ δ ]T)}
   → (σ ^ A) ∘ (δ ,s t) ≡ σ ∘ δ ,s tr (Tm Y) [][]T t
^∘, {Γ}{Δ}{A}{σ}{Y}{δ}{t} = helper (from-transp _ [][]T refl)
  where
    helper : ∀ {vz[]} vz[]e → (σ ^ A) ∘ (δ ,s t) ≡ σ ∘ δ ,s tr (Tm Y) [][]T t
    helper {vz[]} vz[]e =
      ((σ ^ A) ∘ (δ ,s t) )

          -- =⟨ ,∘ {ts = vz[]} vz[]e ◾ {!!} ⟩
          -- =⟨ ,∘ {ts = vz[]} vz[]e ◾ {!!} ⟩
          =⟨ ,∘ {ts = vz[]} vz[]e ⟩
        ((σ ∘ wk) ∘ (δ ,s t) ,s vz[])

          =⟨
           ap (λ x → ₁ x ,s ₂ x)
            (pair=
              esub
              (≅↓ et))
           ⟩
          
        (σ ∘ δ ,s tr (Tm Y) [][]T t)

        =∎
      where
        esub : (σ ∘ wk) ∘ (δ ,s t) ≡ σ ∘ δ
        esub =  
                (((σ ∘ wk) ∘ (δ ,s t))

                  =⟨ ass ⟩
                (σ ∘ (wk ∘ (δ ,s t)))

                  =⟨ ap (_ ∘_) wk∘, ⟩
                (σ ∘ δ)
                  =∎)

        et : vz[] ≅ tr (Tm Y) [][]T t
        et = 
          vz[]

            ≅⟨ (↓≅ vz[]e) !≅ ⟩
          (tr (Tm (Γ ▶ A [ σ ]T)) [][]T vz [ δ ,s t ]t)

              ≅⟨ (↓≅ (ap↓ (_[ δ ,s t ]t) (from-transp (Tm (Γ ▶ A [ σ ]T)) [][]T refl))) !≅ ⟩
          (vz [ δ ,s t ]t)

          ≅⟨ ↓≅ (vz[,] _ _ _) ⟩
            t

          ≅⟨ ↓≅ (from-transp _ [][]T refl )  ⟩
            tr (Tm Y) [][]T t
          ≅∎
        

<>∘ : ∀ {Γ}{A : Ty Γ}{u : Tm Γ A}{Y}{σ : Sub Y (Γ)} →
  (< u > ∘ σ) ≡ ((σ ^  A) ∘ < u [ σ ]t > )
<>∘ {Γ}{A}{u}{Y}{σ} =
  
    (< u > ∘ σ)

        =⟨   ,∘ (from-transp (Tm Y) [][]T refl) ⟩
    (id ∘ σ ,s tr (Tm Y) ([][]T {A = A})(transport! (Tm Γ) [id]T u [ σ ]t))

      =⟨  helper ⟩
    (σ ∘ id ,s tr (Tm Y) ([][]T {A = A}) (transport! (Tm Y) [id]T (u [ σ ]t)))

      =⟨ ! ( ^∘, {A = A}{σ = σ}{δ = id}) ⟩
    ((σ ^ A) ∘ < u [ σ ]t >)
  =∎
  where
    helper :
      (id ∘ σ ,s tr (Tm Y) ([][]T {A = A})(transport! (Tm Γ) [id]T u [ σ ]t))
      ≡
      (σ ∘ id ,s tr (Tm Y) ([][]T {A = A}) (transport! (Tm Y) [id]T (u [ σ ]t)))
    helper =
      ap (λ x → ₁ x ,s ₂ x)
        (pair= (idl ◾ ! idr)
        (≅↓
         (((↓≅ (from-transp _ [][]T refl)) !≅)
         ∘≅ (↓≅ (ap↓ (_[ σ ]t) (from-transp! _ [id]T refl)))
         ∘≅ ((↓≅ (from-transp! _ [id]T refl)) !≅)
         ∘≅ (↓≅ (from-transp _ [][]T refl))
         )))
    
   

[<>][]T : ∀ {Γ}{A : Ty Γ}{u : Tm Γ A}{B : Ty (Γ ▶ A)}{Y}{σ : Sub Y (Γ)} →
  ( B [ < u > ]T [ σ ]T )
  ≡ ( B [ σ ^ A ]T [ < u [ σ ]t > ]T)

[<>][]T {Γ}{A}{u}{B}{Y}{σ} =
  [][]T {A =  B}{σ =  σ}{δ = _}
  ◾ ap   (λ s → (B [ s ]T)) (<>∘ {A = A})
  ◾ (! ([][]T {A =  B} ))

-- Universe
--------------------------------------------------------------------------------

postulate
  U    : ∀{Γ} → Ty Γ
  -- U[]  : {Γ Δ : Con} {σ : Sub Γ Δ} → _≡_ {i} {Ty Γ} (_[_]T {Γ} {Δ} (U {Δ}) σ) (U {Γ})
  U[]  : {Γ Δ : Con} {σ : Sub Γ Δ} → _↦_ {i} {Ty Γ} (_[_]T {Γ} {Δ} (U {Δ}) σ) (U {Γ})
{-# REWRITE U[]  #-}

postulate
  El   : ∀{Γ}(a : Tm Γ U) → Ty Γ

  El[] :
    {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} →
    _↦_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (El {Δ} a) σ)
    (El {Γ} (a [ σ ]t))
{-# REWRITE El[]  #-}



-- Inductive function
--------------------------------------------------------------------------------
postulate
  Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ
  Π[] :
    {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)} →
    ((Π a B) [ σ ]T) ↦ Π (a [ σ ]t) (B [ σ ^ El a ]T)

{-# REWRITE Π[]  #-}

{- 
  Π[] :
    {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)} →
    _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (Π {Δ} a B) σ) (Π {Γ} (tr {_}
    {_} {Ty Γ} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ}
    {σ}) (_[_]t {Γ} {Δ} {U {Δ}} a σ)) (tr {_} {_} {Ty Γ} (λ x → Ty
    (Γ ▶ x)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (tr {_} {_} {Ty Γ}
    (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}) (_[_]t {Γ}
    {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ}
    (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a)))))
    -}

postulate
  app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B

-- TODO: voir si on peut le demander en définitional: est ce la cas dans la syntaxe ?
  app[] :
    {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)}
    {t : Tm Δ (Π {Δ} a B)} →
    app t [ σ ^ El a ]t ≡ app (t [ σ ]t)
    {- 
    {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)}
    {t : Tm Δ (Π {Δ} a B)} → _≡_ {_} {Tm (Γ ▶ El {Γ} (coe {_} {Tm Γ
    (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty
    -- Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
    Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} refl)
    (_[_]t {Γ} {Δ} {U {Δ}} a σ))) (tr {_} {_} {Ty Γ} (λ z → Ty (Γ ▶
    z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ}
    {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm
    Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} refl) (_[_]t {Γ} {Δ}
    -- Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ}
    {U {Δ}} a σ))} refl (_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El
    -- {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El
    {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a))))} (tr2 {_}
    {_} {_} {Ty Γ} {λ z → Ty (Γ ▶ z)} (λ A → Tm (Γ ▶ A)) {_[_]T {Γ}
    {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)}
    {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm Γ) {_[_]T {Γ}
    {Δ} (U {Δ}) σ} {U {Γ}} refl) (_[_]t {Γ} {Δ} {U {Δ}} a
    -- {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ} {U {Δ}} a
    σ))} refl {_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El {Δ} a) σ} {Δ
    -- σ))} (El[] {Γ} {Δ} {σ} {a}) {_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El {Δ} a) σ} {Δ
    ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a))} {tr {_} {_} {Ty Γ} (λ
    z → Ty (Γ ▶ z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ
    (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty
    Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} refl)
    -- Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
    (_[_]t {Γ} {Δ} {U {Δ}} a σ))} refl (_[_]T {Γ ▶ _[_]T
    -- (_[_]t {Γ} {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T
    {Γ} {Δ} (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a)))}
    refl (_[_]t {Γ ▶ _[_]T {Γ} {Δ} (El {Δ} a) σ} {Δ ▶ El {Δ} a} {B} (app
    {Δ} {a} {B} t) (_^_ {Γ} {Δ} σ (El {Δ} a)))) (app {Γ} {coe {_} {Tm Γ
    (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty
    Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} refl)
    -- Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
    (_[_]t {Γ} {Δ} {U {Δ}} a σ)} {tr {_} {_} {Ty Γ} (λ z → Ty (Γ ▶
    z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T {Γ}
    {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_} (Tm
    Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} refl) (_[_]t {Γ} {Δ}
    -- Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ} {Δ}
    {U {Δ}} a σ))} refl (_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El
    -- {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ} (El
    {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a)))} (tr {_}
    {_} {Ty Γ} (Tm Γ) {_[_]T {Γ} {Δ} (Π {Δ} a B) σ} {Π {Γ} (coe {_}
    {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _}
    {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} refl)
    -- {Ty Γ} {_} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
    (_[_]t {Γ} {Δ} {U {Δ}} a σ)) (tr {_} {_} {Ty Γ} (λ z → Ty
    (Γ ▶ z)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (coe {_} {Tm Γ (_[_]T
    {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})} (_&_ {_} {suc _} {Ty Γ} {_}
    (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} refl) (_[_]t {Γ}
    -- (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ})) (_[_]t {Γ}
    {Δ} {U {Δ}} a σ))} refl (_[_]T {Γ ▶ _[_]T {Γ} {Δ}
    -- {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ}
    (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a))))} refl
    -- (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a))))} (Π[] {Γ} {Δ} {σ} {a} {B})
    (_[_]t {Γ} {Δ} {Π {Δ} a B} t σ)))
    -}


_$_ : ∀ {Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}(t : Tm Γ (Π a B))(u : Tm Γ (El a)) → Tm Γ (B [ < u > ]T)
_$_ {Γ} {a} {B} t u = app t [ < u > ]t

-- nécessaire pour le weakening (application)
$[] : 
  ∀ {Y}{Γ}{σ : Sub Y Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}{t : Tm Γ (Π a B)}{u : Tm Γ (El a)}
  → ((t $ u) [ σ ]t) == (t [ σ ]t) $ (u [ σ ]t) [ Tm _ ↓ [<>][]T {Γ}{El a}{u}{B} ]

$[] {Y}{Γ}{σ}{a}{B}{t}{u} =
  ≅↓
    (
      ((t $ u) [ σ ]t)

          ≅⟨ ↓≅ [][]t ⟩
      (app t [ < u > ∘ σ ]t)

          ≅⟨ ↓≅ (HoTT.apd (app t [_]t) <>∘)  ⟩
      (app t [ (σ ^ El a) ∘ < u [ σ ]t > ]t)

          ≅⟨ (↓≅ [][]t) !≅  ⟩
      (app t [ (σ ^ El a) ]t [ < u [ σ ]t > ]t)

          ≅⟨ =≅ (ap (_[  < u [ σ ]t >  ]t) app[]) ⟩
      (app (t [ σ ]t) [ < u [ σ ]t > ]t )
      ≅∎
    )
 {- 
  _[_]t {z} {z ▶ El {z} z₁} {z₂} (app {z} {z₁} {z₂} t) (_,s_ {z} {z}
  (id {z}) {El {z} z₁} (coe {_} {Tm z (El {z} z₁)} {Tm z (_[_]T {z}
  {z} (El {z} z₁) (id {z}))} (_&_ {_} {suc _} {Ty z} {_} (Tm
  z) {El {z} z₁} {_[_]T {z} {z} (El {z} z₁) (id {z})}
  e)
  u))
  -}
  -- where
  --   e : El a ≡ El a [ id ]T
  --   e =
    -- _⁻¹ {_} {Ty z} {_[_]T {z} {z} (El {z} z₁) (id {z})} {El {z} z₁} ([id]T {z} {El {z} z₁})




{- ------------

Telescopes:
Ils sont nécessaires pour la raison suivante:
- preuve que la substitution préserve la relation ~ pour B du cas Π A B: j'ai un
weakening d'une substitution dont je dois prouver la relation
- j'en déduis que je dois d'abord prouver que le weakening préserve la relation
- Cela nécessite une notion de lift (le weakening ne suffit pas: Cf le cas Π A B) et donc de
télescope

je reprends la notion de télescope que j'avais faite pour le modèle standard

------------   -}

data isTel  (Γ : Con) : (Δ : Con) → Set i where
  is∙t : isTel Γ Γ
  is▶t : ∀ {Δ} → isTel Γ Δ → (A : Ty Δ) → isTel Γ (Δ ▶ A)

Tel : Con → Set i
Tel Γ = Σ _ (isTel Γ)

∙t : (Γ : Con) → Tel Γ
∙t Γ = _ , is∙t 

_^^_ : (Γ : Con) (Δ : Tel Γ) → Con
_^^_ Γ Δ = ₁ Δ

_▶t_  : ∀ {Γ}(Δ : Tel Γ) → Ty (Γ ^^ Δ) → Tel Γ
_▶t_ {Γ} Δ A = (₁ Δ ▶ A) , is▶t (₂ Δ) A

Telₛ : {Γ Δ : Con} → ∀ {T}(iT : isTel Δ T) (s : Sub Γ Δ)  → Σ (Tel Γ) (λ x → Sub (Γ ^^ x) (Δ ^^ (_ , iT)))
Telₛ {_} {Δ} is∙t s  = ( _ , is∙t ) , s
-- Telₛ {Γ} {Δ} {.(Σ (₁ T) (₁ A) , _ , _)}  (is▶t T iT A) s  =
Telₛ {Γ} {Δ}   (is▶t {T} iT A) s  =
  (_ , is▶t (₂ (₁ (Telₛ iT s))) (A [ ₂ (Telₛ iT s)  ]T)) ,
  ((₂ (Telₛ iT s)) ^ A)

_[_]Te  : {Γ Δ : Con} → ∀ (T : Tel Δ) (s : Sub Γ Δ)  → Tel Γ
T [ s ]Te = ₁ (Telₛ (₂ T) s)

longₛ : {Γ Δ : Con} → ∀ (T : Tel Δ) (s : Sub Γ Δ)  → Sub (Γ ^^ (T [ s ]Te)) (Δ ^^ T)
longₛ T s = ₂ (Telₛ (₂ T) s)
longWk : ∀{Γ}{E : Ty Γ}(Δ : Tel Γ) → Sub ((Γ ▶ E) ^^ (Δ [ wk {Γ = Γ} {A = E} ]Te)) (Γ ^^ Δ)
longWk {Γ}{E} Δ = longₛ Δ (wk {Γ = Γ}{A = E})

wkTel : {Γ : Con}(E : Ty Γ)(Δ : Tel Γ) → Tel (Γ ▶ E)
wkTel {Γ} E Δ = Δ [ wk {Γ = Γ}{A = E} ]Te


liftT : {Γ : Con}(Δ : Tel Γ)(Ex : Ty Γ)(A : Ty (Γ ^^ Δ)) → Ty ((Γ ▶ Ex) ^^ wkTel Ex Δ)
liftT {Γ} Δ Ex A = A [ longWk {Γ = Γ}{Ex}Δ ]T

liftt : {Γ : Con}(Δ : Tel Γ)(Ex : Ty Γ){A : Ty (Γ ^^ Δ)}(t : Tm (Γ ^^ Δ) A) →
  Tm ((Γ ▶ Ex) ^^ wkTel Ex Δ) (liftT Δ Ex A)
liftt {Γ} Δ Ex {A} t = t [ longWk Δ ]t
  -- {A = A}
  -- t
  -- (longWk  Δ)


wk∘longWk : {Γ : Con}{Δ : Tel Γ}(A : Ty (Γ ^^ Δ))
   {E : Ty Γ} →
     wk ∘ longWk {E = E} (Δ ▶t A) ≡ longWk Δ ∘ wk

--   
wk∘longWk {Γ}{Δ}A {E} =
   (wk ∘ (longWk Δ ^ A))
   =⟨  wk∘^ ⟩
    (longWk Δ ∘  wk)
  =∎

  


-- for this one, I checked the need of the explicit arguments
-- for the inference engine
lift-wkT : {Γ : Con}(Δ : Tel Γ){A : Ty (Γ ^^ Δ)}
  (B : Ty (Γ ^^ Δ))
  {E : Ty Γ} →
  -- liftT Γ (Δ ▶t A) E (wkT (Γ ^^ Δ) A B) ≡
  liftT (Δ ▶t A) E (B [ wk ]T) ≡ liftT Δ E B [ wk ]T
   -- wkT (Γ ▶ E ^^ wkTel Γ E Δ) (liftT Γ Δ E A) (liftT Γ Δ E B)

lift-wkT {Γ} Δ {A} B {E} =
  
  (B [ wk ]T [ longWk (Δ ▶t A)]T)

    =⟨  [][]T {A = B} ⟩
  (B [ wk ∘ longWk (Δ ▶t A)]T)

    =⟨  ap (B [_]T) ( wk∘longWk {Δ = Δ} A {E} ) ⟩
  (B [ longWk Δ ∘ wk ]T)

    =⟨  ! ([][]T {A = B}) ⟩
  (B [ longWk Δ ]T [ wk ]T)
  =∎
  

lift-wkt : {Γ : Con}(Δ : Tel Γ){A : Ty (Γ ^^ Δ)}
  {B : Ty (Γ ^^ Δ)}(t : Tm (Γ ^^ Δ) B)
  {E : Ty Γ} →
-- liftT Γ (Δ ▶t A) E (wkT (Γ ^^ Δ) A B) ≡
  liftt {Γ = Γ} (Δ ▶t A) E (t [ wk ]t) == liftt {Γ = Γ} Δ E t [ wk ]t [ Tm _ ↓ lift-wkT Δ B ]

lift-wkt {Γ}Δ{B}t{E} =
  ≅↓
    ((↓≅ [][]t)
    ∘≅ (↓≅ (apd (t [_]t) ( wk∘longWk {Δ = Δ} B {E} )))
    ∘≅ ((↓≅ ([][]t)) !≅) )

liftV0 : {Γ : Con}(Δ : Tel Γ) (A : Ty (Γ ^^ Δ))(Ex : Ty Γ) →
  liftt  (Δ ▶t A)  Ex {A [ wk ]T} vz
  == vz   [ Tm _ ↓ lift-wkT Δ A  ]

liftV0 {Γ} Δ A Ex =
  ≅↓
  ((vz [ longWk ( Δ ▶t A) ]t)
      ≅⟨  ↓≅ vz[^] ⟩
    vz
    ≅∎)

<>∘longWk :
  {Γ : Con}(Δ : Tel Γ){E : Ty Γ} {A : Ty (Γ ^^ Δ)}
  {t : Tm (Γ ^^ Δ) A} →
  (< t > ∘ longWk {E = E} Δ) ≡ (longWk {E = E}(Δ ▶t A) ∘ < t [ longWk Δ ]t >)
<>∘longWk {Γ}Δ{E}{A}{t} = <>∘

lift-subT : {Γ : Con}(Δ : Tel Γ){E : Ty Γ} {A : Ty (Γ ^^ Δ)}{B : Ty ((Γ ^^ Δ) ▶ A)}
  {t : Tm (Γ ^^ Δ) A} →
  liftT Δ E (B [ < t > ]T) ≡   (liftT (Δ ▶t A) E B) [ < (liftt Δ E t) > ]T

lift-subT {Γ} Δ {E}{A}{B}{t} =
  
  (B [ < t > ]T [ longWk Δ ]T)

    =⟨  [][]T {A = B} ⟩
  (B [ < t > ∘ longWk Δ ]T)

    =⟨  ap (B [_]T) (<>∘longWk  Δ {E = E} ) ⟩
  (B [ longWk (Δ ▶t A) ∘ < t [ longWk Δ ]t > ]T)

    =⟨  ! ([][]T {A = B}) ⟩
  (B [ longWk (Δ ▶t A) ]T [ < t [ longWk Δ ]t > ]T)
  =∎
  


{-
Old stuff
-}
-- ??? pourquoi pas de [][]t ??
-- t = π₂ (id , t)  
-- t[σ] = π₂ ((id , t) ∘ σ)
-- t[σ][δ] = π₂ (((id , t) ∘ σ) ∘ δ)
--         = π₂ ( (id , t) ∘ (σ ∘ δ))
--         = t[σ∘δ]
-- et donc
-- t [σ][δ] = (π₂ (id , t)) [σ][δ]
--          = (π₂ (id ∘ σ, (π₂ (id , t) [σ])))[δ]
--          = π₂ ((id , t) ∘ σ)
{-
t[]=π₂∘ : ∀ {Γ}{Δ}{σ : Sub Γ Δ}{A : Ty Δ}{t : Tm Δ A}
  {t' : Tm Δ (A [ id ]T)}
  (et : t' == t [ Tm Δ ↓ [id]T ])
  {t'' : Tm Γ (A [ id ∘ σ ]T)}
  (et' : (t' [ σ ]t) == t'' [ Tm Γ ↓ [][]T ])
  →
    π₂ ((id ,s t') ∘ σ)
    == 
    (t [ σ ]t)
    [ (λ s → Tm _ (A [ s ]T)) ↓
     ap π₁ (,∘ et') ◾ π₁β ◾ idl ]
t[]=π₂∘ {Γ}{Δ}{σ}{A}{t}{t'}et{t''} et'' =
  ≅↓
   (
   π₂ ((id ,s t') ∘ σ)

    ≅⟨ ↓≅ (HoTT.apd π₂ (,∘ et'')) ⟩
  π₂ (id ∘ σ ,s t'' )

    ≅⟨ ↓≅ π₂β ⟩
  t''

    ≅⟨ ↓≅ et'' !≅ ⟩
  (t' [ σ ]t)

    ≅⟨ ↓≅ (HoTT.ap↓ (λ z → z [ σ ]t) et) ⟩
  (t [ σ ]t)
    ≅∎
   )
   -}
{-
  El[] :
    {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} →
    _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (El {Δ} a) σ)
    (El {Γ}
     (coe {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})}
      (_&_ {_} {suc _} {Ty Γ} {_} (Tm Γ)
       {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
      (_[_]t {Γ} {Δ} {U {Δ}} a σ)))


_^El_ :
  {Γ Δ : Con}(σ : Sub Γ Δ)(a : Tm Δ U)
  → Sub (Γ ▶ El (tr (Tm Γ) (U[] ) (a [ σ ]t))) (Δ ▶ El a)
_^El_ {Γ}{Δ} σ a = σ ∘ wk ,s tr (Tm (Γ ▶ El (tr (Tm Γ) (U[] {σ = σ}) (a [ σ ]t))))
                                  (((_[ wk ]T) & (El[] {Γ}{Δ}{σ}{a} ⁻¹)) ◾
                                  ([][]T {A = El a}{wk}{σ})) vz

infixl 5 _^El_

_^U : ∀ {Γ Δ}(σ : Sub Γ Δ) → Sub (Γ ▶ U) (Δ ▶ U)
_^U {Γ} {Δ} σ =
  _,s_ {Γ ▶ U {Γ}} {Δ} (_∘_ {Γ ▶ U {Γ}} {Γ} {Δ} σ (π₁ {Γ ▶ U {Γ}} {Γ}
  {U {Γ}} (id {Γ ▶ U {Γ}}))) {U {Δ}} (coe {_} {Tm (Γ ▶ U {Γ})
  (_[_]T {Γ ▶ U {Γ}} {Γ} (U {Γ}) (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶
  U {Γ}})))} {Tm (Γ ▶ U {Γ}) (_[_]T {Γ ▶ U {Γ}} {Δ} (U {Δ}) (_∘_ {Γ ▶
  U {Γ}} {Γ} {Δ} σ (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶ U {Γ}}))))}
  (_&_ {_} {suc _} {Ty (Γ ▶ U {Γ})} {_} (Tm (Γ ▶ U {Γ}))
  {_[_]T {Γ ▶ U {Γ}} {Γ} (U {Γ}) (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶
  U {Γ}}))} {_[_]T {Γ ▶ U {Γ}} {Δ} (U {Δ}) (_∘_ {Γ ▶ U {Γ}} {Γ} {Δ} σ
  (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶ U {Γ}})))} (_◾_ {_} {Ty (Γ
  ▶ U {Γ})} {_[_]T {Γ ▶ U {Γ}} {Γ} (U {Γ}) (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}}
  (id {Γ ▶ U {Γ}}))} {U {Γ ▶ U {Γ}}} {_[_]T {Γ ▶ U {Γ}} {Δ} (U {Δ})
  (_∘_ {Γ ▶ U {Γ}} {Γ} {Δ} σ (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶ U
  {Γ}})))} (U[] {Γ ▶ U {Γ}} {Γ} {π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶ U
  {Γ}})}) (_⁻¹ {_} {Ty (Γ ▶ U {Γ})} {_[_]T {Γ ▶ U {Γ}} {Δ} (U {Δ})
  (_∘_ {Γ ▶ U {Γ}} {Γ} {Δ} σ (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶ U
  {Γ}})))} {U {Γ ▶ U {Γ}}} (U[] {Γ ▶ U {Γ}} {Δ} {_∘_ {Γ ▶ U {Γ}} {Γ}
  {Δ} σ (π₁ {Γ ▶ U {Γ}} {Γ} {U {Γ}} (id {Γ ▶ U {Γ}}))})))) (π₂ {Γ ▶ U
  {Γ}} {Γ} {U {Γ}} (id {Γ ▶ U {Γ}})))

-- Identity
--------------------------------------------------------------------------------

postulate
  Id   : ∀ {Γ}(a : Tm Γ U) → Tm Γ (El a) → Tm Γ (El a) → Ty Γ
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

  Reflect : ∀ {Γ}{a : Tm Γ (U {Γ})}{t u : Tm Γ (El a)} → Tm Γ (Id a t u) → t ≡ u
  -}
