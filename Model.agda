


open import Level
open import EqLib renaming (fst to ₁ ; snd to ₂ ; _∙_ to _◾_ ) hiding (_∘_ ; _⁻¹ ; Π ; _$_)
open import Lib hiding (tr2)

module Model   where


record baseCwF {i : Level}{j : Level} : Set (Level.suc (lmax i j)) where
 field
  Con : Set i
  Ty  : Con → Set i
  Tm  : ∀ Γ → Ty Γ → Set j
  Sub : Con → Con → Set j

record nextCwF {i : Level}{j : Level}(b : baseCwF {i}{j}) : Set (Level.suc (lmax i j)) where
 open baseCwF b
 infixl 7 _[_]T
 infixl 5 _,s_
 infix  6 _∘_
 infixl 8 _[_]t
 infixl 4 _▶_
 field

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

  idl   : {Γ Δ : Con} {σ : Sub Γ Δ} →  (id ∘ σ) ≡ σ
  idr   : {Γ Δ : Con} {σ : Sub Γ Δ} →  (σ ∘ id) ≡ σ

  ass   : {Γ Δ : Con} {Σ : Con} {Ω : Con} {σ : Sub Σ Ω} {δ : Sub Δ Σ}
    {ν : Sub Γ Δ} → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)


{-
  π₁∘ : ∀ {Γ Δ} {A : Ty Δ}{σ : Sub Γ (Δ ▶ A)}
    {Y}{δ : Sub Y Γ} →
    π₁ (σ ∘ δ) ≡ (π₁ σ ∘ δ )

  π₂∘ : ∀ {Γ Δ} {A : Ty Δ}{σ : Sub Γ (Δ ▶ A)}
    {Y}{δ : Sub Y Γ} →
    π₂ (σ ∘ δ) == (π₂ σ [ δ ]t)  [ Tm _ ↓ ap (A [_]T) π₁∘ ◾ ! [][]T ]
    -}
  -- instead, I postulate this
  π₁,∘ :
    {Γ Δ : Con} {Σ : Con} {δ : Sub Γ Δ} {σ : Sub Σ Γ} {A : Ty Δ}
    {t : Tm Γ (_[_]T {Γ} {Δ} A δ)}
    → π₁ ((δ ,s t) ∘ σ) ≡ δ ∘ σ
  π₂,∘ :
    {Γ Δ : Con} {Σ : Con} {δ : Sub Γ Δ} {σ : Sub Σ Γ} {A : Ty Δ}
    {t : Tm Γ (_[_]T {Γ} {Δ} A δ)}
    → π₂ ((δ ,s t) ∘ σ) == (t [ σ ]t) [ Tm _ ↓  ap (A [_]T) π₁,∘ ◾  ! [][]T ]



  π₁β   : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ}
     {t : Tm Γ (_[_]T {Γ} {Δ} A σ)} →
     _≡_ {_} {Sub Γ Δ} (π₁ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)) σ

  πη    : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ (Δ ▶ A)} →
    _≡_ {_} {Sub Γ (Δ ▶ A)}
    (_,s_ {Γ} {Δ} (π₁ {Γ} {Δ} {A} σ) {A} (π₂ {Γ} {Δ} {A} σ)) σ

  εη    : {Γ : Con} {σ : Sub Γ ∙} → _≡_ {_} {Sub Γ ∙} σ (ε {Γ})

  π₂β   : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ}
    {t : Tm Γ (_[_]T {Γ} {Δ} A σ)} →
    π₂ {Γ} {Δ} {A} (_,s_ {Γ} {Δ} σ {A} t)
    ==
    t
    [ (λ σ₁ → Tm Γ (_[_]T {Γ} {Δ} A σ₁)) ↓ (π₁β {Γ} {Δ} {A} {σ} {t}) ]



  -- infixl 7 _[_]T
  -- infixl 5 _,s_
  -- infix  6 _∘_
  -- infixl 8 _[_]t
  -- infixl 4 _▶_

 wk : ∀{Γ}{A : Ty Γ} → Sub (Γ ▶ A) Γ
 wk {z} {z₁} = π₁ {z ▶ z₁} {z} {z₁} (id {z ▶ z₁})


 vz : ∀{Γ}{A : Ty Γ} → Tm (Γ ▶ A) (A [ wk ]T)
 vz {z} {z₁} = π₂ {z ▶ z₁} {z} {z₁} (id {z ▶ z₁})

 vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
 vs {z} {z₁} {z₂} x = _[_]t {z ▶ z₂} {z} {z₁} x (π₁ {z ▶ z₂} {z} {z₂} (id {z ▶ z₂}))

 -- todo utiliser ça pour faire les autres du genre [][]t, [id]t
 <_> : ∀{Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▶ A)
 <_> {z} {z₁} t = id ,s transport! (Tm _) [id]T t

 infix 4 <_>


 -- In the syntax, this is keep
 _^_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ (A [ σ ]T)) (Δ ▶ A)
 _^_ {Γ} {Δ} σ A = (σ ∘ wk) ,s transport (Tm _) [][]T vz

 infixl 5 _^_

 ,s= : ∀ {Γ Δ }{σ δ : Sub Γ Δ} {A : Ty Δ}{t : Tm _ (A [ σ ]T)}{u : Tm _ (A [ δ ]T)} →
   (e : σ ≡ δ) → t == u [ (λ s → Tm _ (A [ s ]T)) ↓ e ] → (σ ,s t) ≡ (δ ,s u)
 ,s= {Γ}{Δ}{σ}{δ}{A}{t} refl refl  = refl

 ,∘    :
   {Γ Δ : Con} {Σ : Con} {δ : Sub Γ Δ} {σ : Sub Σ Γ} {A : Ty Δ}
   {t : Tm Γ (_[_]T {Γ} {Δ} A δ)}
   {ts : Tm Σ (A [ δ ∘ σ ]T)}
   (et : (t [ σ ]t) == ts [ Tm Σ ↓  [][]T ])
   →
   ((δ ,s t) ∘ σ)
   ≡ ((δ ∘ σ) ,s ts)

 ,∘ {Γ}{Δ}{Σ}{δ}{σ}{A}{t}{ts}et =
     ! πη ◾ ,s= π₁,∘
       (≅↓ (↓≅ π₂,∘
         ∘≅ ↓≅ et))
 {-

 ,∘ {Γ}{Δ}{Σ}{δ}{σ}{A}{t}{ts}et =
   ! πη ◾
     ,s=
       (π₁∘ {σ = (δ ,s t)} ◾ ap (_∘ _) π₁β)
       (≅↓
         (  ↓≅ (π₂∘{σ = (δ ,s t)})
         ∘≅  ↓≅ (ap↓ (_[ σ ]t) π₂β)
         ∘≅ ↓≅ et))

 -}
 π₁∘ : ∀ {Γ Δ} {A : Ty Δ}{σ : Sub Γ (Δ ▶ A)}
    {Y}{δ : Sub Y Γ} →
    π₁ (σ ∘ δ) ≡ (π₁ σ ∘ δ )
 π₁∘ {Γ}{Δ}{A}{σ}{Y}{δ} =
   -- transport (λ s → π₁ (s ∘ δ) ≡ π₁ s ∘ δ) πη (π₁,∘ ◾ ap (λ s → s ∘ δ) (! π₁β))
   ap (λ s → π₁ (s ∘ δ)) (! πη) ◾ π₁,∘
   -- (π₁,∘ ◾ ap (λ s → s ∘ δ) (! π₁β))

 π₂∘ : ∀ {Γ Δ} {A : Ty Δ}{σ : Sub Γ (Δ ▶ A)}
    {Y}{δ : Sub Y Γ} →
    π₂ (σ ∘ δ) == (π₂ σ [ δ ]t)  [ Tm _ ↓ ap (A [_]T) π₁∘ ◾ ! [][]T ]
 π₂∘ {Γ}{Δ}{A}{σ}{Y}{δ} =
   -- use of uip for simplicty
   ≅↓ (
   -- transport (λ s → π₂ (_∘_ s δ) ≅ _[_]t (π₂ σ) δ) πη
   ↓≅ (apd (λ s → π₂( s ∘ δ)) (! πη))
   ∘≅
   (↓≅ π₂,∘))


record CwF {i : Level}{j : Level} : Set (Level.suc (lmax i j)) where
 -- infixl 7 _[_]T
 -- infixl 5 _,s_
 -- infix  6 _∘_
 -- infixl 8 _[_]t
 -- infixl 4 _▶_
 field
  basecwf : baseCwF {i}{j}
  nextcwf : nextCwF basecwf
 open baseCwF basecwf public
 open nextCwF nextcwf public


 wk∘, : ∀ {Γ Δ} {σ : Sub Γ Δ}{A : Ty Δ} {t : Tm Γ (A [ σ ]T)} →
   wk ∘ (σ ,s t) ≡ σ
 wk∘, {Γ = Γ}{σ = σ} {A = A}{t = t} =
     (wk ∘ (σ ,s t)) =⟨ ! π₁,∘ ⟩
     π₁ ((π₁ id ,s π₂ id) ∘ (σ ,s t))   =⟨ ap (λ x → π₁ (x ∘ (σ ,s t)))  πη  ⟩
     π₁ (id ∘ (σ ,s t))   =⟨ ap π₁ idl ⟩
     π₁ (σ ,s t) =⟨ π₁β ⟩
     σ
     ∎
 wk∘ : ∀ {Γ Δ}{A : Ty Δ} {σ : Sub Γ (Δ ▶ A)}  →
   wk ∘ σ  ≡ π₁ σ
 wk∘{Γ}{Δ}{A}{σ} =
   ap (λ s → wk ∘ s) (! πη) ◾ wk∘,


 wk[]T : ∀ {Γ}{Δ}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
   {B : Ty Δ}
   → (B [ wk ]T [ σ ,s t ]T ) ≡  B [ σ ]T
 wk[]T = [][]T ◾ ap (_ [_]T) wk∘,


 vz[,] : ∀ {Γ Δ} (σ : Sub Γ Δ)(A : Ty Δ) (t : Tm Γ (A [ σ ]T)) →
   (vz [ σ ,s t ]t) == t
   [ Tm Γ ↓ wk[]T ]
 vz[,] {Γ}{Δ}σ A t = ≅↓
       ( (vz [ σ ,s t ]t)
           ≅⟨ ↓≅ π₂,∘ !≅ ⟩
       π₂ ( (π₁ id ,s π₂ id) ∘ (σ ,s t))

           ≅⟨ ↓≅ (apd (λ s → π₂ (s ∘ (σ ,s t))) πη) ⟩
       π₂ ( id ∘ (σ ,s t))

           ≅⟨ ↓≅ (apd π₂ idl) ⟩
       π₂ ( σ ,s t)

           ≅⟨ ↓≅ π₂β ⟩
       t
       ≅∎)


 <>∘ : ∀ {Γ}{A : Ty Γ}{u : Tm Γ A}{Y}{σ : Sub Y (Γ)} →
   < u > ∘ σ ≡ (σ ,s (u [ σ ]t) )

 <>∘ {Γ}{A}{u}{Y}{σ} =
   (< u > ∘ σ)

       =⟨ ( (,∘ {δ = id}{σ = σ} {t = transport! (Tm Γ) [id]T u} (from-transp _ [][]T refl) )) ⟩
   (((id ∘ σ) ,s (transport (Tm Y) [][]T (transport! (Tm Γ) [id]T u [ σ ]t))) )

       =⟨ ,s= idl (≅↓ (((↓≅ (from-transp _ [][]T refl)) !≅) ∘≅ (↓≅ (ap↓ (_[ σ ]t) (from-transp! _ [id]T refl)))))  ⟩
     (σ ,s (u [ σ ]t ))
   =∎

 π₁<>∘ : ∀ {Γ}{A : Ty Γ}{t : Tm Γ A}{Y}{σ : Sub Y (Γ)} →
   π₁ (< t > ∘ σ) ≡ σ

 π₁<>∘ = ap π₁ <>∘ ◾ π₁β

 π₂<>∘ : ∀ {Γ}{A : Ty Γ}{t : Tm Γ A}{Y}{σ : Sub Y (Γ)} →
   (π₂ (< t > ∘ σ)) == (t [ σ ]t) [ (λ s → Tm _ (A [ s ]T)) ↓ π₁<>∘ ]

 π₂<>∘ {Γ}{A}{t}{σ}  = ≅↓ (↓≅ (apd π₂ <>∘) ∘≅ ↓≅ π₂β)



 wk∘<> : ∀{Γ}{A : Ty Γ} → {t : Tm Γ A} → (wk ∘ < t >) ≡ id
 wk∘<> {Γ}{A}{t} = wk∘,

 π₂<> : ∀{Γ}{A : Ty Γ} {t :  Tm Γ A} → (π₂ < t >) == t [ Tm _ ↓ ap (A [_]T) π₁β ◾ [id]T ]
 π₂<> {Γ}{A}{t} = ≅↓ ((↓≅ π₂β) ∘≅ ↓≅ (from-transp! _ [id]T refl))

 vz<>  : ∀{Γ}{A : Ty Γ} → {t : Tm Γ A} → (vz [ < t > ]t) == t [ Tm Γ ↓ wk[]T  ◾ [id]T ]
 vz<> {Γ}{A}{t} = ≅↓ helper
   where
   -- extensive use of UIP (don't know whether it is really necessary)
   helper : (vz [ < t > ]t) ≅ t
   helper =
     ↓≅ (vz[,] id A (transport! (Tm _) [id]T t))
     ∘≅
     ↓≅ (from-transp! _ [id]T refl)


 [id]t : {Γ : Con}{A : Ty Γ}{t : Tm Γ A} →
   (t [ id ]t) == t [ Tm Γ ↓ [id]T ]

 [id]t = ≅↓ (((↓≅ π₂<>∘) !≅)
     ∘≅ (↓≅ (apd π₂ idr))
     ∘≅ ↓≅ π₂<>)

 -- a version withou transport
 <>= :  ∀{Γ}{A : Ty Γ} → {t : Tm Γ A } →
   < t > ≡ (id ,s (t [ id ]t))
 <>= {Γ}{A}{t}  = ,s= refl (! (to-transp! [id]t))


 -- utile pour wk∘longWk
 wk∘^ : {Γ : Con}{Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ} → wk ∘ (σ ^ A) ≡ σ ∘ wk
 wk∘^ = wk∘,

 -- utile
 [][]T=∘ : ∀{Γ}{Δ₁}{Δ₂}{E}(A : Ty E)
    {σ₁ : Sub Γ Δ₁}{δ₁ : Sub Δ₁ E} 
    {σ₂ : Sub Γ Δ₂}{δ₂ : Sub Δ₂ E} →
   (e∘ : δ₁ ∘ σ₁ ≡ δ₂ ∘ σ₂)
   → A [ δ₁ ]T [ σ₁ ]T ≡ A [ δ₂ ]T [ σ₂ ]T
 [][]T=∘ A e∘ = [][]T ◾  ap (A [_]T) e∘ ◾ ! [][]T
 
 -- [][]T ◾  ap (A [_]T) e∘ ◾ ! [][]T
 
 -- utile pour liftV0
 vz[^] : {Γ : Con}{Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ} →
   (vz [ (σ ^ A) ]t) == vz [ Tm _ ↓ [][]T=∘ A wk∘^ ]

 vz[^] {Γ}{Δ}{A}{σ} =
   ≅↓
     (
     (vz [ (σ ^ A) ]t)

       ≅⟨  ↓≅ (vz[,] (σ ∘ π₁ id) A _) ⟩

     transport (Tm _) [][]T vz

       ≅⟨  ↓≅ (from-transp (Tm _) [][]T refl) !≅ ⟩
     vz
     ≅∎
     )

 ^∘, : {Γ : Con}{Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ}{Y : Con}
     -- {δ : Sub Y (Γ ▶ A [ σ ]T)}
     {δ : Sub Y Γ}
     {t : Tm Y (A [ σ ]T [ δ ]T)}
   → (σ ^ A) ∘ (δ ,s t) ≡ (σ ∘ δ) ,s (transport (Tm Y) [][]T t)

 ^∘, {Γ}{Δ}{A}{σ}{Y}{δ}{t} = helper (from-transp _ [][]T refl)
   where
     helper : ∀ {vz[]} vz[]e → (σ ^ A) ∘ (δ ,s t) ≡ (σ ∘ δ) ,s (transport (Tm Y) [][]T t)
     helper {vz[]} vz[]e =
       ((σ ^ A) ∘ (δ ,s t) )

           =⟨ ,∘ {ts = vz[]} vz[]e ⟩
         (((σ ∘ wk) ∘ (δ ,s t)) ,s vz[])

           =⟨ ,s= esub (≅↓ et) ⟩

         ((σ ∘ δ) ,s transport (Tm Y) [][]T t)

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

         et : vz[] ≅ transport (Tm Y) [][]T t
         et =
           vz[]

             ≅⟨ (↓≅ vz[]e) !≅ ⟩
           (transport (Tm (Γ ▶ (A [ σ ]T))) [][]T vz [ δ ,s t ]t)

               ≅⟨ (↓≅ (ap↓ (_[ δ ,s t ]t) (from-transp (Tm (Γ ▶ (A [ σ ]T))) [][]T refl))) !≅ ⟩
           (vz [ δ ,s t ]t)

           ≅⟨ ↓≅ (vz[,] _ _ _) ⟩
             t

           ≅⟨ ↓≅ (from-transp _ [][]T refl )  ⟩
             transport (Tm Y) [][]T t
           ≅∎

 ^∘<> :  ∀{Γ}{A : Ty Γ} {Y}{σ : Sub Y Γ } →{t : Tm Y (A  [ σ ]T)}  →
   -- ((σ ^ A) ∘ < t [ σ ]t >) ≡ σ ,s (t [ σ ]t)
   ((σ ^ A) ∘ < t  > ) ≡ σ ,s t

 ^∘<> = ^∘, ◾ ,s= idr (≅↓
   (((↓≅ (from-transp _ [][]T refl)) !≅)
   ∘≅ (↓≅ (from-transp! _ [id]T refl))
   ))


 [<>][]T : ∀ {Γ}{A : Ty Γ}{u : Tm Γ A}{B : Ty (Γ ▶ A)}{Y}{σ : Sub Y (Γ)} →
   ( B [ < u > ]T [ σ ]T )
   ≡ ( B [ σ ^ A ]T [ < u [ σ ]t > ]T)

 [<>][]T {Γ}{A}{u}{B}{Y}{σ} =
   [][]T=∘ B (<>∘ {A = A} ◾ ! ^∘<> )


 [][]t : {Γ Δ : Con} {Σ : Con} {A : Ty Σ} {t : Tm Σ A}{σ : Sub Γ Δ}
   {δ : Sub Δ Σ} →
   (t [ δ ]t [ σ ]t) == t [ δ ∘ σ ]t [ Tm Γ ↓ [][]T ]

 [][]t {t = t}{σ}{δ} = ≅↓
   (
   ↓≅ (from-transp _ [][]T refl)
   ∘≅ ↓≅    π₂β !≅
   ∘≅ ↓≅ ( apd π₂ e )
   ∘≅ ↓≅ π₂<>∘
   )
   where
   e : ((δ ∘ σ) ,s transport (Tm _ ) [][]T (t [ δ ]t [ σ ]t))  ≡  (< t > ∘ (δ ∘ σ))
   e =  (! (ap (_∘ σ) ( <>∘ ) ◾ ,∘ (from-transp _  [][]T refl) )) ◾ ass

 -- utile
 [][]t=∘ : ∀{Γ}{Δ₁}{Δ₂}{E}{A : Ty E}(t : Tm E A)
    {σ₁ : Sub Γ Δ₁}{δ₁ : Sub Δ₁ E} 
    {σ₂ : Sub Γ Δ₂}{δ₂ : Sub Δ₂ E} →
   (e∘ : δ₁ ∘ σ₁ ≡ δ₂ ∘ σ₂)
   → (t [ δ₁ ]t [ σ₁ ]t) == (t [ δ₂ ]t [ σ₂ ]t) [ Tm _ ↓ [][]T=∘ A e∘ ]
 -- use of UIP (could probably be avoided here)
 [][]t=∘ t e∘ = 
    ≅↓
      ((↓≅ [][]t)
      ∘≅ (↓≅ (apd (t  [_]t) e∘))
      ∘≅ ((↓≅ ([][]t)) !≅) )
 

 -- utilise [][]t
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

         ≅⟨ ↓≅ (apd (b [_]t) wk∘,) ⟩
       (b [ σ ]t)
       ≅∎





record UnivΠ {i : _}{j : _}{k : _}(M : CwF {i}{j}) : Set ((Level.suc (lmax i (lmax j k)))) where
    open CwF M
    field
      U    : ∀{Γ} → Ty Γ
      U[]  : {Γ Δ : Con} {σ : Sub Γ Δ} → _≡_ {i} {Ty Γ} (_[_]T {Γ} {Δ} (U {Δ}) σ) (U {Γ})


      El   : ∀{Γ}(a : Tm Γ U) → Ty Γ

      El[] :
        {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} →
        _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (El {Δ} a) σ)
        (El {Γ}
        (coe {_} {Tm Γ (_[_]T {Γ} {Δ} (U {Δ}) σ)} {Tm Γ (U {Γ})}
        (ap {_} {suc _} {Ty Γ} {_} (Tm Γ)
        {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}))
        (_[_]t {Γ} {Δ} {U {Δ}} a σ)))

      Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ
      Π[] :
        {Γ Δ : Con} {σ : Sub Γ Δ} {a : Tm Δ (U {Δ})} {B : Ty (Δ ▶ El {Δ} a)} →
        _≡_ {_} {Ty Γ} (_[_]T {Γ} {Δ} (Π {Δ} a B) σ) (Π {Γ} (transport {_}
        {_} {Ty Γ} (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ}
        {σ}) (_[_]t {Γ} {Δ} {U {Δ}} a σ)) (transport {_} {_} {Ty Γ} (λ x → Ty
        (Γ ▶ x)) {_[_]T {Γ} {Δ} (El {Δ} a) σ} {El {Γ} (transport {_} {_} {Ty Γ}
        (Tm Γ) {_[_]T {Γ} {Δ} (U {Δ}) σ} {U {Γ}} (U[] {Γ} {Δ} {σ}) (_[_]t {Γ}
        {Δ} {U {Δ}} a σ))} (El[] {Γ} {Δ} {σ} {a}) (_[_]T {Γ ▶ _[_]T {Γ} {Δ}
        (El {Δ} a) σ} {Δ ▶ El {Δ} a} B (_^_ {Γ} {Δ} σ (El {Δ} a)))))

      _$_ : ∀ {Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}(t : Tm Γ (Π a B))(u : Tm Γ (El a)) → Tm Γ (B [ < u > ]T)
      $[] :
        ∀ {Y}{Γ}{σ : Sub Y Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)}{t : Tm Γ (Π a B)}{u : Tm Γ (El a)}
        → ((t $ u) [ σ ]t) == (transport (Tm _) Π[] (t [ σ ]t)) $ transport (Tm _) El[] (u [ σ ]t)
        -- ∙' rather than ◾ so that it computes when the second is refl
          [ Tm _ ↓ [<>][]T {Γ}{El a}{u}{B} ∙'
             J (λ el[] eq →
                (B [ σ ^ El a ]T [ < u [ σ ]t > ]T)
                ≡
                (transport (λ x → Ty (Y ▶ x)) eq (B [ σ ^ El a ]T) [
                  < transport (Tm Y) eq (u [ σ ]t) > ]T) )
                  refl
                  El[]
                 ]

      ΠNI : ∀{Γ}{T : Set k}(B : T → Ty Γ) → Ty Γ
      ΠNI[] : {Γ Δ : Con} {σ : Sub Γ Δ} {T : Set k} {B : T → Ty Δ} →
        (ΠNI {Δ} B) [ σ ]T ≡ (ΠNI {Γ} {T} λ a → B a [ σ ]T)

      _$NI_ : ∀ {Γ}{T : Set k}{B : T → Ty Γ}(t : Tm Γ (ΠNI B))(u : T) → Tm Γ (B u)
      $NI[] :
        ∀ {Y}{Γ}{σ : Sub Y Γ}{T : Set k}{B : T → Ty Γ}{t : Tm Γ (ΠNI B)}{u : T}
        → ((t $NI u) [ σ ]t) ≡ (  (transport (Tm _) ΠNI[] (t [ σ ]t)) $NI u )

      ΠInf : ∀{Γ}{T : Set k}(B : T → Tm Γ U) → Tm Γ U
      ΠInf[] : {Γ Δ : Con} {σ : Sub Γ Δ} {T : Set k} {B : T → Tm Δ U} →
        (((ΠInf {Δ} B) [ σ ]t) == (ΠInf {Γ} {T} (λ a → transport (Tm _) U[] ((B a) [ σ ]t))) [ Tm _ ↓ U[] ])

      _$Inf_ : ∀ {Γ}{T : Set k}{B : T → Tm Γ U}(t : Tm Γ (El (ΠInf B)))(u : T) → Tm Γ (El (B u))
      $Inf[] :
        ∀ {Y}{Γ}{σ : Sub Y Γ}{T : Set k}{B : T → Tm Γ U}{t : Tm Γ (El (ΠInf B))}{u : T}
        → ((t $Inf u) [ σ ]t) ==
             transport (Tm Y) (El[] ◾ ap El (to-transp ΠInf[])) (t [ σ ]t)
             $Inf u [ Tm _ ↓ El[] ]



module CwFUnivΠ {i}{j}{k}{c : CwF {i}{j}}(cov : UnivΠ {k = k} c) where
  open CwF c public
  open UnivΠ cov public
