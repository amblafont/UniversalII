{-# OPTIONS --rewriting   #-}
-- --overlapping-instances
-- an attempt with rewrite rules, but by postulating the model rather than defining a record (because rewrite rules don't work)
-- in this file: definition of the functional relation, and proof that the relation is indeed functional

-- open import HoTT.Base
open import Level
open import Hott renaming ( _∙_ to _◾_ ;  transport to tr ; fst to ₁ ; snd to ₂)
open import Data.Nat renaming (suc to S)
open import monlib
module RelationCwf {k : Level.Level}  where

  open import Syntax {k} as S
  import ModelCwf {k}  as M


  -- module M = Model {α}

-- infixl 5 _^^_
  -- _^^_ : Conp → Conp → Conp
  -- Γ ^^ Δ = Γ Syntax.^^ Δ

  -- Logical relation between the presyntax and the M model expressing
  -- that presyntactic and semantic values have the same structure
  -- in these versions, we assume for Ty~' that Γm is already realted to Γw
  -- and the same for Tm~'  and Var~' (although Var~' enforces that Γm is related to Γw)
  -- the advantage : I won't need to show that Ty~' implies Con~'
  -- However I would still need to prove that _w are HProp (consider you would state
  --   the main theorem for Ty~' and the case of context extension)
  Con~ : {Γp : Conp}(Γw :  Γp ⊢) → M.Con → Set (lmax M.i (lmax M.j k))
  Ty~ : ∀ {Γ A} (Aw : Γ ⊢ A) {Γm} (Am : M.Ty Γm) → Set (lmax M.i (lmax M.j k))
  Tm~ : ∀ {Γ A t} (tw : Γ ⊢  t ∈ A) {Γm} {Am : M.Ty Γm}(tm : M.Tm Γm Am) → Set (lmax M.i (lmax M.j k))
  Var~ : ∀ {Γ A x} (xw : Γ ⊢  x ∈v A) {Γm} {Am : M.Ty Γm}(tm : M.Tm Γm Am) → Set (lmax M.i (lmax M.j k))

-- Con~ {Γ}Γw Γm = {!!}
-- Sub~ {Γ}{Δ}{σ}σw {Γm}{Δm}σm = {!!}
  Con~ {.∙p} ∙w Γm =
    Lift { ℓ = lmax M.j k} (Γm ≡ M.∙)
    -- HoTT.Lift { j = M.j} (Γm ≡ M.∙)
  Con~ {.(_ ▶p _)} (▶w Γw Aw) Δm =
    Σ (∃ (Con~ Γw)) λ Γm →
    Σ (∃ (Ty~ Aw {₁ Γm})) λ Am →
    Δm ≡ (₁ Γm M.▶ ₁ Am )

-- Ty~ {Γ}{E} Ew {Cm} Em = {!Ew!}
  Ty~   (Uw  Γw) {Cm} Em = Lift {ℓ = lmax M.j k} (Em ≡ M.U )
  Ty~ {Γ} {.(ΠΠp ( _) _)} (Πw Γw Aw Bw) {Cm} Em =
    Σ (∃ (Tm~ Aw {Cm} {M.U})) λ am →
    Σ (∃ (Ty~ Bw {Cm M.▶ M.El (₁ am)} )) λ Bm →
      Em ≡ M.Π (₁ am) (₁ Bm)
  Ty~ {Γ}  (ΠNIw Γw {T}{Bp} Bw) {Cm} Em =
    Σ (∀ a → ∃ (Ty~ (Bw a) {Cm} )) λ Bm →
      Em ≡ M.ΠNI  (λ a → ₁ (Bm a) )

  Ty~ {Γ} {.(Elp _)} (Elw Γw aw) {Cm} Em =
    Σ (∃ (Tm~ aw {Cm} {M.U})) λ am →
      -- HoTT.Lift (Em ≡ M.El (₁ am))
      (Em ≡ M.El (₁ am))


  Tm~ {Γ} {E} {.(V _)} (vw xw) {Cm} {Em} zm = (Var~ xw zm)
  Tm~    (appw Γw aw Bw tw uw) {Δm} {Em} zm =
    Σ (∃ (Tm~ aw {Δm} {M.U })) λ am →
    Σ (∃ (Ty~ Bw {Δm M.▶ M.El (₁ am)})) λ Bm →

    Σ (∃ (Tm~ tw {Δm} {M.Π (₁ am) (₁ Bm)})) λ tm →
    Σ (∃ (Tm~ uw {Δm} {M.El  (₁ am)})) λ um →
    Σ (Em ≡ (₁ Bm M.[ M.< ₁ um > ]T) ) λ eC →
      zm == (₁ tm) M.$ (₁ um) [ M.Tm Δm ↓ eC ]
  Tm~   {t = appNI t u} (appNIw Γw {T} {Bp} Bw tw u) {Δm} {Em} zm =

    Σ (∀ a → ∃ (Ty~ (Bw a) {Δm} )) λ Bm →
    Σ (∃ (Tm~ tw {Δm} {M.ΠNI  (λ a → ₁ (Bm a))})) λ tm →
    Σ (Em ≡ (₁ (Bm u)) ) λ eC →
      zm == (₁ tm) M.$NI u [ M.Tm Δm ↓ eC ]
  Tm~   {t = appNI t u} (appInfw Γw {T} {Bp} Bw tw u) {Δm} {Em} zm =

    Σ (∀ a → ∃ (Tm~ (Bw a) {Δm} )) λ Bm →
    Σ (∃ (Tm~ tw {Δm} {M.El (M.ΠInf  (λ a → ₁ (Bm a)))})) λ tm →
    Σ (Em ≡ M.El (₁ (Bm u)) ) λ eC →
    zm == (₁ tm) M.$Inf u [ M.Tm Δm ↓ eC ]

  Tm~ {Γ} (ΠInfw Γw {T}{Bp} Bw) {Cm} {Em} zm =
     Σ (∀ a → ∃ (Tm~ (Bw a) {Cm} )) λ Bm →
      Σ (Em ≡ M.U) λ eE →
      zm == M.ΠInf  (λ a → ₁ (Bm a) ) [ M.Tm _ ↓ eE ]


-- Var~ {Γ}{E}{x} xw {Cm}{Em} xm = {!Ew!}
  Var~    (V0w Γw Aw) {Cm} {Em} xm =

     Σ (∃ (Con~ Γw )) λ Γm →
     Σ (∃ (Ty~  Aw {₁ Γm} )) λ Am →
     Σ (Cm ≡ (₁ Γm M.▶ ₁ Am)) λ eC →
     Σ (Em == ₁ Am M.[ M.wk ]T [ M.Ty ↓ eC ]) λ eE →
      xm == M.vz [ (λ CE → M.Tm (₁ CE)(₂ CE)) ↓ pair= eC eE ]

  Var~  (VSw Γw Aw Bw xw) {Cm} {Em} zm =
    Σ (∃ (Con~ Γw )) λ Γm →
    Σ (∃ (Ty~  Aw {₁ Γm} )) λ Am →
    Σ (∃ (Ty~  Bw {₁ Γm} )) λ Bm →
    Σ (∃ (Var~ xw {₁ Γm}{₁ Bm})) λ xm →
    Σ (Cm ≡ (₁ Γm M.▶ ₁ Am)) λ eC →
    Σ (Em == ₁ Bm M.[ M.wk ]T [ M.Ty ↓ eC ]) λ eE →

    zm == M.vs (₁ xm) [ (λ CE → M.Tm (₁ CE)(₂ CE)) ↓ pair= eC eE ]


    -- λ um → (Cm , zm) ≡ M.subT Δm (M.El Δm (₁ am)) (₁ um) (₁ Bm) ,
    -- M.app Δm (₁ am) (₁ Bm) (₁ tm) (₁ um)


  Sub~ : ∀ {Γ Δ σ} (σw :  Γ ⊢ σ ⇒ Δ) {Γm Δm} (σm : M.Sub Γm Δm) → Set (lmax M.i (lmax M.j k))
  -- Sub~ {Γ} {.∙p} {.nil} nilw {Γm} {Δm} σm = {!(Δm , σm) ≡ (M.∙ , M.ε )!}
  Sub~ {Γ} {.∙p} {.nil} nilw {Γm} {Δm} σm =
    Σ (Δm ≡ M.∙ ) λ eC → Lift {ℓ  = k} (σm == M.ε [ M.Sub Γm ↓ eC ])
  -- _,_ {A = M.Con}{ M.Sub Γm} Δm σm ≡ (M.∙ , M.ε )
  Sub~ {Γ} {.(_ ▶p _)}  (,sw Δw σw Aw tw) {Γm} {Cm} sm =
    Σ (∃ (Con~ Δw)) λ Δm →
    Σ (∃ (Sub~ σw {Γm} {₁ Δm})) λ σm →
    Σ (∃ (Ty~ Aw {₁ Δm})) λ Am →
    Σ (∃ (Tm~ tw { Γm } {Am = ₁ Am M.[ ₁ σm ]T})) λ tm →
      Σ (Cm ≡ (₁ Δm M.▶ ₁ Am)) λ eC →
      sm == ₁ σm M.,s ₁ tm [ M.Sub Γm ↓ eC ]

  ConP : ∀ {Γp} Γw → is-prop (∃ (Con~ {Γp} Γw))
  TyP : ∀ {Γ A} (Aw : Γ ⊢ A) Γm → is-prop (∃ (Ty~ Aw {Γm}))
  TmP : ∀ {Γ A t} (tw : Γ ⊢  t ∈ A) {Γm} (Am : M.Ty Γm) → is-prop (∃ (Tm~ tw {Γm}{Am}))
  VarP : ∀ {Γ A x} (x : Γ ⊢  x ∈v A) {Γm} (Am : M.Ty Γm) → is-prop (∃ (Var~ x {Γm}{Am}))

  -- new version of Agda does not support explicit arguments for instances
  instance
    i-ConP : ∀ {Γp} {Γw} → is-prop (∃ (Con~ {Γp} Γw))
    i-TyP : ∀ {Γ A} {Aw : Γ ⊢ A} {Γm} → is-prop (∃ (Ty~ Aw {Γm}))
    i-TmP : ∀ {Γ A t} {tw : Γ ⊢  t ∈ A} {Γm} {Am : M.Ty Γm} → is-prop (∃ (Tm~ tw {Γm}{Am}))
    i-VarP : ∀ {Γ A x} {x : Γ ⊢  x ∈v A} {Γm} {Am : M.Ty Γm} → is-prop (∃ (Var~ x {Γm}{Am}))

    i-ConP {Γw = Γw} = ConP Γw
    i-TyP {Aw = Aw}{Γm = Γm} = TyP Aw Γm
    i-TmP {tw = tw}{Am = Am} = TmP tw Am
    i-VarP {Am = Am} = VarP _ Am
  -- Var~ : ∀ {Γ A x} (xw : Varw Γ A x) {Γm} {Am : M.Ty Γm}(tm : M.Tm Γm Am) → Set (lmax M.i M.j)

    ConP {.∙p} ∙w =  Lift-pathto-is-prop M.∙
    ConP {.(_ ▶p _)} (▶w Cw Aw) =
     equiv-preserves-level
      (Σ₁-×-comm   ∘e
      Σ-emap-r λ Γm → Σ₁-×-comm)
      {{ Σ-level (ConP Cw)
              (λ x →
                  Σ-level (TyP Aw (₁ x)) (λ x₁ → pathto-is-prop (₁ x M.▶ ₁ x₁)))

        }}

-- TyP {Γ}{ A} Aw Γm = {!!}
    TyP (Uw Γw) Γm = Lift-pathto-is-prop M.U
    TyP {Γ} {.(ΠΠp ( _) _)} (Πw Γw Aw Bw) Γm =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Am' →
      Σ₁-×-comm
      )
      {{ Σ-level (TmP Aw {Γm} M.U) λ Am' →
           Σ-level (TyP Bw (Γm M.▶ M.El (₁ Am')))
               (λ x → pathto-is-prop (M.Π (₁ Am') (₁ x)))

         }}
    TyP {Γ}  (ΠNIw Γw {T}{Bp} Bw) Γm =

      equiv-preserves-level
      (
      Σ₁-×-comm
      -- ∘e Σ-emap-r λ Am' → {!!}
      )
      -- This needs funext actually
      {{  Σ-level (Π-level (λ a →  TyP (Bw a) Γm )) λ Am' →  pathto-is-prop (M.ΠNI (λ a → ₁ (Am' a)))  }}

      -- Σ-emap-r λ Am' →
      -- ?

    TyP {Γ} {.(Elp _)} (Elw Γw aw) Γm =

      equiv-preserves-level Σ₁-×-comm
      {{ Σ-level (TmP aw {Γm} M.U) λ Am' →  pathto-is-prop (M.El (₁ Am'))  }}


    TmP {Γ} {A} {.(V _)} (vw xw) {Γm} Am = VarP xw Am
    TmP  (appw Γw aw Bw tw uw) {Γm} Am =

      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Am' →
      Σ₁-×-comm ∘e Σ-emap-r λ Bm' →
      Σ₁-×-comm ∘e Σ-emap-r λ tm' →
      Σ₁-×-comm ∘e Σ-emap-r λ um' →
      Σ₁-×-comm
      )
      {{  Σ-level (TmP aw {Γm} M.U) λ Am' →
          Σ-level (TyP Bw _) λ Bm' →
          Σ-level (TmP tw _) λ tm' →
          Σ-level (TmP uw _) λ um' →
          Σ-level (all-paths-is-prop uip ) λ eC' → pathOverto-is-prop (M.Tm Γm) eC' _
          -- raise-level ⟨-2⟩ {!!}
          }}
    TmP   {t = appNI t u} (appNIw Γw {T}{Bp} Bw tw u) {Γm} Am =


       equiv-preserves-level
       (
      Σ₁-×-comm ∘e Σ-emap-r λ Am' →
      Σ₁-×-comm ∘e Σ-emap-r λ Bm' →
      Σ₁-×-comm
       )
       {{ Σ-level (Π-level (λ a →  TyP (Bw a) Γm )) λ Bm' →

          Σ-level (TmP tw _) λ tm' →
          Σ-level (all-paths-is-prop uip ) λ eC' →
          pathOverto-is-prop (M.Tm Γm) eC' _

        }}
    TmP   {t = appNI t u} (appInfw Γw {T}{Bp} Bw tw u) {Γm} Am =

       equiv-preserves-level
       (
      Σ₁-×-comm ∘e Σ-emap-r λ Am' →
      Σ₁-×-comm ∘e Σ-emap-r λ Bm' →
      Σ₁-×-comm
       )
       {{ Σ-level (Π-level (λ a → TmP (Bw a) M.U)) λ Bm' →

          Σ-level (TmP tw _) λ tm' →
          Σ-level (all-paths-is-prop uip ) λ eC' →
          pathOverto-is-prop (M.Tm Γm) eC' _

        }}
    TmP {Γ}  (ΠInfw Γw {T}{Bp} Bw) {Γm} Am =
      equiv-preserves-level
       (
          Σ₁-×-comm ∘e Σ-emap-r λ Am' →
          Σ₁-×-comm
       )
      -- This needs funext actually
       {{ Σ-level (Π-level (λ a → TmP (Bw a) _)) λ Bm' →
            Σ-level ( all-paths-is-prop uip ) λ eT →
             pathOverto-is-prop (M.Tm Γm) eT _ }}

    VarP (V0w Γw Aw) {Γm} Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
      Σ₁-×-comm ∘e Σ-emap-r λ eC →
      Σ₁-×-comm
      )
      {{ Σ-level ( ConP Γw ) λ Γm' →
        Σ-level  (TyP Aw (₁ Γm'))  λ Am' →
        Σ-level ( all-paths-is-prop uip ) λ eC' →
        Σ-level (uip-over-prop _ _ _ _) λ eE' →
        pathOverto-is-prop _ _ _
       }}

    VarP (VSw Γw Aw Bw xw) {Γm} Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
      Σ₁-×-comm ∘e Σ-emap-r λ Bm →
      Σ₁-×-comm ∘e Σ-emap-r λ xm →
      Σ₁-×-comm ∘e Σ-emap-r λ eC →
      Σ₁-×-comm

      )
      {{ Σ-level (ConP Γw ) λ Γm' →
          Σ-level  (TyP Aw (₁ Γm'))  λ Am' →
          Σ-level  (TyP Bw _)  λ Bm' →
          Σ-level  (VarP xw _)  λ xm' →
          Σ-level (all-paths-is-prop uip) λ eC' →
          Σ-level (uip-over-prop _ _ _ _) λ eE' →
          pathOverto-is-prop _ _ _
       }}


  SubP : ∀ {Γ Δ s} (sw :  Γ ⊢ s ⇒ Δ) Γm Δm → is-prop (∃ (Sub~ sw {Γm}{Δm}))

  instance
    i-SubP : ∀ {Γ Δ s} {sw :  Γ ⊢ s ⇒ Δ} {Γm} {Δm} → is-prop (∃ (Sub~ sw {Γm}{Δm}))
    i-SubP {sw = sw}{Γm = Γm}{Δm = Δm} = SubP sw Γm Δm

  -- SubP {Γ}{Δ}{s}sw Γm Δm = {!sw!}
  SubP {Γ} {.∙p} {.nil} nilw Γm Δm =

    equiv-preserves-level
    Σ₁-×-comm

    {{ Σ-level (all-paths-is-prop uip) λ eC' →
      Lift-pathOverto-is-prop _ eC' M.ε
      }}

  SubP {Γ} {.(_ ▶p _)}  (,sw Δw sw Aw tw) Γm Δm =

    equiv-preserves-level
    (
    Σ₁-×-comm ∘e Σ-emap-r λ Δm' →
    Σ₁-×-comm ∘e Σ-emap-r λ σm' →
    Σ₁-×-comm ∘e Σ-emap-r λ Am' →
    Σ₁-×-comm ∘e Σ-emap-r λ tm' →
    Σ₁-×-comm
    )
      {{ Σ-level (ConP Δw ) λ Δm' →
        Σ-level ( SubP sw Γm (₁ Δm') ) λ σm' →
        Σ-level ( TyP Aw (₁ Δm') ) λ Am' →
        Σ-level (TmP tw (₁ Am' M.[ ₁ σm' ]T)) λ tm' →
        Σ-level ( all-paths-is-prop uip ) λ eC' →
        pathOverto-is-prop _ _ _
      }}


  -- heterogeneous
  ConPh : ∀ {Γp} {Γw} {Γw'} (Γm : ∃ (Con~ {Γp} Γw))(Γm' : ∃ (Con~ {Γp} Γw'))
    → ₁ Γm ≡ ₁ Γm'

  ConPh {Γ}{Γw}{Γw'} Γm Γm' rewrite prop-has-all-paths Γw Γw' |
    prop-path (ConP Γw') Γm Γm' = refl


  -- some helper
  Σ▶~ : ∀ {Γ}{Γw : Γ ⊢} (Γm : ∃ (Con~ Γw))
    {A}{Aw : Γ ⊢ A}(Am : ∃ (Ty~ Aw {₁ Γm}))
    → ∃ (Con~ (▶w Γw Aw))
  Σ▶~ Γm Am = _ , Γm , Am , refl
