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
  Con~ : {Γp : Conp}(Γw : Conw Γp) → M.Con → Set (lmax M.i (lmax M.j k))
  Ty~ : ∀ {Γ A} (Aw : Tyw Γ A) {Γm} (Am : M.Ty Γm) → Set (lmax M.i (lmax M.j k))
  Tm~ : ∀ {Γ A t} (tw : Tmw Γ A t) {Γm} {Am : M.Ty Γm}(tm : M.Tm Γm Am) → Set (lmax M.i (lmax M.j k))
  Var~ : ∀ {Γ A x} (xw : Varw Γ A x) {Γm} {Am : M.Ty Γm}(tm : M.Tm Γm Am) → Set (lmax M.i (lmax M.j k))

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
  Ty~ {.Γp} {.Up} (Uw Γp Γw) {Cm} Em = Lift {ℓ = lmax M.j k} (Em ≡ M.U )
  Ty~ {Γ} {.(ΠΠp (Elp _) _)} (Πw Γw Aw Bw) {Cm} Em =
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
  Tm~ {.Γp} {.(l-subT 0 u Bp)} {.(app t u)} (appw Γp Γw ap aw Bp Bw t tw u uw) {Δm} {Em} zm =
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
  Var~ {.(Γp ▶p Ap)} {.(liftT 0 Ap)} {.0} (V0w Γp Γw Ap Aw) {Cm} {Em} xm =

     Σ (∃ (Con~ Γw )) λ Γm →
     Σ (∃ (Ty~  Aw {₁ Γm} )) λ Am →
     Σ (Cm ≡ (₁ Γm M.▶ ₁ Am)) λ eC →
     Σ (Em == ₁ Am M.[ M.wk ]T [ M.Ty ↓ eC ]) λ eE →
      xm == M.vz [ (λ CE → M.Tm (₁ CE)(₂ CE)) ↓ pair= eC eE ]

  Var~ {.(Γp ▶p Ap)} {.(liftT 0 Bp)} {.(S xp)} (VSw Γp Γw Ap Aw Bp Bw xp xw) {Cm} {Em} zm =
    Σ (∃ (Con~ Γw )) λ Γm →
    Σ (∃ (Ty~  Aw {₁ Γm} )) λ Am →
    Σ (∃ (Ty~  Bw {₁ Γm} )) λ Bm →
    Σ (∃ (Var~ xw {₁ Γm}{₁ Bm})) λ xm →
    Σ (Cm ≡ (₁ Γm M.▶ ₁ Am)) λ eC →
    Σ (Em == ₁ Bm M.[ M.wk ]T [ M.Ty ↓ eC ]) λ eE →

    zm == M.vs (₁ xm) [ (λ CE → M.Tm (₁ CE)(₂ CE)) ↓ pair= eC eE ]


    -- λ um → (Cm , zm) ≡ M.subT Δm (M.El Δm (₁ am)) (₁ um) (₁ Bm) ,
    -- M.app Δm (₁ am) (₁ Bm) (₁ tm) (₁ um)


  Sub~ : ∀ {Γ Δ σ} (σw : Subw Γ Δ σ) {Γm Δm} (σm : M.Sub Γm Δm) → Set (lmax M.i (lmax M.j k))
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
  TyP : ∀ {Γ A} (Aw : Tyw Γ A) Γm → is-prop (∃ (Ty~ Aw {Γm}))
  TmP : ∀ {Γ A t} (tw : Tmw Γ A t) {Γm} (Am : M.Ty Γm) → is-prop (∃ (Tm~ tw {Γm}{Am}))
  VarP : ∀ {Γ A x} (x : Varw Γ A x) {Γm} (Am : M.Ty Γm) → is-prop (∃ (Var~ x {Γm}{Am}))

  -- new version of Agda does not support explicit arguments for instances
  instance
    i-ConP : ∀ {Γp} {Γw} → is-prop (∃ (Con~ {Γp} Γw))
    i-TyP : ∀ {Γ A} {Aw : Tyw Γ A} {Γm} → is-prop (∃ (Ty~ Aw {Γm}))
    i-TmP : ∀ {Γ A t} {tw : Tmw Γ A t} {Γm} {Am : M.Ty Γm} → is-prop (∃ (Tm~ tw {Γm}{Am}))
    i-VarP : ∀ {Γ A x} {x : Varw Γ A x} {Γm} {Am : M.Ty Γm} → is-prop (∃ (Var~ x {Γm}{Am}))

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
      {{  
        Σ-level (ConP Cw)
              (λ x →
                  Σ-level (TyP Aw (₁ x)) (λ x₁ → pathto-is-prop (₁ x M.▶ ₁ x₁)))

        }}

-- TyP {Γ}{ A} Aw Γm = {!!}
    TyP {.Γp} {.Up} (Uw Γp Γw) Γm = Lift-pathto-is-prop M.U
    TyP {Γ} {.(ΠΠp (Elp _) _)} (Πw Γw Aw Bw) Γm =
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
    TmP {.Γp} {.(l-subT 0 u Bp)} {.(app t u)} (appw Γp Γw ap aw Bp Bw t tw u uw) {Γm} Am =

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

    VarP {.(Γp ▶p Ap)} {.(liftT 0 Ap)} {.0} (V0w Γp Γw Ap Aw) {Γm} Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
      Σ₁-×-comm ∘e Σ-emap-r λ eC →
      Σ₁-×-comm
      )
      {{ 
        Σ-level ( ConP Γw ) λ Γm' →
        Σ-level  (TyP Aw (₁ Γm'))  λ Am' →
        Σ-level ( all-paths-is-prop uip ) λ eC' →
        Σ-level (uip-over-prop _ _ _ _) λ eE' →
        pathOverto-is-prop _ _ _
       }}

    VarP {.(Γp ▶p Ap)} {.(liftT 0 Bp)} {.(S xp)} (VSw Γp Γw Ap Aw Bp Bw xp xw) {Γm} Am =
      equiv-preserves-level
      (
      Σ₁-×-comm ∘e Σ-emap-r λ Γm →
      Σ₁-×-comm ∘e Σ-emap-r λ Am →
      Σ₁-×-comm ∘e Σ-emap-r λ Bm →
      Σ₁-×-comm ∘e Σ-emap-r λ xm →
      Σ₁-×-comm ∘e Σ-emap-r λ eC →
      Σ₁-×-comm

      )
      {{ 
         Σ-level (ConP Γw ) λ Γm' →
          Σ-level  (TyP Aw (₁ Γm'))  λ Am' →
          Σ-level  (TyP Bw _)  λ Bm' →
          Σ-level  (VarP xw _)  λ xm' →
          Σ-level (all-paths-is-prop uip) λ eC' →
          Σ-level (uip-over-prop _ _ _ _) λ eE' →
          pathOverto-is-prop _ _ _
       }}


  SubP : ∀ {Γ Δ s} (sw : Subw Γ Δ s) Γm Δm → is-prop (∃ (Sub~ sw {Γm}{Δm}))

  instance
    i-SubP : ∀ {Γ Δ s} {sw : Subw Γ Δ s} {Γm} {Δm} → is-prop (∃ (Sub~ sw {Γm}{Δm}))
    i-SubP {sw = sw}{Γm = Γm}{Δm = Δm} = SubP sw Γm Δm

  -- SubP {Γ}{Δ}{s}sw Γm Δm = {!sw!}
  SubP {Γ} {.∙p} {.nil} nilw Γm Δm =

    equiv-preserves-level
    Σ₁-×-comm

    {{ 
    Σ-level (all-paths-is-prop uip) λ eC' →
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
      {{ 
        Σ-level (ConP Δw ) λ Δm' →
        Σ-level ( SubP sw Γm (₁ Δm') ) λ σm' →
        Σ-level ( TyP Aw (₁ Δm') ) λ Am' →
        Σ-level (TmP tw (₁ Am' M.[ ₁ σm' ]T)) λ tm' →
        Σ-level ( all-paths-is-prop uip ) λ eC' →
        pathOverto-is-prop _ _ _


      }}




  -- Ty~  : {Γp : Conp}{Ap : Typ}(Aw : Tyw Γp Ap) (Δm : M.Con) (Cm : M.Ty Δm)  → Set α
  -- Tm~ : {Γp : Conp}{Ap : Typ}(tp : Tmp)(tw : Tmw Γp Ap tp)(Δm : M.Con)(Cm : M.Ty Δm)(zm : M.Tm _ Cm)  → Set α
  -- Var~  : (Γp : Conp)(Ap : Typ)(xp : ℕ)(xw : Varw Γp Ap xp)(Δm : M.Con)(Cm : M.Ty Δm)(zm : M.Tm _ Cm)  → Set α
  -- Sub~ : ∀ {Γp}Δp (Δw : Conw (Γp ^^ Δp)) (Γm : M.Con)(Δm : M.Telescope Γm) → Set α

{-

  Telescope~ ∙p Δw Γm Δm = Δm ≡ M.∙t Γm
  Telescope~ (Δp ▶p A) (▶w Δw Aw) Γm Em =
    Σ (Σ _ (Telescope~ Δp Δw Γm)) λ Δm →
    Σ (Σ _ (Ty~' _ A Aw (Γm M.^^ (₁ Δm)))) λ Am →
    Em ≡ (₁ Δm M.▶t ₁ Am)


  Con~' .∙p ∙w Γm = Γm ≡ M.∙
  Con~' .(Γp ▶p Ap) (▶w {Γp} Γw {Ap} Aw) Δm =
    Σ (Σ _ (Con~' _ Γw))
    λ Γm → Σ (Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    λ Am → Δm ≡ (₁ Γm M.▶ ₁ Am )

  Ty~' Γp .Up (Uw .Γp Γw) Δm Cm = Cm ≡ M.U Δm
  Ty~' Γp .(ΠΠp (Elp ap) Bp) (Πw  Γw {ap} Aw {Bp} Bw) Δm Cm =
    Σ (Σ _ (Tm~' _ _ ap Aw Δm (M.U Δm) ))
    λ am → Σ (Σ _ (Ty~' _ Bp Bw (Δm M.▶ M.El Δm  (₁ am))))
    λ Bm → Cm ≡ M.ΠΠ Δm _ (₁ Bm)
  Ty~' Γp _ (Elw Γw aw) Δm Cm =
    Σ (Σ _ (Tm~' _ _ _ aw Δm (M.U Δm) ))
    λ am → Cm ≡ M.El _ (₁ am)

  Tm~' Γp Ap .(V _) (vw xw) Δm Cm zm = Var~' _ _ _ xw Δm Cm zm
  Tm~' Γp .(l-subT 0 u Bp) .(app t u) (appw .Γp Γw ap aw Bp Bw t tw u uw) Δm Cm zm =
    Σ (Σ _ (Tm~' _ _ ap aw Δm (M.U Δm)))
    λ am → Σ (Σ _ (Ty~' _ Bp Bw (Δm M.▶ M.El Δm  (₁ am))))
    λ Bm → Σ (Σ _ (Tm~' _ _ t tw Δm (M.ΠΠ Δm _ (₁ Bm))))
    λ tm → Σ (Σ _ (Tm~' _ _ u uw Δm (M.El Δm (₁ am))))
    λ um → (Cm , zm) ≡ M.subT Δm (M.El Δm (₁ am)) (₁ um) (₁ Bm) ,
    M.app Δm (₁ am) (₁ Bm) (₁ tm) (₁ um)

  Var~' .(Γp ▶p Ap) .(liftT 0 Ap) .0 (V0w Γp Γw Ap Aw) Δm Cm zm =
    Σ (Σ _ (Con~' Γp Γw ))
    λ Γm → Σ (Σ _ (Ty~' _ Ap Aw (₁ Γm) ))
    λ Am →
    -- this left associative stuff makes {! it !} easier to inhbabite thanks to pair=
    _,_  {A = Σ _ M.Ty}{B = λ x → M.Tm (₁ x)(₂ x)}
    (Δm , Cm) zm ≡
    (((₁ Γm M.▶ ₁ Am)  , _ ) , ( M.V0 (₁ Γm) (₁ Am)))
  -- _,_ {B = λ Γm → Σ (M.Ty Γm) λ Am → M.Tm Γm Am}
  --  Δm (Cm , zm) ≡
  -- (₁ Γm M.▶ ₁ Am)  , _ , M.V0 (₁ Γm) (₁ Am)

  -- Var~' .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Δm Cm zm = {!!}
  Var~' .(Γp ▶p Ap) .(liftT 0 Bp) .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Δm Cm zm =
    Σ (Σ _ (Con~' Γp Γw ))
    λ Γm → Σ (Σ _ (Ty~' _ Ap Aw (₁ Γm) ))
    λ Am → Σ (Σ _ (Ty~' _ Bp Bw (₁ Γm) ))
    λ Bm → Σ (Σ _ (Var~' _ _ _ xw (₁ Γm) (₁ Bm) ))
    λ xm →
    -- this left associative stuff makes {! it !} easier to inhbabite thanks to pair=
    _,_  {A = Σ _ M.Ty}{B = λ x → M.Tm (₁ x)(₂ x)}
    (Δm , Cm) zm ≡
    (((₁ Γm M.▶ ₁ Am)  , _ ) , ( M.wkt _ _ _ (₁ xm)))
    -- _,_ {B = λ Γm → Σ (M.Ty Γm) λ Am → M.Tm Γm Am}
    -- Δm (Cm , zm) ≡
    -- (₁ Γm M.▶ ₁ Am)  , _ , M.wkt _ _ _ (₁ xm)

  mkΣTm : (Γm : M.Con)(A : M.Ty Γm)(t : M.Tm Γm A) → Σ (Σ _ M.Ty) λ x → M.Tm (₁ x)(₂ x)
  mkΣTm Γ A t = ((Γ , A) , t)

  -- todo: utiliser ces lemmes avant, par exemple dans v1
  -- todo : reformuler en utilisant des rewrites
  trVar~' : {Γp : Conp}{Ap : Typ}{xp : ℕ}(xw : Varw Γp Ap xp)
    (xw' : Varw Γp Ap xp)
    {Δm : M.Con}{Cm : M.Ty Δm}(zm : M.Tm _ Cm)  → Var~' _ _ _ xw _ _ zm → Var~' _ _ _ xw' _ _ zm
  trVar~' xw xw' zm = tr (λ xw → Var~' _ _ _ xw _ _ zm) (prop-path (VarwP _ _ _) xw xw')

  trCon~' : {Γp : Conp}(Γw : Conw Γp)(Γw' : Conw Γp)
    (Γm : M.Con) → Con~' _ Γw Γm → Con~' _ Γw' Γm
  trCon~' Γw Γw' Γm = tr (λ Γw → Con~' _ Γw Γm) (prop-path (ConwP _) Γw Γw')

  ^^~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
          {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) )) →
          Con~' _ Δw ((₁ Γm) M.^^ (₁ Δm))

  ^^~ Γw Γm {∙p} Δw Δm rewrite (₂ Δm) = trCon~' Γw Δw _ (₂ Γm)

  ^^~ Γw Γm {Δp ▶p Ap} (▶w Δw Aw) (.(₁ Δm M.▶t ₁ Am) , Δm , Am , refl) =
    (((₁ Γm M.^^ ₁ Δm) , (^^~ Γw Γm Δw Δm )) , Am , refl)


  Σ^^~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) )) →
    Σ _ (Con~' _ Δw )
  Σ^^~ Γw Γm Δw Δm = _ , ^^~ Γw Γm Δw Δm

  ▶t~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Ap} Aw (Am : Σ _ (Ty~' (Γp ^^ Δp) Ap Aw (₁ Γm M.^^ ₁ Δm) ))
    → Telescope~ {Γp} (Δp ▶p Ap) (▶w Δw Aw) (₁ Γm) (₁ Δm M.▶t ₁ Am)

  ▶t~ Γw Γm Δw Δm Aw Am = Δm , Am , refl


  Σ▶t~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Ap} Aw (Am : Σ _ (Ty~' (Γp ^^ Δp) Ap Aw (₁ Γm M.^^ ₁ Δm) ))
    → Σ _ (Telescope~ {Γp} (Δp ▶p Ap) (▶w Δw Aw) (₁ Γm))
  Σ▶t~ Γw Γm Δw Δm Aw Am =  _ , ▶t~ Γw Γm Δw Δm Aw Am

  ΣEl~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
           tp tw (Am : Σ _ (Tm~' Γp Up tp tw (₁ Γm) (M.U _))) →
           Σ _ (Ty~' Γp (Elp tp) (Elw Γw tw) (₁ Γm))
  ΣEl~ Γw Γm tp tw Am = _ , Am , refl

  -- Σ▶~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))


-- -}

-- La verion par récurrence sur Δp  est plus pratique dans certains cas que
-- la version Tel~ Δw Δm = Con~ Δw (₁ Δm)
-- mais beaucoup moinsdans le cas liftV~ quand le telescope est non vide.
-- en effet, dans ce cas, je dois pouvoir montrer que si le telescope est en relation
-- alors le contexte sous jacent l'est, et j'ai la flemme de le montrer.
-- Il semble cependant, j'en ai vraiment besoin dans l e cas liftV0 ∙p V0w
  Tel~ : {Γp : Conp}{Δp : Conp}(Δw : Telw Γp Δp) → {Γm : M.Con} → M.Tel Γm → Set (lmax M.i (lmax M.j k))
  -- Tel~ Δw Δm = Con~ Δw (₁ Δm)
  -- Tel~ {Δp = Δp} Δw Δm = {!!}
  Tel~ {Δp = ∙p} Δw Δm = Lift {ℓ   = lmax k M.j}(Δm ≡ M.∙t _)
  Tel~ {Γ} {Δp = Δp ▶p Ap} (▶w Δw Aw) {Γm = Γm} Cm =
    Σ (∃ (Tel~ {Γp = Γ }Δw {Γm}))
    (λ Δm → Σ (∃ (Ty~ Aw {Γm M.^^ (₁ Δm)}))
    λ Am → Cm ≡ (₁ Δm M.▶t ₁ Am))

  ^^~ : {Γp : Conp}{Γw : Conw Γp}(Γm : ∃ (Con~ Γw))
   {Δp : Conp}{Δw : Telw Γp Δp} {Δm : M.Tel (₁ Γm)} →
   (Δr : Tel~ {Γp = Γp}{Δp} Δw Δm) → Con~ Δw (₁ Γm M.^^ Δm)
   -- Tel^^Con~{Γp}{Γw}Γm{Δp}{Δw}{Δm}Δr  = {!Δp!}
  ^^~ {Γp} {Γw} Γm {∙p} {Δw} {_} (lift refl) rewrite prop-has-all-paths Δw Γw = ₂ Γm
  ^^~ {Γp} {Γw} Γm {Δp ▶p Ap} {▶w Δw Aw}  (Δm , Am , refl) =
     (_ , ^^~ Γm (₂ Δm)) ,
     (Am , refl)
