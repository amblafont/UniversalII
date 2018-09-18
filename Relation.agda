{-# OPTIONS --rewriting  #-}
-- an attempt with rewrite rules, but by postulating the model rather than defining a record (because rewrite rules don't work)

-- open import HoTT.Base
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
import Model
open import Syntax
module Relation {α} where
  module M = Model {α}
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
  Con~' : (Γp : Conp)(Γw : Conw Γp) → M.Con → Set α
  Ty~'  : (Γp : Conp)(Ap : Typ)(Aw : Tyw Γp Ap) (Δm : M.Con) (Cm : M.Ty Δm)  → Set α
  Tm~'  : (Γp : Conp)(Ap : Typ)(tp : Tmp)(tw : Tmw Γp Ap tp)(Δm : M.Con)(Cm : M.Ty Δm)(zm : M.Tm _ Cm)  → Set α
  Var~'  : (Γp : Conp)(Ap : Typ)(xp : ℕ)(xw : Varw Γp Ap xp)(Δm : M.Con)(Cm : M.Ty Δm)(zm : M.Tm _ Cm)  → Set α
  Telescope~ : ∀ {Γp}Δp (Δw : Conw (Γp ^^ Δp)) (Γm : M.Con)(Δm : M.Telescope Γm) → Set α

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
    -- this left associative stuff makes it easier to inhbabite thanks to pair=
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
    -- this left associative stuff makes it easier to inhbabite thanks to pair=
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


-- I think the following is deprecated
-- helper to inhabit v1 ~ zm
  v1~ : ∀ {Γp : Conp}(Γw : Conw Γp){Ap}(Aw : Tyw Γp Ap){Exp}(Exw : Tyw (Γp ▶p Ap) Exp) →
    ∀ (Γm : Σ _ (Con~' Γp Γw))
       (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
       -- this will be deduced later (weakening preserves the relation)
       (Ar : Ty~' _ _ (wkTw Aw Aw) (₁ Γm M.▶ ₁ Am) (M.wkT (₁ Γm) (₁ Am) (₁ Am)))
       (Exm : Σ _ (Ty~' _ _ Exw (₁ Γm M.▶ ₁ Am))) → 
    ∀ Δm Cm zm → 
     mkΣTm Δm Cm zm ≡
         ((((₁ Γm M.▶ (₁ Am)) M.▶ (₁ Exm)) , M.wkT _ (₁ Exm) (M.wkT _ (₁ Am) (₁ Am)) ) ,
          M.wkt _ (₁ Exm) _ (M.V0 _ (₁ Am))) 
     →
    Var~' _ _ _
       (VSw _ (▶w Γw Aw) _ Exw _ (wkTw Aw Aw) 0 (V0w _ Γw _ Aw)) Δm Cm zm
  v1~ Γw Aw Exw Γm Am Ar Exm Δm Cm zm eq =
    transport!
    {A = Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x) }
    (λ x →
      Var~' _ _ _
      (VSw _ (▶w Γw Aw) _ Exw _ (wkTw Aw Aw) 0 (V0w _ Γw _ Aw)) (₁ (₁ x)) (₂ (₁ x)) (₂ x)
    ) eq
    (
    ((_ , Γm , Am , refl)) , 
    Exm , (((M.wkT _ (₁ Am)(₁ Am)) , Ar) ,
    (M.V0 (₁ Γm) (₁ Am) , Γm , Am , refl) , refl))

  v1~' : ∀ {Γp : Conp}(Γw : Conw Γp){Ap}(Aw : Tyw Γp Ap){Exp}(Exw : Tyw (Γp ▶p Ap) Exp) 
    (wxw : Varw (Γp ▶p Ap ▶p Exp) (wkT (wkT Ap)) (1)) →
    ∀ (Γm : Σ _ (Con~' Γp Γw))
    (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    -- this will be deduced later (weakening preserves the relation)
    (Ar : Ty~' _ _ (wkTw Aw Aw) (₁ Γm M.▶ ₁ Am) (M.wkT (₁ Γm) (₁ Am) (₁ Am)))
    (Exm : Σ _ (Ty~' _ _ Exw (₁ Γm M.▶ ₁ Am))) → 
    ∀ Δm Cm zm → 
    mkΣTm Δm Cm zm ≡
    ((((₁ Γm M.▶ (₁ Am)) M.▶ (₁ Exm)) , M.wkT _ (₁ Exm) (M.wkT _ (₁ Am) (₁ Am)) ) ,
    M.wkt _ (₁ Exm) _ (M.V0 _ (₁ Am))) 
    →
    Var~' _ _ _
    wxw Δm Cm zm

  v1~' Γw Aw Exw wxw with prop-path (VarwP _ _ _) wxw (VSw _ (▶w Γw Aw) _ Exw _ (wkTw Aw Aw) 0 (V0w _ Γw _ Aw)) 
  v1~' Γw Aw Exw .(VSw (_ ▶p _) (▶w Γw Aw) _ Exw (liftT 0 _) (liftTw Aw ∙p Aw) 0 (V0w _ Γw _ Aw)) | refl
    = v1~ Γw Aw Exw

