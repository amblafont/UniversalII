{-# OPTIONS  --rewriting  #-}

-- proof that is 
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
import Model
open import Syntax

module RelSubst {α} where
  open import Relation {α}
  open import RelationProp {α}
  open import RelWeakening {α}

{-


Preservation of the relation by substitution


-}

  -- this was needed to do the variable case (it appears e.g. in the last case of l-subV~)
  subTel~ :  ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) 
    {Ep} Ew (Em : (Σ _ (Ty~' Γp Ep Ew (₁ Γm))))
    {Δp} Δw (Δm : (Σ _ (Telescope~ {Γp ▶p Ep} Δp Δw (₁ Γm M.▶ ₁ Em))))
    {zp} zw (zm : (Σ _ (Tm~' Γp Ep zp zw (₁ Γm) (₁ Em))))
    (Δsw : Conw (Γp ^^ (subTel zp Δp))   )
    → Telescope~ {Γp} (subTel zp Δp) Δsw (₁ Γm) (M.subTel (₁ Em) (₁ Δm) (₁ zm))

  -- packed version
  ΣsubTel~ :  ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) 
    {Ep} Ew (Em : (Σ _ (Ty~' Γp Ep Ew (₁ Γm))))
    {Δp} Δw (Δm : (Σ _ (Telescope~ {Γp ▶p Ep} Δp Δw (₁ Γm M.▶ ₁ Em))))
    {zp} zw (zm : (Σ _ (Tm~' Γp Ep zp zw (₁ Γm) (₁ Em))))
    (Δsw : Conw (Γp ^^ (subTel zp Δp))   )
    → Σ _ (Telescope~ {Γp} (subTel zp Δp) Δsw (₁ Γm)) 
  ΣsubTel~ Γw Γm Ew Em Δw Δm zw zm Δsw = _  , subTel~ Γw Γm Ew Em Δw Δm zw zm Δsw
    


-- do I need such a general statment, can I do it only when A = El a ?
-- I don't think assuming A = El a makes the proof simpler anyway
-- Do I need to enforce that Γm is related ?

  l-subT~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) 
    {Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
    {Δp} Δw (Δm : (Σ _ (Telescope~ {Γp ▶p Ap} Δp Δw (₁ Γm M.▶ ₁ Am))))
    {Bp} Bw (Bm : (Σ _ (Ty~' (Γp ▶p Ap ^^ Δp) Bp Bw (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) )))
    {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
    (Bsw : Tyw (Γp ^^ (subTel up Δp))  (l-subT ∣ Δp ∣ up Bp) )
    → Ty~' (Γp ^^ (subTel up Δp)) (l-subT ∣ Δp ∣ up Bp) Bsw (₁ Γm M.^^ M.subTel (₁ Am) (₁ Δm) (₁ um))
      (M.l-subT (₁ Am) (₁ Δm) (₁ um) (₁ Bm))

  l-subt~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) 
    {Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
    {Δp} Δw (Δm : (Σ _ (Telescope~ {Γp ▶p Ap} Δp Δw (₁ Γm M.▶ ₁ Am))))
    {Bp} (Bm : (M.Ty  (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) ))
    {tp} tw (tm : (Σ _ (Tm~' (Γp ▶p Ap ^^ Δp) Bp tp tw (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) Bm)))
    {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
    (tsw : Tmw (Γp ^^ (subTel up Δp))  (l-subT ∣ Δp ∣ up Bp) (l-subt ∣ Δp ∣ up tp))
    → 
    Tm~' (Γp ^^ (subTel up Δp)) (l-subT ∣ Δp ∣ up Bp) (l-subt ∣ Δp ∣ up tp) tsw (₁ Γm M.^^ M.subTel (₁ Am) (₁ Δm) (₁ um))
     (M.l-subT (₁ Am) (₁ Δm) (₁ um) Bm)
      (M.l-subt  (₁ Am) (₁ Δm) (₁ um) Bm (₁ tm))

  l-subV~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) 
      {Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
      {Δp} Δw (Δm : (Σ _ (Telescope~ {Γp ▶p Ap} Δp Δw (₁ Γm M.▶ ₁ Am))))
      {Bp} (Bm : (M.Ty  (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) ))
      {tp} tw (tm : (Σ _ (Var~' (Γp ▶p Ap ^^ Δp) Bp tp tw (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) Bm)))
      {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
      (tsw : Tmw (Γp ^^ (subTel up Δp))  (l-subT ∣ Δp ∣ up Bp) (l-subV ∣ Δp ∣ up tp))
      → 
      Tm~' (Γp ^^ (subTel up Δp)) (l-subT ∣ Δp ∣ up Bp) (l-subV ∣ Δp ∣ up tp) tsw (₁ Γm M.^^ M.subTel (₁ Am) (₁ Δm) (₁ um))
      (M.l-subT (₁ Am) (₁ Δm) (₁ um) Bm)
      (M.l-subt  (₁ Am) (₁ Δm) (₁ um) Bm (₁ tm))
  

  -- packed version of l-subT~
  Σl-subT~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) 
    {Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
    {Δp} Δw (Δm : (Σ _ (Telescope~ {Γp ▶p Ap} Δp Δw (₁ Γm M.▶ ₁ Am))))
    {Bp} Bw (Bm : (Σ _ (Ty~' (Γp ▶p Ap ^^ Δp) Bp Bw (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) )))
    {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
    (Bsw : Tyw (Γp ^^ (subTel up Δp))  (l-subT ∣ Δp ∣ up Bp) )
    →
    Σ _ (Ty~' (Γp ^^ (subTel up Δp)) (l-subT ∣ Δp ∣ up Bp) Bsw (₁ Γm M.^^ M.subTel (₁ Am) (₁ Δm) (₁ um)))
  Σl-subT~ Γw Γm Aw Am Δw Δm Bw Bm uw um Bsw = _ , l-subT~ Γw Γm Aw Am Δw Δm Bw Bm uw um Bsw

  -- packed version of l-subt~
  Σl-subt~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) 
    {Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
    {Δp} Δw (Δm : (Σ _ (Telescope~ {Γp ▶p Ap} Δp Δw (₁ Γm M.▶ ₁ Am))))
    {Bp} (Bm : (M.Ty  (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) ))
    {tp} tw (tm : (Σ _ (Tm~' (Γp ▶p Ap ^^ Δp) Bp tp tw (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm) Bm)))
    {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
    (tsw : Tmw (Γp ^^ (subTel up Δp))  (l-subT ∣ Δp ∣ up Bp) (l-subt ∣ Δp ∣ up tp))
    → Σ _
    (Tm~' (Γp ^^ (subTel up Δp)) (l-subT ∣ Δp ∣ up Bp) (l-subt ∣ Δp ∣ up tp) tsw (₁ Γm M.^^ M.subTel (₁ Am) (₁ Δm) (₁ um))
    (M.l-subT (₁ Am) (₁ Δm) (₁ um) Bm))

  Σl-subt~ Γw Γm Aw Am Δw Δm Bm tw tm uw um tsw = _ , l-subt~ Γw Γm Aw Am Δw Δm Bm tw tm uw um tsw 

  subTel~ Γw Γm {Ep} Ew Em {∙p} (▶w Γw' Ew') (_ , refl) {zp} zw zm Δsw = refl

  subTel~ Γw Γm {Ep} Ew Em {Δp ▶p Ap} (▶w Δw Aw) (_ , Δm , Am , refl) {zp} zw zm (▶w Δsw Asw) =
    ▶t~ Γw Γm Δsw (_ , subTel~ _ Γm Ew Em {Δp} Δw Δm zw zm Δsw )
     Asw (Σl-subT~ Γw Γm Ew Em Δw Δm {Ap} Aw Am zw zm Asw)
    
    
    -- Ty~' (Γp ^^ (subTel up Δp)) (l-subT ∣ Δp ∣ up Bp) Bsw (₁ Γm M.^^ M.subTel (₁ Am) (₁ Δm) (₁ um))
    -- (M.l-subT (₁ Am) (₁ Δm) (₁ um) (₁ Bm))

-- l-subT~ {Γp₁} Γw Γm {Ep} Ew Em {Δp} Δw Δm  Tw Tm {zp} zw zm Tsw = {!Tw!}
  l-subT~ {Γp₁} Γw Γm {Ep} Ew Em {Δp} Δw Δm (Uw .(Γp₁ ▶p Ep ^^ Δp) Γw₁) (.(Model.U (₁ Γm Model.▶ ₁ Em Model.^^ ₁ Δm)) , refl) {zp} zw zm (Uw .(Γp₁ ^^ subTel zp Δp) Γw₂) = refl

  l-subT~ {Γp₁} Γw Γm {Ep} Ew Em {Δp} Δw Δm (Πw Γw₁ {ap₁} Aw Tw) (.(Model.ΠΠ (₁ Γm Model.▶ ₁ Em Model.^^ ₁ Δm) (₁ am) (₁ Bm)) , am , Bm , refl) {zp} zw zm (Πw Γw₂ Aw₁ Tsw)
     =
    Σl-subt~ Γw Γm _ Em _ Δm (M.U _) Aw am zw zm Aw₁ ,
    Σl-subT~ Γw Γm _ Em {Δp ▶p Elp ap₁} (▶w Δw (Elw Δw Aw))
      ((₁ Δm M.▶t M.El _ (₁ am)) ,
        ▶t~ (▶w Γw Ew) (_ , Γm , Em , refl) Δw Δm (Elw Δw Aw) (_ , am , refl))
      Tw Bm zw zm Tsw
     ,
    refl

  l-subT~ {Γp₁} Γw Γm {Ep} Ew Em {Δp} Δw Δm (Elw Γw₁ aw) (_ , am , refl) {zp} zw zm (Elw Γw₂ aw₁) =
    (_ , l-subt~ Γw Γm _ Em _ Δm {Up} (M.U _) aw am zw zm aw₁) ,
    refl



  -- l-subt~ {Γp} Γw Γm {Ap} Aw Am {Δp} Δw Δm {Bp} Bm {tp} tw tm {up} uw um tsw = {!tw!}

  l-subt~ {Γp} Γw Γm {Ap} Aw Am {Δp} Δw Δm {Bp} Bm {.(V _)} (vw xw) tm {up} uw um tsw =
    l-subV~ Γw Γm Aw Am Δw Δm Bm xw tm uw um tsw

  l-subt~ {Γp} Γw Γm {Ap} Aw Am {Δp} Δw Δm {.(l-subT 0 u Bp)} Bm {.(app t u)} (appw .(Γp ▶p Ap ^^ Δp) Γw₁ ap₁ tw Bp Bw t tw₁ u tw₂) (_ , am , Cm , tm' , um' , refl) {up} uw um tsw
   rewrite l-subT-subT ∣ Δp ∣ up u Bp  
     |
    prop-has-all-paths tsw
      (
        (
        (appw (Γp ^^ subTel up Δp) (subTelw uw Δw) (l-subt ∣ Δp ∣ up ap₁) (subtw uw tw)
        (l-subT (S ∣ Δp ∣) up Bp) (subTw {Δp = Δp ▶p Elp ap₁} {Bp = Bp} uw Bw  )
        (l-subt ∣ Δp ∣ up t) (subtw uw tw₁)
        (l-subt ∣ Δp ∣ up u) (subtw uw tw₂)
        )
        )
      )
    =
     
    Σl-subt~ {Γp} Γw Γm {Ap} Aw Am {Δp = Δp} Δw Δm {Up} (M.U (₁ Γm M.▶ ₁ Am M.^^ ₁ Δm)) tw am {up} uw um (subtw uw tw) ,
    Σl-subT~ Γw Γm Aw Am {Δp = Δp ▶p Elp ap₁} (▶w Δw (Elw Δw tw))
        (_ , Δm , (_ , am , refl) , refl) {Bp} Bw Cm uw um (subTw {Δp = Δp ▶p Elp ap₁} {Bp = Bp} uw Bw  ) ,
    Σl-subt~ Γw Γm Aw Am Δw Δm {ΠΠp (Elp ap₁) Bp}
        (M.ΠΠ _ (₁ am) (₁ Cm)) tw₁ tm' uw um (subtw uw tw₁) ,
    Σl-subt~ Γw Γm Aw Am Δw Δm {Elp ap₁} (M.El _ (₁ am)) tw₂ um' uw um (subtw uw tw₂) ,
      pair=
       (M.l-subT-subT (₁ Am) (₁ Δm) (₁ um) _ (₁ um') (₁ Cm))
        (M.sub-app (₁ Am) (₁ Δm)(₁ um) _ _ (₁ tm')(₁ um'))



  subT~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw))) →
    ∀{Ap} Aw (Am : (Σ _ (Ty~' Γp Ap Aw (₁ Γm))))
    {Bp} Bw (Bm : (Σ _ (Ty~' (Γp ▶p Ap) Bp Bw (₁ Γm M.▶ ₁ Am) )))
    {up} uw (um : (Σ _ (Tm~' Γp Ap up uw (₁ Γm) (₁ Am))))
    (Bsw : Tyw Γp (subT up Bp) )
    → Ty~' Γp (subT up Bp) Bsw (₁ Γm)
     (M.subT (₁ Γm)(₁ Am) (₁ um)  (₁ Bm))
  subT~ Γw Γm Aw Am = l-subT~ Γw Γm Aw Am {∙p} (▶w Γw Aw) (M.∙t _ , refl )


  -- l-subV~ {Γp} Γw Γm {Ep} Ew Em {Δp} Δw Δm {Bp} Bm {xp} xw xm {zp} zw zm xsw = {!!}
  {-
  Γ , E ⊢ x : B   =   Γ' , A ⊢ v0 : wkT A 

  et on veut que  Γp ⊢ zp : Ap ~ Γ ⊢ x[z] : B[z]
  sachant que Γp ⊢ zp : Ap  ~  Γ ⊢ z : E
  -}
  -- Γm = Γm' par unicité
  -- Em = Am' par unicité
  l-subV~ {Γp} Γw' Γm {.Ap} Ew Em {∙p} (▶w Γw'' Aw') (_ , refl) {.(liftT 0 Ap)} Bm {.0} (V0w Γp Γw Ap Aw) (xm , Γm' , Am' , exm) {zp} zw zm xsw
    rewrite prop-has-all-paths Γw' Γw | prop-path (ConP _ Γw) Γm' Γm
      | prop-has-all-paths Ew Aw
      | prop-path (TyP _ _ Aw _) Am' Em
      | subT-wkT Ap zp
      | prop-has-all-paths zw xsw
    = tr P (! (₁triple= exm))
      Prefl
    -- Q Bm xm exm
     where
      P : (Ax : Σ (M.Ty (₁ Γm M.▶ ₁ Em)) (M.Tm _)) → Set _
      P Ax = 
        Tm~' Γp Ap zp xsw (₁ Γm)
        (M.l-subT (₁ Em) (M.∙t (₁ Γm M.▶ ₁ Em)) (₁ zm) (₁ Ax))
        (M.l-subt (₁ Em) (M.∙t (₁ Γm M.▶ ₁ Em)) (₁ zm) (₁ Ax) (₂ Ax))
      Prefl : _
      Prefl =
      -- ici il manque le fait que subT ∘ wkT = id (dans la syntaxe : subT-wkT)
        tr (λ y → Tm~' Γp Ap zp xsw (₁ Γm) (₁ y) (₂ y))
          (! (pair= (M.subT-wkT (₁ zm) (₁ Em))
          -- il manque subt u M.V0 ≡ u
            (M.subt-v0 (₁ zm)))) (₂ zm)


  l-subV~ {Γp₁} Γw Γm {.Ap} Ew Em {∙p} (▶w Δw Aw₁) (_ , refl) {.(liftT 0 Bp)} Bm {.(S xp)} (VSw Γp₁ Γw₁ Ap Aw Bp Bw xp xw) (zm' , Γm' , Am , Bm' , xm' , e) {zp} zw zm (vw xw₁)
    rewrite prop-has-all-paths Γw₁ Γw | prop-path (ConP _ Γw) Γm' Γm
     | prop-has-all-paths Aw Ew | prop-path (TyP _ _ Ew _) Am Em
     | subT-wkT Bp zp
    =
    tr P (! (₁triple= e)) Prefl
    where
      P : (Bz : Σ (M.Ty (₁ Γm M.▶ ₁ Em)) (M.Tm _)) → Set _
      P Bz = 
        Var~' Γp₁ Bp xp xw₁ (₁ Γm)    
        (M.l-subT (₁ Em) (M.∙t (₁ Γm M.▶ ₁ Em)) (₁ zm) (₁ Bz))    
        (M.l-subt (₁ Em) (M.∙t (₁ Γm M.▶ ₁ Em)) (₁ zm) (₁ Bz) (₂ Bz))
      Prefl : _
      Prefl rewrite prop-has-all-paths xw xw₁  =
      -- le fait que subT ∘ liftT = id
      -- subT-wkT
         tr (λ y → Var~' Γp₁ Bp xp xw₁ (₁ Γm) (₁ y) (₂ y))
           (! (pair=
                   _
                   (M.subt-wkt (₁ zm) (₁ xm'))))
           (₂ xm')
        
    

  l-subV~ {Γp} Γw Γm {Ep} Ew Em {Δp ▶p Cp} (▶w Δw' Aw₁) (_ , Δm , Am , refl) {.(liftT 0 Cp)} Bm {.0} (V0w .(Γp ▶p Ep ^^ Δp) Δw _ Aw)
    (zm' , Γm' , Am' , e) {zp} zw zm xsw
    rewrite prop-has-all-paths Δw' Δw
     | prop-path (ConP _ Δw) Γm' ( Σ^^~ {Γp ▶p Ep} (▶w Γw Ew) (_ , Γm , Em , refl ) {Δp} Δw Δm )
     | prop-has-all-paths Aw₁ Aw
     | prop-path (TyP _ _ Aw _) Am' Am
     | l-subT-wkT ∣ Δp ∣ zp Cp
     = tr P (! (₁triple= e)) Prefl
     where
      P : (Bz : Σ (M.Ty (₁ Γm M.▶ ₁ Em M.^^ ₁ Δm M.▶ ₁ Am)) (M.Tm _)) → Set _
      P Bz =
       Tm~' ((Γp ^^ subTel zp Δp) ▶p l-subT ∣ Δp ∣ zp Cp)
        (wkT (l-subT ∣ Δp ∣ zp Cp)) (V 0) xsw
        -- (l-subT (S ∣ Δp ∣) zp (liftT 0 Cp)) (V 0) xsw
        (₁ Γm M.^^ M.subTel (₁ Em) (₁ Δm) (₁ zm) M.▶
        M.l-subT (₁ Em) (₁ Δm) (₁ zm) (₁ Am))
        (M.l-subT (₁ Em) (₁ Δm M.▶t ₁ Am) (₁ zm) (₁ Bz))
        (M.l-subt (₁ Em) (₁ Δm M.▶t ₁ Am) (₁ zm) (₁ Bz) (₂ Bz))
      Prefl : _
      Prefl rewrite prop-has-all-paths xsw
         (vw (V0w (Γp ^^ subTel zp Δp) (subTelw zw Δw) (l-subT ∣ Δp ∣ zp Cp)
           (subTw zw Aw₁)))
        =
        Σ^^~ {Γp} Γw Γm {subTel zp Δp} (subTelw zw Δw)
         (ΣsubTel~ {Γp} _ Γm Ew Em Δw Δm zw zm (subTelw zw Δw)),
        (Σl-subT~ {Γp} _ Γm Ew Em Δw Δm {Cp} Aw Am zw zm (subTw zw Aw₁)) ,
        -- l-subT-wkT
        -- M.l-subT o wkT = wkT o subT
        ₁mk-triple= (M.l-subT-wkT (₁ zm) {Δ = ₁ Δm}(₁ Am)(₁ Am))
          -- ici il manque le fait l-subT (S n) u v0 = v0
          (M.Sn-subt-v0 (₁ zm) (₁ Am))
        

  l-subV~ {Γp} Γw Γm {Ep} Ew Em {Δp ▶p Cp} (▶w Δw' Cw') (_ , Δm , Cm , refl) {.(liftT 0 Bp)} Bm {.(S xp)} (VSw .(Γp ▶p Ep ^^ Δp) Δw _ Cw Bp Bw xp xw) (zm' , ΓΔm , Cm' , Bm' , xm , e) {zp} zw zm xsw
    rewrite
     prop-has-all-paths Δw' Δw
   | prop-path (ConP _ Δw) ΓΔm (Σ^^~ {Γp ▶p Ep} (▶w Γw Ew) (_ , Γm , Em , refl) Δw Δm)
   | prop-has-all-paths Cw' Cw
   | prop-path (TyP _ _ Cw _) Cm' Cm
   | l-subT-wkT ∣ Δp ∣ zp Bp
    = tr P (! (₁triple= e)) Prefl
    where
      P : (Bz : Σ (M.Ty (₁ Γm M.▶ ₁ Em M.^^ ₁ Δm M.▶ ₁ Cm)) (M.Tm _)) → Set _
      P Bz = 
        Tm~' ((Γp ^^ subTel zp Δp) ▶p l-subT ∣ Δp ∣ zp Cp)
        (wkT (l-subT (∣ Δp ∣) zp Bp)) (liftt 0 (l-subV ∣ Δp ∣ zp xp))
        xsw
        (₁ Γm M.^^ M.subTel (₁ Em) (₁ Δm) (₁ zm) M.▶
        M.l-subT (₁ Em) (₁ Δm) (₁ zm) (₁ Cm))
        (M.l-subT (₁ Em) (₁ Δm M.▶t ₁ Cm) (₁ zm) (₁ Bz))
        (M.l-subt (₁ Em) (₁ Δm M.▶t ₁ Cm) (₁ zm) (₁ Bz) (₂ Bz))
      helper : ∀ tsw →  Tm~' (Γp ^^ subTel zp Δp) (l-subT ∣ Δp ∣ zp Bp)
        (l-subV ∣ Δp ∣ zp xp) tsw (₁ Γm M.^^ M.subTel (₁ Em) (₁ Δm) (₁ zm))
        (M.l-subT (₁ Em) (₁ Δm) (₁ zm) (₁ Bm'))
        (M.l-subt (₁ Em) (₁ Δm) (₁ zm) (₁ Bm') (₁ xm))
      Prefl : _
      Q : (y : _) → Set _
      Qrefl : _

      Prefl =
      -- l-subT-wkT
      -- M.l-subT o M.wkT = wkT o l-subT
       
        tr Q
        (! (pair= _ (M.l-subt-wkt (₁ zm) (₁ xm)(₁ Cm)))
        -- (M.Σl-sub-wk (₁ zm)(₁ xm)(₁ Cm))
        )
        Qrefl
           
      helper = l-subV~ {Γp} _ Γm {Ep} Ew Em {Δp} Δw Δm  (₁ Bm') xw xm zw zm 
      Q y = 
        Tm~' ((Γp ^^ subTel zp Δp) ▶p l-subT ∣ Δp ∣ zp Cp)
        (liftT 0 (l-subT ∣ Δp ∣ zp Bp)) (liftt 0 (l-subV ∣ Δp ∣ zp xp)) xsw
        (₁ Γm M.^^ M.subTel (₁ Em) (₁ Δm) (₁ zm) M.▶
        M.l-subT (₁ Em) (₁ Δm) (₁ zm) (₁ Cm))
        (₁ y) (₂ y)
      Qrefl = 
        liftt~ {Γp ^^ subTel zp Δp} {subTelw zw Δw}
          (Σ^^~ _ Γm {subTel zp Δp} (subTelw zw Δw)
          (ΣsubTel~ Γw Γm Ew Em Δw Δm zw zm (subTelw zw Δw)))
          {∙p} (subTelw zw Δw) (M.∙t _ , refl) {l-subT ∣ Δp ∣ zp Cp}
          (subTw zw Cw) (Σl-subT~ _ Γm Ew Em Δw Δm Cw Cm zw zm (subTw zw Cw))
          {l-subT ∣ Δp ∣ zp Bp} (M.l-subT (₁ Em) (₁ Δm) (₁ zm) (₁ Bm'))
          {l-subV ∣ Δp ∣ zp xp} (subVw zw xw) xsw
            _  (helper (subVw zw xw))
        


        -- l-subV~ {Γp} _ Γm {Ep} Ew Em {Δp ▶p Cp} (▶w Δw Cw)
        --   (_ , Δm , Cm , refl) {liftT 0 Bp} (M.wkT _ (₁ Cm) (₁ Bm')) {xp} {!xw!} {!!}
        --   {!!} {!!} {!!}
      







