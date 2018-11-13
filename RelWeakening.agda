{-# OPTIONS  --rewriting  #-}

-- proof that is 
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
import Model
open import Syntax

module RelWeakening {α} where
  open import Relation {α}
  open import RelationProp {α}

{-


Preservation of the relation by weakening


-}



  liftT~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Exp} Exw (Exm : Σ _ (Ty~' Γp Exp Exw (₁ Γm)) )
    {Bp} Bw wBw Bm
    → Ty~' (Γp ^^ Δp) Bp Bw ((₁ Γm) M.^^ (₁ Δm))  Bm
    → Ty~' ((Γp ▶p Exp)^^ (wkC Δp)) (liftT ∣ Δp ∣ Bp) wBw
      (((₁ Γm) M.▶ (₁ Exm)) M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm))
      (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) Bm) 


  -- shortcut
  wkT~ : ∀ {Γp} Γw (Γm : (Σ _ (Con~' Γp Γw)))
    {Exp} (Exw : Tyw Γp Exp)(Exm : Σ _ (Ty~' Γp Exp Exw (₁ Γm)))
    {Ap} (Aw : Tyw Γp Ap)(Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    wAw
    → Ty~' (Γp ▶p Exp) (wkT Ap) wAw
    (₁ Γm M.▶ ₁ Exm)
    (M.wkT (₁ Γm) (₁ Exm)(₁ Am))
  wkT~ Γw Γm Exw Exm Aw Am wAw = liftT~ Γw Γm {∙p} Γw
    (M.∙t (₁ Γm) , refl) Exw Exm Aw wAw (₁ Am) (₂ Am)

  liftt~ : ∀ {Γp} {Γw} (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Ep} Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm)) )
    {Bp} Bm

    {tp} tw
    wtw
    tm
    → Tm~' (Γp ^^ Δp) Bp tp tw
    ((₁ Γm) M.^^ (₁ Δm)) Bm tm
    → Tm~' ((Γp ▶p Ep)^^ (wkC Δp)) (liftT ∣ Δp ∣ Bp) (liftt ∣ Δp ∣ tp)
    wtw
    -- (liftVw {Ap = Ep} Ew Δp {Bp = Bp} {tp} tw )
    (((₁ Γm) M.▶ (₁ Em)) M.^^ M.wkC (₁ Γm) (₁ Em) (₁ Δm)) (M.liftT (₁ Γm) (₁ Δm) (₁ Em) Bm) (M.liftt (₁ Γm) (₁ Δm) (₁ Em) Bm tm)

      -- let us start form minmal requirement

  liftV~ : ∀ {Γp} {Γw} (Γm : Σ _ (Con~' Γp Γw))
        {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
      {Exp} Exw (Exm : Σ _ (Ty~' Γp Exp Exw (₁ Γm)) )
      {Bp} Bm

      {xp} xw
      -- should this wxw be given ?
      --- yes so that it does not unfold unwantingly the goal
      wxw
      xm
      → Var~' (Γp ^^ Δp) Bp xp xw
        ((₁ Γm) M.^^ (₁ Δm)) Bm xm
      → Var~' ((Γp ▶p Exp)^^ (wkC Δp)) (liftT ∣ Δp ∣ Bp) (liftV ∣ Δp ∣ xp)
        wxw
        -- (liftVw {Ap = Exp} Exw Δp {Bp = Bp} {xp} xw )
        (((₁ Γm) M.▶ (₁ Exm)) M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm)) (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) Bm) (M.liftt (₁ Γm) (₁ Δm) (₁ Exm) Bm xm)



  wkTelescope~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
                   {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
                   {Ep} Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm))) →
        Telescope~ (wkC Δp) (wkCw' Ew Δp Δw) (₁ Γm M.▶ ₁ Em) (M.wkC (₁ Γm) (₁ Em) (₁ Δm))

  wkTelescope~ Γw Γm {∙p} Δw Δm Ew Em rewrite (₂ Δm) = refl

  wkTelescope~ Γw Γm {Δp ▶p Ap} (▶w Δw Aw) (_ , Δm , Am , refl) Ew Em =
    ( M.wkC (₁ Γm) (₁ Em) (₁ Δm) , wkTelescope~ Γw Γm Δw Δm Ew Em) ,
    (M.liftT (₁ Γm) (₁ Δm)(₁ Em) (₁ Am) , liftT~ Γw Γm Δw Δm Ew Em Aw (liftTw Ew Δp Aw) (₁ Am) (₂ Am)) ,
    refl


-- Σ means we bundle the model stuff and its relational proof together in a Σ type in the conclusion
-- these are shortcuts that use the true recursive functions wkC, lift*~
  ΣCon~'▶ : ∀ {Γp}{Γw : Conw Γp}{Ap} {Aw : Tyw Γp Ap}
    (Γm : Σ M.Con (Con~' Γp Γw))
    (Am   : Σ (M.Ty (₁ Γm)) (Ty~' Γp Ap Aw (₁ Γm)))
    (ΓAw :
    Conw (Γp ▶p Ap)) → Σ M.Con (Con~' (Γp ▶p Ap) ΓAw)
  ΣCon~'▶ {Γw = Γw} {Aw = Aw} Γm Am ΓAw = 
    (₁ Γm M.▶ ₁ Am) ,
    (trCon~' (▶w Γw Aw) ΓAw (₁ Γm M.▶ ₁ Am)
      (Γm , (Am , refl)))



-- this is also induced by ΣliftT~'
  ΣwkTy~' : ∀ {Γp}{Γw : Conw Γp}{Ap} {Aw : Tyw Γp Ap}{Bp}{Bw : Tyw Γp Bp}
      (Γm : Σ M.Con (Con~' Γp Γw))
      (Am   : Σ (M.Ty (₁ Γm)) (Ty~' Γp Ap Aw (₁ Γm)))
      (Bm   : Σ (M.Ty (₁ Γm)) (Ty~' Γp Bp Bw (₁ Γm))) →
      Σ (M.Ty (₁ Γm M.▶ ₁ Am)) (Ty~' (Γp ▶p Ap) (wkT Bp) (wkTw Aw Bw) (₁ Γm M.▶ ₁ Am))

  ΣwkTy~' {Γw = Γw} {Aw = Aw} {Bw = Bw} Γm Am Bm  = 
    (M.wkT _ (₁ Am)(₁ Bm)) ,
    wkT~ Γw Γm Aw Am Bw Bm (wkTw Aw Bw)
    




  Σ^^wk~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
          {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
          {Ep}Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm) ))
          → Σ _ (Con~' (Γp ▶p Ep ^^ wkC Δp) (wkCw' Ew Δp Δw))

  Σ^^wk~ {Γp} Γw Γm {Δp} Δw Δm {Ep} Ew Em =
    (₁ Γm M.▶ ₁ Em M.^^ M.wkC (₁ Γm) (₁ Em) (₁ Δm)) ,
      ^^~ {Γp = Γp ▶p Ep} (▶w _ Ew)
      (((₁ Γm) M.▶ (₁ Em)) , Γm , Em , refl)
      {Δp  = wkC Δp} (wkCw' Ew Δp Δw)
      ((M.wkC (₁ Γm) (₁ Em) (₁ Δm)) , wkTelescope~ _ Γm _ Δm Ew Em)

  ΣliftT~' :  ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Ep}Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm) ))
    {Ap} Aw (Am : Σ _ (Ty~' (Γp ^^ Δp) Ap Aw (₁ Γm M.^^ ₁ Δm)))
    → Σ _ (Ty~' (Γp ▶p Ep ^^ wkC Δp) (liftT ∣ Δp ∣ Ap)
        (liftTw Ew Δp Aw) (₁ Γm M.▶ ₁ Em M.^^ M.wkC (₁ Γm) (₁ Em) (₁ Δm) ))

  ΣliftT~' Γw Γm {Δp} Δw Δm Ew Em Aw Am =
    M.liftT (₁ Γm) (₁ Δm)(₁ Em) (₁ Am) , liftT~ _ Γm {Δp} _  Δm Ew Em  Aw (liftTw Ew Δp Aw) (₁ Am) (₂ Am)  
  
  Σliftt~' :  ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Ep}Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm) ))
    {Ap} Am
    {tp} tw (tm : Σ _ (Tm~' (Γp ^^ Δp) Ap tp tw (₁ Γm M.^^ ₁ Δm) Am  ))
    → Σ _ (Tm~' (Γp ▶p Ep ^^ wkC Δp) (liftT ∣ Δp ∣ Ap)
    (liftt ∣ Δp ∣ tp) (lifttw Ew Δp tw)  (₁ Γm M.▶ ₁ Em M.^^ M.wkC (₁ Γm) (₁ Em) (₁ Δm) )
    (M.liftT (₁ Γm) (₁ Δm)(₁ Em) Am)
    )
  Σliftt~' Γw Γm {Δp} Δw Δm Ew Em Am tw tm = 
    (M.liftt (₁ Γm) (₁ Δm) (₁ Em) Am (₁ tm)) ,
    (liftt~ Γm Δw Δm Ew Em Am tw (lifttw Ew Δp tw) (₁ tm) (₂ tm))

  ΣliftV~' :  ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) ))
    {Ep}Ew (Em : Σ _ (Ty~' Γp Ep Ew (₁ Γm) ))
    {Ap} Am
    {xp} xw (xm : Σ _ (Var~' (Γp ^^ Δp) Ap xp xw (₁ Γm M.^^ ₁ Δm) Am  ))
    → Σ _ (Var~' (Γp ▶p Ep ^^ wkC Δp) (liftT ∣ Δp ∣ Ap)
        (liftV ∣ Δp ∣ xp) (liftVw Ew Δp xw)  (₁ Γm M.▶ ₁ Em M.^^ M.wkC (₁ Γm) (₁ Em) (₁ Δm) )
        (M.liftT (₁ Γm) (₁ Δm)(₁ Em) Am)
      )
  ΣliftV~' Γw Γm {Δp} Δw Δm Ew Em Am xw xm = 
    (M.liftt (₁ Γm) (₁ Δm) (₁ Em) Am (₁ xm)) ,
    (liftV~ Γm Δw Δm Ew Em Am xw (liftVw Ew Δp xw) (₁ xm) (₂ xm))

  liftT~ {Γp} Γw Γm {Δp} Δw Δm {Exp} Exw Exm {.Up} (Uw .(Γp ^^ Δp) Δw') (Uw .(Γp ▶p Exp ^^ wkC Δp) ΓEΔw) .(Model.U (₁ Γm Model.^^ ₁ Δm)) refl
    = refl
    -- M.liftU  (₁ Δm) (₁ Exm) (but ok with rewrite rules)

  liftT~ {Γp} Γw Γm {Δp} Δw Δm {Exp} Exw Exm {.(ΠΠp (Elp _) _)} (Πw Δw' Aw Bw) (Πw ΓEΔw Aw' wBw) .(Model.ΠΠ (₁ Γm Model.^^ ₁ Δm) (₁ am) (₁ Bm')) (am , Bm' , refl)
    rewrite prop-has-all-paths Aw' (lifttw Exw Δp Aw)
    | prop-has-all-paths wBw (liftTw Exw (Δp ▶p Elp _) Bw)
    =
    -- Aw is smaller than the principal argument (Πw Δw' Aw Bw)
    Σliftt~' Γw Γm Δw Δm Exw Exm (M.U _) Aw am , 
    ΣliftT~' _ Γm (▶w Δw (Elw Δw' Aw))
      -- this function is not part of the recursive block
      (Σ▶t~ _ Γm _ Δm {Elp _} (Elw Δw' Aw) (_ , am , refl))
      Exw Exm
      -- Bw is smaller than the principal argument
      Bw
      Bm'
        ,
        refl
        -- M.liftΠ (₁ Δm) (₁ Exm) _ (₁ Bm') 

  -- principal argument  Elw Δw' aw
  liftT~ {Γp} Γw Γm {Δp} Δw Δm {Exp} Exw Exm {.(Elp _)} (Elw Δw' aw) (Elw Γw₁ waw) _ (am , refl)
    rewrite prop-has-all-paths waw (lifttw Exw Δp aw) =
    -- aw is smaller than the principal argument
    Σliftt~' _ Γm _ Δm Exw Exm {Up} (M.U _) aw  am
    ,
    refl

  liftt~ {Γp} {Γw} Γm {Δp} Δw Δm Ew Em {Bp} Bm {.(V _)} (vw xw) (vw wxw) tm tr =
  -- xw is smaller than the principal argument
     liftV~ Γm Δw Δm Ew Em Bm xw wxw tm tr
     -- {!liftV~ Γm Δw Δm Ew Em Bm xw wxw tm tr!}

  -- Γ ^ Δ ⊢ t : Π A B ~ tm
  -- Γ ^ Δ ⊢ u : A ~ um
  -- B ~ Bm
  -- A ~ am
  liftt~ {Γp} {Γw} Γm {Δp} Δw Δm {Ep} Ew Em {.(l-subT 0 u Bp)} .(Model.subT (₁ Γm Model.^^ ₁ Δm) (Model.El (₁ Γm Model.^^ ₁ Δm) (₁ am)) (₁ um) (₁ Bm)) {.(app t u)} (appw .(Γp ^^ Δp) Δw' A aw Bp Bw t tw u uw) waw .(Model.app (₁ Γm Model.^^ ₁ Δm) (₁ am) (₁ Bm) (₁ tm) (₁ um)) (am , Bm , tm , um , refl)
   rewrite lift-subT ∣ Δp ∣ u Bp
    | prop-has-all-paths waw
         (appw (Γp ▶p Ep ^^ wkC Δp ) (wkCw' Ew Δp Δw') (liftt ∣ Δp ∣ A) (lifttw Ew Δp aw) (liftT (S ∣ Δp ∣) Bp ) (liftTw {Γp} {Ap = Ep } Ew (Δp ▶p Elp A ) Bw)
        (liftt ∣ Δp ∣ t)
        (lifttw Ew Δp {Bp = ΠΠp (Elp A) Bp} tw)
        (liftt ∣ Δp ∣ u)
        (lifttw Ew Δp {Bp = Elp A} uw))
    = (Σliftt~' _ Γm _ Δm Ew Em {Ap = Up} (M.U _) aw am) ,
    -- ?? Σ▶t~
    (ΣliftT~' _ Γm (▶w Δw (Elw Δw aw))
       (Σ▶t~ _ Γm _ Δm {Ap = Elp A} (Elw Δw aw) (ΣEl~ Δw (Σ^^~ Γw Γm Δw Δm) _ aw am))
       Ew Em Bw Bm) ,
      Σliftt~' _ Γm _ Δm Ew Em (M.ΠΠ (₁ Γm M.^^ ₁ Δm) (₁ am) (₁ Bm)) tw tm ,
    (Σliftt~' _ Γm _ Δm Ew Em _ uw um) ,
    finaleq
   where
    finaleq : _
    -- I need sub El = El sub and lift El = El lift. I require definitional equalities here in the model because
    -- I don't know how to handle this sigma equality nicely
    finaleq =
      pair= (M.lift-subT (₁ Δm)(₁ Em) _ (₁ Bm) (₁ um))
      (M.lift-app {₁ Γm} (₁ Δm) (₁ Em) (₁ am) (₁ Bm) (₁ tm)
       (₁ um)
      )


    

  liftV~ {Γw = Γw'} (Ym , Yr) {∙p} Δw (.(Model.∙t Ym) , refl) {Exp} Exw Exm Bm (V0w Γp Γw Ap Aw) wxw xm (Γm , Am , eq)
      = 
      tr P (! eq )
       Prefl
       Exm
      where
        P : (YBxm : Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x)) → Set α
        P YBxm = 
          (Exm' : Σ (M.Ty (₁ (₁ YBxm)))(Ty~' (Γp ▶p Ap) _ Exw (₁ (₁ YBxm)))) →
          Var~' (Γp ▶p Ap ▶p _) (liftT 0 (liftT 0 Ap)) 1 wxw
          ((₁ (₁ YBxm)) M.▶ ₁ Exm' M.^^ M.wkC (₁ (₁ YBxm)) (₁ Exm') (M.∙t (₁ (₁ YBxm))))
          (M.liftT (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)))
          (M.liftt (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)) (₂ YBxm))
        Prefl : _
        Prefl Exm'
          rewrite prop-has-all-paths wxw (VSw _ (▶w Γw Aw) _ Exw (wkT Ap) (wkTw Aw Aw) O (V0w Γp Γw Ap Aw))
          = (_ , Γm , Am , refl) ,
          (Exm' ,
          ((ΣwkTy~' Γm Am Am) ,
          ((_ , Γm , Am , refl) ,
          refl)))

     
  liftV~ (Ym , Yr) {∙p} Δw (.(M.∙t Ym) , refl) Exw Exm Bm (VSw Γp Γw Ap Aw Bp Bw xp xw) wxw xm (Γm , Am , Bm' , xm' , eq)
   = tr P (! eq)  Prefl Exm
    where
      P : (YBxm : Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x)) → Set α
      P YBxm = 
        (Exm' : Σ (M.Ty (₁ (₁ YBxm)))(Ty~' (Γp ▶p Ap) _ Exw (₁ (₁ YBxm)))) →
        Var~' (Γp ▶p Ap ▶p _) (liftT 0 (liftT 0 Bp)) (S (S xp)) wxw
        ((₁ (₁ YBxm)) M.▶ ₁ Exm' M.^^ M.wkC (₁ (₁ YBxm)) (₁ Exm') (M.∙t (₁ (₁ YBxm))))
        (M.liftT (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)))
        (M.liftt (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)) (₂ YBxm))
      Prefl :  P
        (((₁ Γm M.▶ ₁ Am) , M.wkT (₁ Γm) (₁ Am) (₁ Bm')) ,
        M.wkt (₁ Γm) (₁ Am) (₁ Bm') (₁ xm'))
      Prefl Exm'
        rewrite prop-has-all-paths wxw 
          (VSw (Γp ▶p Ap) Δw _ Exw _
            (wkTw Aw Bw)
            (S xp)
            (VSw Γp Γw Ap Aw Bp Bw xp xw))
        =
          (ΣCon~'▶ {Γw = Γw} {Aw = Aw} Γm Am Δw ,
          Exm' ,
          ΣwkTy~' {Γw = Γw} {Aw = Aw} {Bw = Bw}
            Γm Am Bm' ,
          (M.wkt (₁ Γm) (₁ Am) (₁ Bm') (₁ xm') , Γm , (Am , (Bm' , (xm' , refl)))) ,
            refl)



{-
DEPRECATED
Here we need to know that at most one model type relates to a syntacitc type.

Indeed, I have the following hypotheses : (E = Ex)

    Γ ⊢ E ~ Γₘ ⊢ Eₘ
    Γ ^ Δ ~ ΓΔₘ
Γ ^ Δ ⊢ A ~ ΓΔₘ ⊢ Aₘ
Γ ⊢ Δ ▶ A ~ Γm ⊢ ΔAm from which we deduce the existece of Δₘ ~ Δ and Aₘ' such that Γ ^ Δ ⊢ A ~ Γₘ ^ Δₘ ⊢ Aₘ'
  (and you will see that we will need that Aₘ = Aₘ')

and also
Γₘ ^ ΔAₘ ⊢ xₘ : Bₘ

With the following equations:

Γₘ ^ ΔAₘ = ΓΔm ▶ Aₘ
Bₘ = ΓΔₘ ▶ Aₘ ⊢ wk Am
xₘ = v0

and we would like to show that

    Γ  ▶ E ^ wkΔ ▶ wk A ⊢ v0 : wkA ~ Γₘ ▶ Eₘ ^ wk ΔAₘ ⊢ xₘ

liftV~ {Γp} (Γm , Γr) {Δp ▶p Ap} (▶w Δw Aw) (.(₁ Δm M.▶t ₁ Am') , Δm , Am' , refl) {Exp} Exw Exm Bm (V0w .(Γp ^^ Δp) ΓΔw .Ap Aw') wxw xm (ΓΔm , Am , eq)
--  we know that Δw = ΓΔw and ΓΔm = (Σ^^~ _ (Γm , Γr) _ Δm) by hProp-itude
-- the first is replaced with the second
rewrite prop-has-all-paths Δw ΓΔw | prop-has-all-paths ΓΔm  (Σ^^~ _ (Γm , Γr) _ Δm)
| prop-has-all-paths Aw' Aw | prop-path (TyP _ _ Aw (Γm M.^^ ₁ Δm)) Am Am'

-}

 -- principal argument : V0w ..
  liftV~ {Γp} (Γm , Γr) {Δp ▶p Ap} (▶w Δw Aw') (.(₁ Δm M.▶t ₁ Am') , Δm , Am' , refl) {Exp} Exw Exm Bm (V0w .(Γp ^^ Δp) ΓΔw .Ap Aw) wxw xm (ΓΔm , Am , eq)
  --  we know that Δw = ΓΔw and ΓΔm = (Σ^^~ _ (Γm , Γr) _ Δm) by hProp-itude
  -- the first is replaced with the second
    rewrite
       prop-has-all-paths Δw ΓΔw | prop-has-all-paths ΓΔm  (Σ^^~ _ (Γm , Γr) _ Δm)
      | prop-has-all-paths Aw' Aw | prop-path (TyP _ _ Aw (Γm M.^^ ₁ Δm)) Am Am'
      -- this says that
      | (comm-liftT ∣ Δp ∣ Ap)

      = 
      tr (λ Bxm → statment wxw (₁ Bxm) (₂ Bxm)) (! (₁triple= eq))
        (trVar~' {xp = from-nat (from-nat (from-nat 0))}
        (V0w (Γp ▶p _ ^^ wkC Δp) (wkCw' Exw Δp ΓΔw) (liftT ∣ Δp ∣ Ap) (liftTw Exw Δp Aw))
        wxw _
        (Σ^^wk~ _ (Γm , Γr) ΓΔw Δm Exw Exm ,
        ΣliftT~' _ (Γm , Γr) ΓΔw Δm Exw Exm Aw Am' , 
          ₁mk-triple= (M.lift-wkT {Δ = ₁ Δm}(₁ Am') (₁ Am')(₁ Exm))
            (M.liftV0 _ (₁ Δm) (₁ Am') (₁ Exm))
         ))
    where
      statment : ∀ wxw Bm xm  → Set _
      statment wxw Bm xm  =
        Var~' ((Γp ▶p Exp ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Ap)
        (liftT 0 (liftT ∣ Δp ∣ Ap)) 0 wxw               
        (Γm M.▶ ₁ Exm M.^^ M.wkC Γm (₁ Exm) (₁ Δm) M.▶  
        M.liftT Γm (₁ Δm) (₁ Exm) (₁ Am'))             
        (M.liftT Γm (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm)       
        (M.liftt Γm (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm xm)    

      


  liftV~ Γm {Δp ▶p Ap} (▶w Δw' Aw') (_ , Δm , Am' , refl) Exw Exm Bm (VSw .(_ ^^ Δp) Δw .Ap Aw Bp Bw xp xw) wxw xm
    (ΓΔm , Am , Bm' , xm' , eq)
    rewrite prop-has-all-paths Aw' Aw
    | prop-has-all-paths Δw' Δw
    | prop-has-all-paths ΓΔm  (Σ^^~ _ Γm _ Δm)
    | prop-path (TyP _ _ Aw (₁ Γm M.^^ ₁ Δm)) Am Am'
    | comm-liftT ∣ Δp ∣ Bp
    | prop-has-all-paths wxw
        (VSw (_ ▶p _ ^^ wkC Δp) (wkCw' Exw Δp Δw) (liftT ∣ Δp ∣ Ap)
        (liftTw Exw Δp Aw) (liftT ∣ Δp ∣ Bp) (liftTw Exw Δp Bw) (liftV ∣ Δp ∣ xp)
          (liftVw Exw Δp xw))
    = 
      Σ^^wk~ _ Γm _ Δm Exw Exm ,
        (ΣliftT~' _ Γm Δw Δm Exw Exm Aw Am' ) ,
        ((ΣliftT~' _ Γm Δw Δm Exw Exm Bw Bm'  ) ,
        ΣliftV~' _ Γm Δw Δm Exw Exm (₁ Bm') xw xm' ,
        tr statment (! (₁triple= eq))
        (₁mk-triple= (M.lift-wkT {Δ = ₁ Δm}(₁ Am')(₁ Bm') (₁ Exm))
        (M.lift-wkt (₁ Δm) (₁ Am') (₁ Bm') (₁ Exm) (₁ xm'))))
    where
     statment : Σ _ (M.Tm (₁ Γm M.^^ ₁ Δm M.▶ ₁ Am')) → Set _
     statment (Bm , xm) = 
      ((₁ Γm M.▶ ₁ Exm M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm) M.▶
      M.liftT (₁ Γm) (₁ Δm) (₁ Exm) (₁ Am'))
      , M.liftT (₁ Γm) (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm)
      , M.liftt (₁ Γm) (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm xm
      ≡
      ((₁ Γm M.▶ ₁ Exm M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm) M.▶
      M.liftT (₁ Γm) (₁ Δm) (₁ Exm) (₁ Am'))
      ,
      M.liftT (₁ Γm M.▶ ₁ Exm M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm))
      (M.∙t (₁ Γm M.▶ ₁ Exm M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm)))
      (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) (₁ Am'))
      (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) (₁ Bm')))
      ,
      M.liftt (₁ Γm M.▶ ₁ Exm M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm))
      (M.∙t (₁ Γm M.▶ ₁ Exm M.^^ M.wkC (₁ Γm) (₁ Exm) (₁ Δm)))
      (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) (₁ Am'))
      (M.liftT (₁ Γm) (₁ Δm) (₁ Exm) (₁ Bm'))
      (M.liftt (₁ Γm) (₁ Δm) (₁ Exm) (₁ Bm') (₁ xm'))
