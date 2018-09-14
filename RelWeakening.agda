{-# OPTIONS  --rewriting --allow-unsolved-metas #-}

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

  liftT~ Γw Γm Δw Δm Exw Exm Bw wBw Bm = {!!}

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
        -- let us start form minmal requirement
  -- ^^~ : ∀ {Γp} Γw Γm
  -- wkTelescope~ : ∀ {Γp} Γm
  --       -- (Γm : Σ _ Con~' Γp Γw)
  --       {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw Γm ))
  --       {Exp} Exw (Exm : Σ _ (Ty~' Γp Exp Exw Γm) )
  --       → Telescope~ {((Γp ▶p Exp)^^ (wkC Δp)) ?
  --         ((Γm M.▶ (₁ Exm)) M.^^ M.wkC Γm (₁ Exm) (₁ Δm))

  -- wkTelescope~ {Γp} Γm Δw Δm {Exp} Exw Exm = ?


-- Σ means we bundle the model stuff and its relational proof together in a Σ type in the conclusion
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
    



  Σ^^~ : ∀ {Γp} Γw (Γm : Σ _ (Con~' Γp Γw))
    {Δp} Δw (Δm : Σ _ (Telescope~ {Γp} Δp Δw (₁ Γm) )) →
    Σ _ (Con~' _ Δw )
  Σ^^~ Γw Γm Δw Δm = _ , ^^~ Γw Γm Δw Δm

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

    

 -- TODO: refaire plus proprement sans utiliser v1~'
  liftV~ (Ym , Yr) {∙p} Δw (.(M.∙t Ym) , refl) Exw Exm Bm (V0w Γp Γw Ap Aw) wxw xm (Γm , Am , eq)
    = tr P (! eq ) Prefl Exm
     where
      P : (YBxm : Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x)) → Set α
      P YBxm = 
        (Exm' : Σ (M.Ty (₁ (₁ YBxm)))(Ty~' (Γp ▶p Ap) _ Exw (₁ (₁ YBxm)))) →
        Var~' (Γp ▶p Ap ▶p _) (liftT 0 (liftT 0 Ap)) 1 wxw
        ((₁ (₁ YBxm)) M.▶ ₁ Exm' M.^^ M.wkC (₁ (₁ YBxm)) (₁ Exm') (M.∙t (₁ (₁ YBxm))))
        (M.liftT (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)))
        (M.liftt (₁ (₁ YBxm)) (M.∙t (₁ (₁ YBxm))) (₁ Exm') (₂ (₁ YBxm)) (₂ YBxm))

      Prefl : P (((₁ Γm M.▶ ₁ Am) , M.wkT (₁ Γm) (₁ Am) (₁ Am)) , M.V0 (₁ Γm) (₁ Am))
      Prefl Exm' =
        v1~' Γw Aw Exw wxw Γm Am (wkT~ _ Γm Aw Am Aw Am (wkTw Aw Aw)  ) Exm' _ _ _
        refl
     
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
      Prefl Exm' =
          trVar~'
          (VSw (Γp ▶p Ap) Δw _ Exw _
            (wkTw Aw Bw)
            (S xp)
            (VSw Γp Γw Ap Aw Bp Bw xp xw))
          wxw _
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


-}
  liftV~ {Γp} (Γm , Γr) {Δp ▶p Ap} (▶w Δw Aw) (.(₁ Δm M.▶t ₁ Am') , Δm , Am' , refl) {Exp} Exw Exm Bm (V0w .(Γp ^^ Δp) ΓΔw .Ap Aw') wxw xm (ΓΔm , Am , eq) rewrite prop-has-all-paths Δw ΓΔw
  -- with eqΓΔm
  -- ...  |  e
    =
    -- here we need that:
    -- (liftT (S ∣ Δp ∣) (liftT 0 Ap)) = liftT 0 Ap (lift |Δp| Ap)
    tr (λ Ap' →
      (wxw : Varw ((Γp ▶p _ ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Ap) Ap' 0) →
      Var~' ((Γp ▶p _ ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Ap) Ap' 0 wxw (Γm M.▶ ₁ Exm M.^^ M.wkC Γm (₁ Exm) (₁ Δm M.▶t ₁ Am'))
      (M.liftT Γm (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm) (M.liftt Γm (₁ Δm M.▶t ₁ Am') (₁ Exm) Bm xm))
      (! (comm_liftT ∣ Δp ∣ Ap))
     ( 
      λ wxw →
      
      trVar~' {xp = from-nat 0} 
      (V0w (Γp ▶p _ ^^ wkC Δp) (wkCw' Exw Δp ΓΔw)
      (liftT ∣ Δp ∣ Ap) (liftTw Exw Δp Aw))
      wxw
      {!xm!}
      -- première composante:
      -- j'ai Γ ^ Δ ~ ΓΔₘ
      -- et Γ ⊢ E ~ Γₘ ⊢ Eₘ
      -- et je veux Γ ▶ E ^ Δ  ~  ??
      -- la solution est  ?? := Γₘ ▶ Eₘ ^ wk Δₘ
      -- TODO: faire un lemme séparé de ça
      (Σ^^wk~ _ (Γm , Γr) ΓΔw Δm Exw Exm
      ,
      -- TODO faire une def séparée
      ΣliftT~' _ (Γm , Γr) ΓΔw Δm Exw Exm Aw Am' , 
      -- ((M.liftT Γm (₁ Δm)(₁ Exm) (₁ Am'))
      --     , {!ΣliftT~ !}) ,
          -- liftT~ _ (Γm , Γr) _ Δm Exw Exm {Ap} Aw (liftTw Exw Δp Aw) (₁ Am') (₂ Am')  ) ,

      {-
      I have Γₘ ^ (Δₘ ▶ Aₘ') ⊢ Bₘ
      I know that
        Γₘ ^^ (Δₘ ▶ Aₘ') = ΓΔm ▶ Am
        Bm = wk_Am Am
        xm = V0
      and I want to show that:
        (Γₘ ▶ Eₘ) ^ (Δₘ ▶ Aₘ') ⊢ lift_Em Bm
        = ((Γₘ ▶ Eₘ) ^ Δₘ) ▶ Aₘ' ⊢ wk (lift_Em Bm)
      (and another equation for xm = V0)
      But to use the given equations, I need to know that ΓΔₘ = Γₘ ^^ Δₘ and Aₘ = Aₘ'
      which may be could be proven by using the fact they both relate to the same syntactic counterpart ?
      -}
      {!!}
      
    -- ( (M.liftT Γm (₁ Δm)(₁ Exm) (₁ Am')) , {!!}) ,
      -- {!pair=!}
      )
      )
      
      
      wxw
    where
      eqΓΔm : ΓΔm ≡ Σ^^~ _ (Γm , Γr) _ Δm
      eqΓΔm = prop-has-all-paths _ _
      P : (YBxm : Σ (Σ _ M.Ty) λ x → M.Tm (₁ x) (₂ x)) → Set α
      P YBxm = {!!}
             -- Var~' ((Γp ▶p .Exp ^^ wkC Δp) ▶p liftT ∣ Δp ∣ Ap)
      --   (liftT (S ∣ Δp ∣) (liftT 0 Ap)) 0 wxw
      --   (Γm M.▶ ₁ Exm M.^^ M.wkC Γm (₁ Exm) (₁ ΔAm))
      --   (M.liftT Γm (₁ ΔAm) (₁ Exm) Bm) (M.liftt Γm (₁ ΔAm) (₁ Exm) Bm xm)

  liftV~ Γm {Δp ▶p Ap} Δw Δm Exw Exm Bm (VSw .(_ ^^ Δp) Γw .Ap Aw Bp Bw xp xw) wxw xm xr = {!!}



