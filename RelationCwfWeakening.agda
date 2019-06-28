{-# OPTIONS  --rewriting --allow-unsolved-metas #-}


-- proof #~el
open import Level
open import Hott renaming ( _∙_ to _◾_ ;  transport to tr ; fst to ₁ ; snd to ₂) hiding (_↦_)
open import monlib
open import Syntax as S

module RelationCwfWeakening {k : Level} where


import ModelCwf {k = k} as M
open import RelationCwf



{-

Suppose that Γ ^^ Δ ⊢ and Γ ⊢ E
The following function computes both Γ ▶ E ^^ wk_E Δ and a substitution
from this context to Γ ^^ Δ.
I don't see how to avoid constructing these two components simultaneously

-}
ΣwkTel⇒ᵐ : 
  ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    (Em : M.Ty (₁ Γm))
        {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw)) →
        ∃ λ T → M.Sub T (₁ Δm)


ΣwkTel⇒ᵐ {Γ} {Γw} Γm Em {∙p} {Δw} Δm
  = (₁ Γm M.▶ Em) , (tr (M.Sub _) (ConPh Γm Δm ) M.wk)
ΣwkTel⇒ᵐ {Γ} {Γw} Γm  Em {Δ ▶p A} {▶w Δw Aw} (_ , Δm , Am , refl)
  =
  (₁ (ΣwkTel⇒ᵐ Γm Em Δm) M.▶ ₁ Am M.[ ₂ (ΣwkTel⇒ᵐ Γm Em Δm) ]T)
   , (₂ (ΣwkTel⇒ᵐ Γm Em Δm) M.^ (₁ Am))

wkTelᵐ : 
  ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    (Em : M.Ty (₁ Γm))
        {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw)) →
        M.Con
wkTelᵐ Γm Em Δm = ₁ (ΣwkTel⇒ᵐ Γm Em Δm)

wkTelSᵐ : 
  ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    (Em : M.Ty (₁ Γm))
        {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw)) →
        M.Sub (wkTelᵐ Γm Em Δm) (₁ Δm)
wkTelSᵐ Γm Em Δm = ₂ (ΣwkTel⇒ᵐ Γm Em Δm)

-- wkTelSᵐ∙ Γm Em rewrite (ConPh Γm Γm) = refl
wkTelSᵐ∙ :
  ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    (Em : M.Ty (₁ Γm)) → M.Sub (₁ Γm M.▶ Em) (₁ Γm)

wkTelSᵐ∙ Γm Em = wkTelSᵐ Γm Em {Δ = ∙p} Γm 

-- this uses UIP
wkTelSᵐ∙= :
  ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    (Em : M.Ty (₁ Γm)) →
    wkTelSᵐ∙ Γm Em  ≡ M.wk
-- this uses UIP
wkTelSᵐ∙= Γm Em rewrite (ConPh Γm Γm) = refl

-- analogous to lift-lift* of the syntax
lift-wkTᵐ : 
    ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
        {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw))
        {A}{Aw : Γ ^^ Δ ⊢ A}(Am : ∃ (Ty~ Aw))
         Bm
    {Em : M.Ty (₁ Γm)}
         →

   (( Bm M.[ M.wk ]T) M.[ wkTelSᵐ Γm Em {Δ = Δ ▶p A}{▶w Δw Aw} (Σ▶~ Δm Am) ]T) ≡ (( Bm M.[ wkTelSᵐ Γm Em Δm ]T) M.[ M.wk ]T)

lift-wkTᵐ {Γ}{Γw} Γm {Δ}{Δw} Δm  Am Bm{Em} =
  M.[][]T=∘ Bm M.wk∘^ 

wkTel~ :
  ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
    -- {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ {Γp = Γ} Δw {₁ Γm}))
        {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw))
        -- (Γ≤Δ : ₁ Γm M.≤ ₁ Δm)
    →
    Con~ {Γp = Γ ▶p E ^^ wkTel Δ}(wkTelw {Γp = Γ} Ew Δ Δw)
    (wkTelᵐ Γm (₁ Em) Δm)

liftT~ :
    ∀ {Γ}{Γw :  Γ ⊢}(Γm : ∃ (Con~ Γw) )
    {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
    {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw))
    {A}{Aw : (Γ ^^ Δ) ⊢ A}(Am : ∃ (Ty~ Aw {(₁ Δm)})) →
    Ty~ (liftTw Ew Δ Aw) (₁ Am M.[ wkTelSᵐ Γm (₁ Em) Δm ]T)

liftt~ :
  ∀ {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw) )
  {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
    {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw))
  {t}{A}{tw : (Γ ^^ Δ) ⊢ t ∈ A}
  {Am : M.Ty  ( (₁ Δm))}(tm : ∃ (Tm~ tw { (₁ Δm)}{Am} )) →
  Tm~ (lifttw Ew Δ tw) (₁ tm M.[ wkTelSᵐ Γm (₁ Em) Δm ]t)

liftV~ :
  ∀ {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw) )
  {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
    {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Con~ Δw))
  {x}{A}{xw : (Γ ^^ Δ) ⊢ x ∈v A}
  {Am : M.Ty  ( (₁ Δm))}(tm : ∃ (Var~ xw { (₁ Δm)}{Am} )) →
  Var~ (liftVw Ew Δ xw) (₁ tm M.[ wkTelSᵐ Γm (₁ Em) Δm ]t)

  -- -- j'ai besoin que Γm soit relié pour le cas 0 des variables
  -- ∀ {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw) )
  -- {E}{Ew : Γ ⊢ E}(Em : ∃ (Ty~ Ew {₁ Γm}))
  -- {Δ }{Δw : Γ ^^ Δ ⊢}(Δm : ∃ (Tel~ {Γp = Γ} Δw {₁ Γm}))
  -- -- j'ai besoin que Am soit relié pour le cas 0 des variables
  -- -- ah bah non en fait !!TDODO

  -- -- TDOO enelever cete condition
  -- -- {A}{Aw : Tyw (Γ ^^ Δ) A}(Am : ∃ (Ty~ Aw {(₁ Γm) M.^^ (₁ Δm)}))
  -- -- {x}{xw : Varw (Γ ^^ Δ) A x}(xm : ∃ (Var~ xw {₁ Γm M.^^ (₁ Δm)}{₁ Am} )) →
  -- {x}{A}{xw : (Γ ^^ Δ) ⊢ x ∈v A}{Am :  M.Ty  ((₁ Γm) M.^^ (₁ Δm))}(xm : ∃ (Var~ xw {₁ Γm M.^^ (₁ Δm)}{Am} )) →
  -- Var~ (liftVw Ew Δ xw) (M.liftt (₁ Δm) (₁ Em) (₁ xm))

-- recursion on Δ
-- wkTel~ {Γ} {Γw} Γm {E} {Ew} Em {Δ}{Δw}Δm = {!Δ!}
wkTel~ {Γ} {Γw} Γm {E} {Ew} Em {∙p} {Δw} Δm 
  rewrite prop-has-all-paths Γw Δw
    | prop-path (ConP Δw) Γm Δm
     =
  Δm , Em , refl

wkTel~ {Γ} {Γw} Γm {E} {Ew} Em {Δ ▶p A} {▶w Δw Aw} (_ , Δm , Am , refl) =
   ( (_ , wkTel~ Γm Em Δm)) ,
     (_ , liftT~ Γm Em Δm Am) ,
     refl

-- liftT~ {Γ}{Γw}Γm{E}{Ew}Em{Δ}{Δw}Δm {T}{Tw}Tm = {!Tw!}
-- liftT~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.Up} {Uw Γw₁} Tm = {!!}
liftT~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.Up} {Uw  Γw₁} (_ , Level.lift refl) = Level.lift refl
-- liftT~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(ΠΠp _ _)} {Πw Γw₁ Aw Tw} Tm = {!!}
liftT~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(ΠΠp ( _) _)} {Πw Γw Aw Bw} (_ , am , Bm , refl)
  rewrite prop-has-all-paths Δw Γw
  =
  (_ , (liftt~ Γm Em Δm {tw = Aw} am)) ,
  (_ ,
     (liftT~ Γm Em {Δw = ▶w Γw (Elw Γw Aw)}
      (_ , Δm , (_ , am , refl) , refl)
      Bm)) ,
  refl
liftT~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm  {_} {ΠNIw Γw {T}{Bp} Bw} (_ , Bm , refl) =
  (λ a →  _ , liftT~ Γm Em Δm (Bm a)) ,
   refl

liftT~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(Elp _)} {Elw Γw aw} (_ , am , refl) =
  (_ , (liftt~ Γm Em Δm {tw = aw} am)) ,
  refl


-- liftt~ {Γ}{Γw}Γm{E}{Ew}Em{Δ}{Δw}Δm{z}{T}{zw}{Tm}zm = {!!}
liftt~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(V _)} {T} {vw xw} {Tm} zm = liftV~ Γm Em Δm  zm

liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(app _ _)} {.(_ [ 0 ↦ _ ]T)} {appw Γw aw {Bp}Bw tw {u}uw} {Tm}
 (_ , am , Bm , tm , um , refl , refl)
  rewrite (lift+[↦]T 0 ∣ Δ ∣ u Bp)
    |  prop-has-all-paths Δw Γw
 = 
   (_ , liftt~ Γm Em Δm {tw = aw} am) ,
  (_ , liftT~ Γm Em {Δw = ▶w Γw (Elw Γw aw)}
        (_ , Δm , (_ , am , refl) , refl)
          Bm) ,
  (_ , liftt~ Γm Em Δm {tw = tw} tm) ,
  (_ , liftt~ Γm Em Δm {tw = uw} um) ,
   -- M.lift-subT (₁ Δm) {B = ₁ Bm}{t = ₁ um}
    M.[][]T=∘ (₁ Bm) (M.<>∘ ◾ (! M.^∘<>)) ,
    ≅↓ (↓≅ ( M.$[] {σ =   wkTelSᵐ Γm (₁ Em) Δm }{t = ₁ tm}{u = ₁ um}))
   
 

-- liftt~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(appNI _ u)} {.(_ u)} {appNIw Γw₁ Bw zw u} {Tm} zm = {!!}
liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {appNI t _} {_} {appNIw Γw {T} {Bp} Bw tw u} {_}
    (_ , Bm , tm , refl , refl)
  = (λ a → _ , liftT~ Γm Em Δm (Bm a)) ,
  (_ , liftt~ Γm Em Δm {tw = tw} tm) ,
  refl , refl
liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {appNI t _} {_} {appInfw Γw {T} {Bp} Bw tw u} {_}
  (_ , Bm , tm , refl , refl)
 =
 (λ a → _ , liftt~ Γm Em Δm {tw = Bw a} (Bm a)) ,
    (_ , liftt~ Γm Em Δm {tw = tw} tm) ,
      (refl , refl)

-- liftt~ {Γ} {Γw} Γm {E} {Ew} Em {Δ} {Δw} Δm {.(ΠInf _)} {.Up} {ΠInfw Γw₁ Bw} {Tm} zm = {!!}
liftt~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ} {Δw} Δm {ΠInf B} {_} {ΠInfw Γw {T}{Bp} Bw} {_}
  (_ , Bm , refl , refl)
  = (λ a →  _ , liftt~ Γm Em Δm {tw = Bw a}(Bm a)) , refl , refl


liftV~ {.(_ ▶p _)} {Γw'} Γm {E} {Ew} Em {∙p} {Δw} Δm {.0} {.(liftT 0 _)} {V0w Γw Aw} {Am} 
  (xm , Γm' , Am' , eC , eE , ex)
  rewrite
    prop-has-all-paths Γw' (▶w Γw Aw)
    | prop-has-all-paths Δw (▶w Γw Aw)
    | (prop-path (ConP (▶w Γw Aw)) Γm (Σ▶~ Γm' Am') )
    | (prop-path (ConP (▶w Γw Aw)) Δm (Σ▶~ Γm' Am') )
    | uip eC refl
    | eE | ex
    -- this uses UIP
    | ConPh {Γw = (▶w Γw Aw)}{Γw' = (▶w Γw Aw)}
      ((₁ Γm' M.▶ ₁ Am') , Γm' , Am' , refl)
      ((₁ Γm' M.▶ ₁ Am') , Γm' , Am' , refl)
   =
    ( _ , Γm' , Am' , refl) ,
   Em  ,
   ((₁ Am' M.[ M.wk ]T) ,  coe helper1 (liftT~ Γm' Am' {∙p} {Γw} Γm' Am') )
    ,
      ((_ , Γm' , Am' , refl , refl , refl)) ,
     (refl ,
     refl , refl )

   where
     helper1 : Ty~ (liftTw Aw ∙p Aw) (₁ Am' M.[ wkTelSᵐ∙ Γm' (₁ Am') ]T) ≡ Ty~ (liftTw Aw ∙p Aw) (₁ Am' M.[ M.wk ]T)
     helper1 rewrite ConPh Γm' Γm' = refl
   

liftV~ {.(_ ▶p _)} {Γw} Γm {E} {Ew} Em {∙p} {Δw} (_ , Δr)   {xw = VSw Γw' Aw Bw zw}  
 (_ , Γm' , Am' , Bm , xm , refl , refl , refl)
  rewrite 
    prop-has-all-paths Γw (▶w Γw' Aw)
    | (prop-path (ConP (▶w Γw' Aw)) Γm (Σ▶~ Γm' Am') )
    | (ConPh ((₁ Γm' M.▶ ₁ Am') , Γm' , Am' , refl)
             ((₁ Γm' M.▶ ₁ Am') , Δr)
             )
  = (_ , Γm' , Am' , refl) ,
    Em ,
    ((₁ Bm M.[ M.wk ]T) , coe B~= ((liftT~ Γm' Am' {∙p} {Γw'} Γm' Bm))) ,
    (_ , Γm' , Am' , Bm , xm , refl , refl , refl) ,
    refl , refl , refl 
    where
      B~= :
         Ty~ (liftTw Aw ∙p Bw) (₁ Bm M.[  wkTelSᵐ∙ Γm' (₁ Am') ]T)
         ≡
         Ty~ (liftTw Aw ∙p Bw) (₁ Bm M.[ M.wk ]T)
      -- B~= : Ty~ (liftTw Aw ∙p Aw) (₁ Bm' M.[ wkTelSᵐ∙ Γm' (₁ Am') ]T) ≡ Ty~ (liftTw Aw ∙p Aw) (₁ Am' M.[ M.wk ]T)
      B~= rewrite ConPh Γm' Γm' = refl

-- liftV~ {Γ} {Γw} Γm {E} {Ew} Em {Δ ▶p A} {Δw} Δm {z} {T} {zw} {Tm} zm = {!zw!}

liftV~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ ▶p C} {▶w Δw Cw} (_ , (Δm , Am , refl)) {.0} {.(liftT 0 _)} {V0w Γw Aw} {Tm}
  (zm , Γm' , Am' , eC , eT , ez)
  rewrite (lift-liftT 0 ∣ Δ ∣ C)
  | prop-has-all-paths Δw Γw
  | prop-path (ConP Γw) Γm' Δm
  | prop-has-all-paths Cw Aw
  | prop-path (TyP Aw _) Am' Am
  | uip eC refl
  | eT | ez
  =
   (_ , wkTel~ Γm Em {Δ} Δm) ,
   (((₁ Am M.[ wkTelSᵐ Γm (₁ Em) Δm ]T) , liftT~ Γm Em Δm Am)) ,
   refl ,
     lift-wkTᵐ Γm Δm Am (₁ Am)    ,
    ≅↓ (↓≅ (M.vz[^] {A = ₁ Am}))
    -- ≅↓ (↓≅ (liftV0 Γm (₁ Em)Δm Am))

liftV~ {Γ} {Γw'} Γm {E} {Ew} Em {Δ ▶p C} {▶w Δw Cw} (_ , Δm , Cm , refl) {_}
   {.(liftT 0 _)} {VSw Γw Aw {Bp}Bw zw} {Am} (zm , Γm' , Am' , Bm , xm , eC , eE , ez )
   rewrite
    prop-has-all-paths Δw Γw
  | prop-path (ConP Γw) Γm' Δm

  | prop-has-all-paths Cw Aw
  | prop-path (TyP Aw _) Cm Am'

  | uip eC refl
  | eE | ez
  | (lift-liftT 0 ∣ Δ ∣ Bp)
   =
  (_ , wkTel~ Γm Em {Δ} Δm) ,
  (( _ , (liftT~ Γm Em Δm Am')) ,
  (_ , liftT~ Γm Em Δm Bm) ,
  (_ , liftV~ Γm Em Δm xm) ,
  refl ,
   lift-wkTᵐ Γm Δm Am' (₁ Bm)   ,
   -- lift-wkt
   ≅↓ (↓≅  (M.[][]t=∘ (₁ xm) ( M.wk∘^) ))
   )

  








wkSub~ : ∀
  {Γ}{Γw : Γ ⊢}(Γm : ∃ (Con~ Γw))
  { Δ σ} {σw : Γ ⊢ σ ⇒ Δ}
  { Δm}(σm : ∃ (Sub~ σw {(₁ Γm)}{Δm}))
  {A }{Aw : Γ ⊢ A} (Am : Σ (M.Ty (₁ Γm)) (Ty~ Aw)) →
  Sub~ (wkSw σw Aw)(₁ σm M.∘ M.wk {A = ₁ Am})

wkSub~ {Γ} {Γw} Γm {.∙p} {.nil} {nilw} {_} (_ , refl , Level.lift refl) {E} {Ew} Em = refl ,  Level.lift M.εη
wkSub~ {Γ} {Γw} Γm {.(_ ▶p _)} {_} {,sw Δw {σp = σp} σw {Ap = Ap} Aw {tp = tp} tw}  {_}
  (_ , Δm , σm , Am , tm , refl , refl)
    {E} {Ew} Em
  = Δm ,
    (_ , wkSub~ Γm σm Em) ,
    (Am ,
    tm' ,
    refl ,
    M.,∘ etm)
    where
      tm'₁ : (M.Tm ((₁ Γm) M.▶ (₁ Em)) (₁ Am M.[ ₁ σm M.∘ M.wk ]T))
      tm'₁ = tr (M.Tm _) (M.[][]T {A = ₁ Am}) ((₁ tm) M.[ M.wk ]t)
      tm'₂ :  Tm~
              (transport! (λ A → (Γ ▶p E) ⊢ (liftt 0 tp) ∈ A ) ([wkS]T σp Ap)
                (wktw Ew tw))
              tm'₁
      tm' = tm'₁ , tm'₂
      etm = from-transp _ _ refl
      suite : Tm~ (lifttw Ew ∙p tw) (₁ tm M.[ tr (M.Sub _) (ConPh Γm Γm) M.wk ]t)
         → Tm~ (lifttw Ew ∙p tw) (₁ tm M.[ M.wk ]t) 
      suite rewrite uip (ConPh Γm Γm) refl  = λ x → x
      tm'₂ rewrite [wkS]T σp Ap
        -- |
         -- prop-path (raise-level ⟨-2⟩ has-level-apply-instance) (prop-has-all-paths Γw Γw) refl
          =
        tr-over (λ A t → Tm~ (lifttw Ew ∙p tw) {Am = A} t)
           etm
           (suite( liftt~ Γm {Ew = Ew}Em{∙p} {Δw = Γw} Γm {tw = tw}tm  ))

