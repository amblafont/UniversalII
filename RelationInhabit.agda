{-# OPTIONS  --rewriting  #-}

-- proof that is 
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import monlib
import Model
open import Syntax

module RelationInhabit {α} where
  open import Relation {α}
  open import RelationProp {α}
  open import RelWeakening {α}
  open import RelSubst {α}


  Ty~path : ∀ {Γp}{Γw}(Γm : Σ _ (Con~' Γp Γw)) {Ap} Aw (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    Am' → Ty~' Γp Ap Aw (₁ Γm) Am' → ₁ Am ≡ Am'

  Ty~path Γm Aw Am Am' Ar' = fst= (prop-path (TyP _ _ Aw (₁ Γm)) Am (Am' , Ar'))

  ConTy~path : ∀ {Γp Γw} (Γm : Σ _ (Con~' Γp Γw)) Γw' Γm' (Γr' : Con~' Γp Γw' Γm')
    {Ap Aw} (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm))) -- Aw'
    Am'
    → Ty~' Γp Ap Aw Γm' Am' →   (₁ Γm , ₁ Am) ≡ (Γm' , Am')
  ConTy~path = {!!}

  -- ConTy~path' : ∀ {Γp Γw} (Γm : Σ _ (Con~' Γp Γw)) Γm' Γw' (Γr' : Con~' Γp Γw' Γm')
  --   {Ap Aw} (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm))) Aw Am'
  -- → Ty~' Γp Ap Aw' Γm' Am' →   (₁ Γm , ₁ Am) ≡ (Γm' , Am')
  -- ConTy~path' = {!!}

  Con~el : ∀ Γp Γw → (Σ _ (Con~' Γp Γw))
  Ty~el : ∀ Γp Γw Ap Aw (Γm : (Σ _ (Con~' Γp Γw)))→ (Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
  Tm~el : ∀ Γp Γw Ap Aw tp tw (Γm : (Σ _ (Con~' Γp Γw))) (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    → (Σ _ (Tm~' Γp Ap tp tw (₁ Γm) (₁ Am)))
  Var~el : ∀ Γp Γw Ap Aw xp xw (Γm : (Σ _ (Con~' Γp Γw))) (Am : Σ _ (Ty~' Γp Ap Aw (₁ Γm)))
    → (Σ _ (Var~' Γp Ap xp xw (₁ Γm) (₁ Am)))

  Con~el .∙p ∙w = _ , refl
  Con~el .(Γp ▶p Ap) (▶w {Γp} Γw {Ap} Aw) =
    _ , Con~el _ Γw , Ty~el _ Γw _ Aw (Con~el _ Γw) , refl

  Ty~el Γp Γw' .Up (Uw .Γp Γw) Γm  = _ , refl
  Ty~el Γp Γw' .(ΠΠp (Elp ap) Bp) (Πw  Γw {ap} Aw {Bp} Bw) Γm =
    _ ,
    (Tm~el Γp Γw' Up (Uw Γp Γw') ap Aw Γm (_ , refl)) ,
    (Ty~el  (Γp ▶p Elp ap) (▶w Γw'  (Elw Γw' Aw)) Bp Bw
      -- (_ , tr (λ x → Σ _ (Con~' Γp x)) (prop-path (ConwP Γp) Γw' Γw) Γm , {!!} ) ) ,
      (_ , Γm , (_ ,
      Tm~el Γp Γw' Up (Uw Γp Γw') ap Aw Γm (_ , refl) , refl) , refl) ) ,
    refl
  Ty~el Γp Γw' _ (Elw Γw aw) Γm =
    _ , Tm~el Γp Γw' Up (Uw Γp Γw) _ aw Γm (_ , refl)
     ,
    refl
    -- (tr (λ x → {!!}) {!!} Γm)

  Tm~el Γp Γw Ap Aw .(V _) (vw xw) Γm Am = Var~el _ Γw _ Aw _ xw Γm Am
  Tm~el Γp Γw .(l-subT 0 u Bp) Bsw .(app t u) (appw .Γp Γw' ap aw Bp Bw t tw u uw) Γm Am
      with (Tm~el Γp Γw Up (Uw Γp Γw) ap aw Γm (M.U (₁ Γm) , refl))
  ...       | am
      with (Tm~el Γp Γw (Elp ap) (Elw Γw' aw) u uw Γm
              (M.El (₁ Γm) (₁ am) , am , refl))
         |  Ty~el (Γp ▶p Elp ap) (▶w Γw (Elw Γw aw)) Bp Bw
              ((₁ Γm M.▶ M.El (₁ Γm) (₁ am)) , Γm , (M.El (₁ Γm) (₁ am) , am , refl) , refl)
  ...    | um | Bm
      with Tm~el Γp Γw (ΠΠp (Elp ap) Bp) (Πw Γw aw Bw) t tw Γm
              (M.ΠΠ (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ Bm) , am , Bm , refl)
  ...    | tm =

  -- inferred by the las tequality
   
      transport! (M.Tm (₁ Γm))
      (Ty~path Γm Bsw Am
       (M.subT (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ um) (₁ Bm))
       (subT~ Γw Γm (Elw Γw' aw)
        (M.El (₁ Γm) (₁ am) , am , refl) Bw Bm uw um Bsw))
      (M.app (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ Bm) (₁ (tm)) (₁ um))
    ,
   (am , Bm , tm , um
    ,
   (pair=
     -- (Ty~path Γm _ Am {!!} {!!})
     (Ty~path Γm Bsw Am
        (M.subT (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ um) (₁ Bm))
        (subT~ Γw Γm {Ap = Elp ap} (Elw Γw' aw) ((M.El (₁ Γm) (₁ am)) , am , refl ) Bw Bm uw um Bsw))
        (from-transp! (M.Tm (₁ Γm))
           (Ty~path Γm Bsw Am
            (M.subT (₁ Γm) (M.El (₁ Γm) (₁ am)) (₁ um) (₁ Bm))
            (subT~ Γw Γm {Ap = Elp ap} (Elw Γw' aw)
             (M.El (₁ Γm) (₁ am) , am , refl) Bw Bm uw um Bsw))
           {v =
            M.app (₁ Γm)
            (M.El (₁ Γm) (₁ am)) (₁ Bm) (₁ (tm)) (₁ um)}
           refl)))

  Var~el .(Γp ▶p Ap) wΓw .(liftT 0 Ap) wAw .0 (V0w Γp Γw Ap Aw) Γm Am
      with Con~el Γp Γw 
  ...  | Γm'  
      with Ty~el Γp Γw Ap Aw Γm'  
  ...  | Am' =
    -- inferred by the last hole
      -- transport! (λ x → M.Tm (₁ x) (₂ x))
      -- (ConTy~path Γm (▶w Γw Aw) (₁ Γm' M.▶ ₁ Am') (Γm' , Am' , refl) Am
      -- (M.wkT (₁ Γm') (₁ Am') (₁ Am')) (wkT~ Γw Γm' Aw Am' Aw Am' wAw))
      -- (M.V0 (₁ Γm') (₁ Am'))
      
      transport! (λ x → M.Tm (₁ x) (₂ x))
      (ConTy~path Γm (▶w Γw Aw) (₁ Γm' M.▶ ₁ Am') (Γm' , Am' , refl) {Aw = wAw} Am
      (M.wkT (₁ Γm') (₁ Am') (₁ Am')) (wkT~ Γw Γm' Aw Am' Aw Am' wAw))
      (M.V0 (₁ Γm') (₁ Am'))
      
       ,
      Γm' , Am' ,
      pair=
        (ConTy~path Γm (▶w Γw Aw) _ (Γm' , Am' , refl) {Aw = wAw} Am
         (M.wkT _ _ _) (wkT~ Γw Γm' Aw Am' Aw Am' wAw))
         (from-transp! {A = Σ _ M.Ty}(λ x → M.Tm (₁ x) (₂ x))
         (ConTy~path Γm (▶w  Γw  Aw) _
         (Γm' , Am' , refl)
         -- is it really necessary to have wkTw Aw Aw? Can't I use wAw ?
         {Aw = wAw}
         Am
         -- (wkTw Aw Aw)
         -- wAw
         (M.wkT _ _ _)
         ((wkT~ Γw Γm' Aw Am' Aw Am' wAw
         )))
         {v = M.V0 (₁ Γm') (₁ Am')}
         refl
         )
      
        
      -- (from-transp _ _ refl)
  Var~el .(Γp ▶p Ap) wΓw .(liftT 0 Bp) wAw .(S xp) (VSw Γp Γw Ap Aw Bp Bw xp xw) Γm Am 
      with (Con~el Γp Γw)
  ...  | Γm' 
      with (Ty~el Γp Γw Ap Aw Γm') | (Ty~el Γp Γw Bp Bw Γm')
  ...  | Am' | Bm'
      with (Var~el Γp Γw Bp Bw xp xw Γm' Bm')
  ...  | xm = 
      
     -- inferred from the last equality
     
-- this value was inferred from the last equalities
     transport! (λ x → M.Tm (₁ x) (₂ x))
      (ConTy~path Γm (▶w Γw Aw)
      (₁ Γm' M.▶ ₁ Am')
      (Γm' , Am' , refl)
      {Aw = wAw} Am
      (M.wkT (₁ Γm') (₁ Am') (₁ Bm'))
      (wkT~ Γw Γm' Aw Am' Bw Bm' wAw))
      (M.wkt (₁ Γm') (₁ Am') (₁ Bm') (₁ xm)) 
      ,
     Γm' , (Am' , (Bm' , (xm ,
     pair=
        (ConTy~path Γm (▶w Γw Aw) _
          (Γm' , (Am' , refl)) {Aw = wAw} Am
          -- or wkTw .. .. ?
          -- wAw
          (M.wkT _ _ _)
          (wkT~ Γw Γm' Aw Am' Bw Bm' wAw))
        (
        (from-transp! {A = Σ _ M.Ty}(λ x → M.Tm (₁ x) (₂ x))
          (ConTy~path Γm (▶w Γw Aw) _
            (Γm' , (Am' , refl)) {Aw = wAw} Am
              -- or wkTw .. .. ?
              -- wAw
              (M.wkT _ _ _)
            (wkT~ Γw Γm' Aw Am' Bw Bm' wAw))
        {v = (M.wkt (₁ Γm') (₁ Am') (₁ Bm') (₁ xm))} 
        )
        refl
        )
     )))
