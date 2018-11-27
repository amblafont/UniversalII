-- In this file, we postulate a morphism (with rew rules) between the syntax and the model with rewrite rules
-- I put (at least) the rewrite rules that are satisfied by the one I constructed
-- later we will show that it is unique
{-# OPTIONS  --rewriting   #-}
open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
open import ModelRecord
open import monlib
open import Syntax
open import SyntaxIsRecord
open import SyntaxIsRecord2
open import ModelRewIsRecord 
open import ModelRewIsRecord2
open import ModelMorphism
import Model
open import Relation
open import RelationProp
open import RelationInhabit
open import RelWeakening
open import RelSubst
-- open import Data.String


module ModelMorRew {l} where

  -- import ModelRewIsRecord2.m2
  module N = Model {l}
  module MM = ModelRewIsRecord2.M1

  postulate
    Conᴹ : ∀ (Γ : S1.Con) → N.Con
    Telescopeᴹ : ∀ {Γ : S1.Con}(Δ : S1.Telescope Γ)  → N.Telescope (Conᴹ Γ)
    Tyᴹ : {Γ : S1.Con}(A : S1.Ty Γ) → N.Ty (Conᴹ Γ)
    Tmᴹ : {Γ : S1.Con}{A : S1.Ty Γ} (t : S1.Tm Γ A)
      → N.Tm (Conᴹ Γ) (Tyᴹ {Γ} A)

    ∙ᴹ : Conᴹ S1.∙ ↦ N.∙ 
    -- I have to split the syntax part in two components so that the rewrite rule is valid
    ▶ᴹ : ∀ Γ (Γw : Conw Γ)A (Aw : Tyw Γ A)
       → (Conᴹ ((Γ , Γw) S1.▶ (A , Aw))) ↦ (Conᴹ (Γ , Γw) N.▶ Tyᴹ (A , Aw))
    -- ▶ᴹ : ∀ (Γ : S1.Con) (A : S1.Ty Γ)
    --    → (Conᴹ (Γ S1.▶ A)) ↦ (Conᴹ Γ N.▶ Tyᴹ A)
    -- it cannot be a rewrite rule as ₂ Γ does not appear in the l.h.s.
    ^^ᴹ : ∀ Γ Δ →
      -- (Conᴹ ((Γp ^^ Δp) , Δw)) ↦ (Conᴹ (Γp , Γw) N.^^ Telescopeᴹ (Δp , Δw))
      (Conᴹ (Γ S1.^^ Δ)) ≡ (Conᴹ Γ N.^^ Telescopeᴹ Δ)
    ∙tᴹ : ∀ {Γ} → Telescopeᴹ {Γ = Γ} (S1.∙t Γ) ↦ N.∙t _
  
  {-# REWRITE ∙ᴹ  #-}
  {-# REWRITE ▶ᴹ  #-}
  {-# REWRITE ∙tᴹ  #-}
  -- {-# REWRITE ^^ᴹ  #-}


  postulate

    ▶tᴹ : ∀
      {Γp}{Γw : Conw Γp}{Δp}{Δw : Conw (Γp ^^ Δp)}{Ap}{Aw : Tyw (Γp ^^ Δp) Ap} →
       let Γ = (Γp , Γw) in
       let Δ = (Δp , Δw) in
       let A = (Ap , Aw) in
      (Telescopeᴹ {Γ = Γ} (S1._▶t_ {Γ = Γ} Δ  A)) ↦
      ((Telescopeᴹ {Γ = Γ} Δ) N.▶t tr N.Ty (^^ᴹ Γ Δ) (Tyᴹ {Γ S1.^^ Δ} A))
    
  -- Note that this one is not definitional in the inital morphism.
  {-# REWRITE ▶tᴹ  #-}

  postulate
    Uᴹ : ∀ {Γp}{Γw} →
      let Γ = (Γp , Γw) in
      (Tyᴹ {Γ} (S1.U Γ)) ↦ N.U _

  {-# REWRITE Uᴹ  #-}
  
  postulate
    Elᴹ :
      ∀ {Γp}{Γw}{Ap}{Aw} →
       let Γ = (Γp , Γw) in
       let A = (Ap , Aw) in
      Tyᴹ {Γ} (S1.El Γ A) ↦ N.El _ (Tmᴹ {Γ} {S1.U Γ} A)

  {-# REWRITE Elᴹ  #-}
  postulate
    -- ΠΠᴹ : ∀ {Γ}{A : S1.Tm Γ (S1.U Γ)}{B} →
    ΠΠᴹ : ∀ {Γp}{Γw}{Ap}{Aw}{Bp}{Bw} →
      let Γ = (Γp , Γw) in
      let A = (Ap , Aw) in
      let B = (Bp , Bw) in
      Tyᴹ (S1.ΠΠ Γ A B) ↦ N.ΠΠ _ (Tmᴹ {Γ} {S1.U Γ} A)
        (Tyᴹ {Γ S1.▶ (S1.El Γ A)} B )
  {-# REWRITE ΠΠᴹ  #-}

  postulate
    wkCᴹ : ∀ Γ  E  Δ  →
       Telescopeᴹ {Γ S1.▶ E} (S1.wkC Γ E Δ) ≡  (N.wkC _ (Tyᴹ {Γ} E) (Telescopeᴹ {Γ}Δ)) 

    -- wkCᴹ : ∀ {Γp} {Γw}
    --     {Ep} {Ew}
    --     {Δp} {Δw}
    --     →
    --     let Γ = (Γp , Γw) in
    --     let E = (Ep , Ew) in
    --     let Δ = (Δp , Δw) in
      -- Telescopeᴹ {Γ S1.▶ E} (S1.wkC Γ E Δ) ≡  (N.wkC _ (Tyᴹ {Γ} E) (Telescopeᴹ {Γ}Δ))

    subTelᴹ : ∀ (Γ : S1.Con) (Ex : S1.Ty Γ) (Δ : S1.Telescope (Γ S1.▶ Ex))
      (z : S1.Tm Γ Ex) →
      Telescopeᴹ {Γ } (S1.subTel {Γ} Ex Δ z) ≡
      N.subTel (Tyᴹ {Γ} Ex) (Telescopeᴹ {Γ S1.▶ Ex} Δ) (Tmᴹ {Γ} {Ex} z)
  -- this should not be definitional
  -- {-# REWRITE wkCᴹ  #-}

  ▶wkCᴹ : ∀ Γ Δ E →
    Conᴹ (Γ S1.▶ E S1.^^ S1.wkC Γ E Δ) ≡
    (Conᴹ Γ N.▶ Tyᴹ {Γ} E N.^^ N.wkC (Conᴹ Γ) (Tyᴹ {Γ} E) (Telescopeᴹ {Γ} Δ))
  ▶wkCᴹ Γ Δ E =
     ^^ᴹ (Γ S1.▶ E)(S1.wkC Γ E Δ) ◾ ap (N._^^_ (Conᴹ Γ N.▶ Tyᴹ {Γ = Γ} E)) (wkCᴹ Γ E Δ)
    

  postulate

    liftTᴹ : 
      (Γ : Σ Conp Conw) (Δ : Σ Conp (λ Δ₁ → Conw (₁ Γ ^^ Δ₁)))
      (E : Σ Typ (Tyw (₁ Γ))) (A : Σ Typ (Tyw (₁ Γ ^^ ₁ Δ))) →
      Tyᴹ {Γ = (Γ S1.▶ E) S1.^^ (S1.wkC Γ E Δ)} (S1.liftT Γ Δ E A) ≡
      tr N.Ty
        ((! (▶wkCᴹ Γ Δ E)))
          (Model1.liftT m1 (Conᴹ Γ) (Telescopeᴹ Δ) (Tyᴹ E)
            (Model1.tr-Ty m1 (^^ᴹ Γ Δ) (Tyᴹ A)))
          
  postulate
    lifttᴹ : 
      (Γ : S1.Con) (Δ : S1.Telescope Γ) (E : S1.Ty Γ) (A : S1.Ty (Γ S1.^^ Δ) )
      (t : S1.Tm (Γ S1.^^ Δ) A) →
      Tmᴹ {(Γ S1.▶ E) S1.^^ (S1.wkC Γ E Δ)} {S1.liftT Γ Δ E A} (S1.liftt Γ Δ E A t)
      ≡
      tr2 N.Tm (! (▶wkCᴹ Γ Δ E ))
      (! (liftTᴹ Γ Δ E A))
      (MM.liftt (Conᴹ Γ) (Telescopeᴹ {Γ} Δ) (Tyᴹ {Γ} E)
      (MM.tr-Ty (^^ᴹ Γ Δ) (Tyᴹ {Γ S1.^^ Δ} A))
      (MM.tr2-Tm (^^ᴹ Γ Δ) (Tmᴹ {Γ S1.^^ Δ} {A} t)))

  -- this lemma is defined in fact in ModelMorphism
  ^^subTel : ∀  Γ  E  Δ  z  → _
  ^^subTel Γ  E  Δ  z  = ^^ᴹ Γ (S1.subTel  {Γ}  E Δ z) ◾ ap (MM._^^_ (Conᴹ Γ)) (subTelᴹ Γ E Δ z)

  postulate

    l-subTᴹ : ∀ (Γ : S1.Con)(E : S1.Ty Γ)(Δ : S1.Telescope (Γ S1.▶ E)) (z : S1.Tm Γ E)
      (A : S1.Ty ((Γ S1.▶ E) S1.^^ Δ)) →
      Tyᴹ {Γ S1.^^ (S1.subTel {Γ} E Δ z)} (S1.l-subT {Γ} E Δ z A)
      ≡ MM.tr-Ty (! (^^subTel Γ E Δ z)) 
      (N.l-subT (Tyᴹ {Γ} E)  (Telescopeᴹ {Γ S1.▶ E} Δ) (Tmᴹ {Γ}{E} z)
      (MM.tr-Ty ( ^^ᴹ (Γ S1.▶ E) Δ ) (Tyᴹ {(Γ S1.▶ E) S1.^^ Δ} A)))

    l-subtᴹ : ∀ (Γ : S1.Con)(E : S1.Ty Γ)(Δ : S1.Telescope (Γ S1.▶ E)) (z : S1.Tm Γ E)
      (A : S1.Ty ((Γ S1.▶ E) S1.^^ Δ))(t : S1.Tm ((Γ S1.▶ E) S1.^^ Δ) A) →
      Tmᴹ {Γ S1.^^ (S1.subTel {Γ} E Δ z)} {S1.l-subT {Γ} E Δ z A}(S1.l-subt {Γ} E Δ z A t) ≡
      tr2 N.Tm
      (! (^^subTel Γ E Δ z))
      (! (l-subTᴹ Γ E Δ z A))
      (MM.l-subt (Tyᴹ {Γ} E) (Telescopeᴹ {Γ S1.▶ E} Δ) (Tmᴹ {Γ} {E} z)
      (MM.tr-Ty (^^ᴹ (Γ S1.▶ E) Δ) (Tyᴹ {(Γ S1.▶ E) S1.^^ Δ} A))
      (MM.tr2-Tm (^^ᴹ (Γ S1.▶ E) Δ) (Tmᴹ {(Γ S1.▶ E) S1.^^ Δ} {A} t)))







  mor1 : ModelMorphism1 syntax2 (m2 {l})
  mor1 = record
           { Conᴹ = Conᴹ
           ; Telescopeᴹ = Telescopeᴹ
           ; Tyᴹ = Tyᴹ
           ; Tmᴹ = Tmᴹ
           ; ∙ᴹ = refl
           ; ▶ᴹ = refl
           ; ^^ᴹ = λ {Γ}{Δ}→ ^^ᴹ Γ Δ
           ; ∙tᴹ = refl
           ; ▶tᴹ = refl
           ; Uᴹ = refl
           ; Elᴹ = refl
           ; ΠΠᴹ = refl

           ; wkCᴹ = λ {Γ}{E}{Δ} → wkCᴹ Γ E Δ
           ; liftTᴹ = λ {Γ}{E}{Δ}{A} → liftTᴹ Γ E Δ A
           ; lifttᴹ = λ {Γ}{E} {Δ} {A} t → lifttᴹ Γ E Δ A t
           ; subTelᴹ = λ {Γ}{E}{Δ}{z} → subTelᴹ Γ E Δ z
           ; l-subTᴹ = λ {Γ}{E}{Δ}{z}{A} → l-subTᴹ Γ E Δ z A
           ; l-subtᴹ = λ {Γ}{E}{Δ}{z}{A}{t} → l-subtᴹ Γ E Δ z A t
           }

  -- now the second part of ModelMorphism
  postulate
    -- iniV0ᴹ : ∀ (Γ : S1.Con)(A : S1.Ty Γ) →
    V0ᴹ : ∀ {Γp}{Γw}{Ap}{Aw} →
     let Γ = Γp , Γw in
     let A = Ap , Aw in
       Tmᴹ {Γ S1.▶ A}{S1.wkT Γ A A}(S1.V0 Γ A)
       ↦
      (MM.tr-Tm (! (wkTᴹ syntax2 m2 mor1 {Γ = Γ}{A}{A}))
      (N.V0  (Conᴹ Γ) (Tyᴹ {Γ} A))) 

    appᴹ  :
      ∀ uu →
        (Γ : S1.Con )
        (A : S1.Tm Γ (S1.U Γ))
        (B : S1.Ty (Γ S1.▶ (S1.El Γ A)))
        (t : S1.Tm Γ (S1.ΠΠ Γ A B))
        (u : S1.Tm Γ (S1.El Γ A))
        →
        -- ∀ uu →
        -- ∀ {Γp}{Γw}
        --  {Ap}{Aw} 
        --  {Bp}{Bw} 
        --  {tp}{tw} 
        --  {up}{uw}  →
        --  let Γ = Γp , Γw in
        --  let A = Ap , Aw in
        --  let B = Bp , Bw in
        --  let t = tp , tw in
        --  let u = up , uw in
          
          Tmᴹ {Γ} {S1.subT Γ (S1.El Γ A) u B}  (S1.app Γ A B t u)
          ≡
          MM.tr-Tm 
          (! (subTᴹ syntax2 m2 mor1 uu {Γ}{S1.El Γ A}{u}{B}))
          -- (! (subTᴹ syntax2 m2 mor1 unit' {Γ}{S1.El Γ A}{u}{B}))
          (MM.app (Conᴹ Γ)
            (Tmᴹ {Γ} {S1.U Γ} A)
            (Tyᴹ {Γ S1.▶ (S1.El Γ A)} B)
            (Tmᴹ {Γ}{S1.ΠΠ Γ A B}t)
            (Tmᴹ {Γ}{S1.El Γ A} u))
            

  -- this is not definitional in the initial morphism
  {-# REWRITE V0ᴹ  #-}
  -- this is not definitional in the initial morphism
  -- {-# REWRITE appᴹ  #-}

  mor2 : ModelMorphism2 syntax2 (m2 {l}) mor1
  mor2 = record { V0ᴹ = refl ;
    appᴹ = λ uu {Γ}{A}{B}{t}{u} →  appᴹ uu Γ A B t u 
      
      }

