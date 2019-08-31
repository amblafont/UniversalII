{-# OPTIONS  --rewriting  #-}
{-
TODO: réfélchir à de meilleures preuves

This file postulates a model which enjoys some rewrite rule for some equalities, in order
to simplify the construction of the recursor from the syntax.

Note that agda does not allow (yet?) to define a record with rewrite rules. That's why we postulate it.

The postulated rewrite rules are actually satisfied for the syntax seen as a model.

It would be nice if we later only use the recursor for models which actually satisifies
these equations definitionally.



-}



open import Level
open import EqLib hiding (_∘_ ; _⁻¹ ; Π ; _$_)
open import Lib hiding (tr2)

module ModelRew {k : Level.Level}   where

open import Model

postulate
    i : Level
    j : Level
    RewCwF : CwF {i} {j}
    RewUnivΠ : UnivΠ {k = k} RewCwF

open CwF RewCwF public
open UnivΠ RewUnivΠ public

{-# REWRITE U[]  #-}

postulate
  U[]=1 : ∀ {Γ}{Δ}{σ} → U[]{Γ}{Δ}{σ} ↦ refl

{-# REWRITE U[]=1  #-}




{-# REWRITE El[]  #-}

postulate
  El[]=1 : ∀ {Γ}{Δ}{σ}{a} → El[]{Γ}{Δ}{σ}{a} ↦ refl

{-# REWRITE El[]=1  #-}




{-# REWRITE Π[]  #-}

postulate
  Π[]=1 : ∀ {Γ}{Δ}{σ}{a}{B} → Π[]{Γ}{Δ}{σ}{a}{B} ↦ refl

{-# REWRITE Π[]=1  #-}



{-# REWRITE ΠNI[]  #-}
postulate
   ΠNI[]=1 : {Γ Δ : Con} {σ : Sub Γ Δ} {T : Set k} {B : T → Ty Δ} →
     ΠNI[] {Γ}{Δ}{σ}{T}{B} ↦ refl

{-# REWRITE ΠNI[]=1  #-}



{-# REWRITE $NI[]  #-}

postulate
  $NI[]=1 : ∀ {Y}{Γ}{σ : Sub Y Γ}{T : Set k}{B : T → Ty Γ}{t : Tm Γ (ΠNI B)}{u : T} →
    $NI[] {Y}{Γ}{σ}{T}{B}{t}{u} ↦ refl

{-# REWRITE $NI[]=1  #-}




-- agda does not recognize ΠInf[] as a valid rewrite rule, but if I restates it, it is ok.
postulate
  ΠInf[]' : {Γ Δ : Con} {σ : Sub Γ Δ} {T : Set k} {B : T → Tm Δ U} →
        (((ΠInf {Δ} B) [ σ ]t) ↦ (ΠInf {Γ} {T} (λ a →    ((B a) [ σ ]t))) )

{-# REWRITE ΠInf[]'  #-}

postulate
  ΠInf[]=1 : ∀ {Γ Δ } {σ} {T} {B} →
        ΠInf[] {Γ}{Δ}{σ}{T}{B} ↦ refl

{-# REWRITE ΠInf[]=1  #-}





-- agda does not recognize $Inf[]' as a valid rewrite rule, but if I restates it, it is ok.
postulate
  $Inf[]' : ∀ {Y}{Γ}{σ : Sub Y Γ}{T : Set k}{B : T → Tm Γ U}{t : Tm Γ (El (ΠInf B))}{u : T}
        → ((t $Inf u) [ σ ]t) ≡ (t [ σ ]t) $Inf u
{-# REWRITE $Inf[]'  #-}

postulate
  $Inf[]=1 : ∀ {Y Γ σ T B t u} → $Inf[] {Y}{Γ}{σ}{T}{B}{t}{u} ↦ refl

{-# REWRITE $Inf[]=1  #-}

-- open CwF RewCwF public
-- open UnivΠ RewUnivΠ using (_$_ ; $[] ; _$NI_ ; _$Inf_ ) public
