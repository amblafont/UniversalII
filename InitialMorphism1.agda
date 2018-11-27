-- In this file, we begin the proof that we have a morphism from the syntax to the postulated model with rewrite rules
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
-- import Model
open import Relation
open import RelationProp
open import RelationInhabit
open import RelWeakening
open import RelSubst
-- open import Data.String


module InitialMorphism1 {l} where

  import Model 
  module N = Model {l}


  module MM = Model1 (m1 {l})
  -- module S = Model1 syntax1
  -- module N' = Model2 (m2 {l})
  -- module S' = Model2 syntax2

  -- the initial morphism

  ΣmorCon : ∀ (Γ : Σ _ Conw) → Σ N.Con (Con~' _ _ )
  ΣmorCon Γ = Con~el _ (₂ Γ)

  morCon : ∀ (Γ : S1.Con) → N.Con
  morCon Γ = ₁ (ΣmorCon Γ)

  ΣmorTel : ∀ {Γ : S1.Con}(Δ : S1.Telescope Γ)  → Σ (N.Telescope (morCon Γ)) (Telescope~ _ _ _  )
  ΣmorTel {Γ} Δ = (Telescope~el _ (₂ Γ) _ (₂ Δ) (ΣmorCon Γ))

  morTel : ∀ {Γ : S1.Con}(Δ : S1.Telescope Γ)  → N.Telescope (morCon Γ)
  morTel {Γ} Δ = ₁ (ΣmorTel {Γ} Δ)

  ΣmorTy : {Γ : S1.Con}(A : S1.Ty Γ) → Σ (N.Ty (morCon Γ)) _
  ΣmorTy {Γ} A =  (Ty~el _ _ _ (₂ A) (ΣmorCon Γ))

  morTy : {Γ : S1.Con}(A : S1.Ty Γ) → N.Ty (morCon Γ)
  morTy {Γ} A =  ₁ (ΣmorTy {Γ} A)

  ΣmorTm : {Γ : S1.Con}{A : S1.Ty Γ} (t : S1.Tm Γ A)
    → Σ (N.Tm (morCon Γ) (morTy {Γ} A)) _
  ΣmorTm {Γ} {A} t = (Tm~el _ _ _ _ _ (₂ t)
    (ΣmorCon Γ)
    (ΣmorTy {Γ} A))




  morTm : {Γ : S1.Con}{A : S1.Ty Γ} (t : S1.Tm Γ A)
    → N.Tm (morCon Γ) (morTy {Γ} A)
  morTm {Γ} {A} t = ₁ (ΣmorTm {Γ}{A} t)








  Con~path : ∀ Γ (Γm : Σ _ (Con~' (₁ Γ) (₂ Γ))) Γm' → Con~' {l} (₁ Γ) (₂ Γ) Γm' → ₁ Γm ≡ Γm'
  Con~path Γ Γm Γm' Γr = fst= (prop-path (ConP _ (₂ Γ)) Γm (Γm' , Γr))

  Telescope~path : ∀ Γ (Γm : Σ _ (Con~' (₁ Γ) (₂ Γ))) Δ (Δm : Σ _ (Telescope~ {l} {Γp = ₁ Γ}  (₁ Δ)(₂ Δ)  (₁ Γm)))
    Δm' → Telescope~ _ (₂ Δ) (₁ Γm) Δm' → ₁ Δm ≡ Δm'

  Telescope~path Γ Γm Δ Δm Δm' Δr' = fst= (prop-path (TelescopeP _ _ (₂ Δ) (₁ Γm)) Δm (Δm' , Δr'))

  Ty~path' : ∀ Γ (Γm : Σ _ (Con~' (₁ Γ) (₂ Γ))) A (Am : Σ _ (Ty~' {l} (₁ Γ)  (₁ A)(₂ A)  (₁ Γm)))
    Am' → Ty~' _ _ (₂ A) (₁ Γm) Am' → ₁ Am ≡ Am'

  Ty~path' Γ Γm A Am Am' Ar' = fst= (prop-path (TyP _ _ (₂ A) (₁ Γm)) Am (Am' , Ar'))

  Tm~path' : ∀ Γ (Γm : Σ _ (Con~' (₁ Γ) (₂ Γ))) A (Am : Σ _ (Ty~' {l} (₁ Γ)  (₁ A)(₂ A)  (₁ Γm)))
    t (tm : Σ _ (Tm~' {l} (₁ Γ)  (₁ A)(₁ t)(₂ t)  (₁ Γm)(₁ Am) )) 
    tm'
      → Tm~' _  (₁ A) _ (₂ t)(₁ Γm)(₁ Am) tm' → ₁ tm ≡ tm'

  Tm~path' Γ Γm A Am  t tm tm' tr' =  fst= (prop-path (TmP _ _ _ (₂ t) (₁ Γm)(₁ Am)) tm (tm' , tr'))









  ini^^ᴹ : (Γ : Σ Conp Conw) (Δ : Σ Conp (λ Δ₁ → Conw (₁ Γ ^^ Δ₁)))
          → ₁ (Con~el (₁ Γ ^^ ₁ Δ) (₂ Δ)) ≡
            (
            (₁ (Con~el (₁ Γ) (₂ Γ)) N.^^
            ₁ (Telescope~el (₁ Γ) (₂ Γ) (₁ Δ) (₂ Δ) (Con~el (₁ Γ) (₂ Γ))))
          ) 
  ini^^ᴹ Γ Δ   = 
    -- myadmit 0
    Con~path _ (Con~el (₁ Γ ^^ ₁ Δ) (₂ Δ)) _
      (^^~ (₂ Γ) (Con~el (₁ Γ) (₂ Γ)) (₂ Δ)
      (Telescope~el _ (₂ Γ) _ (₂ Δ) (Con~el (₁ Γ) (₂ Γ)) )
      )

  ini▶tᴹ : {Γ : S1.Con}
     {Δ : S1.Telescope Γ}
     {A : S1.Ty (Γ S1.^^ Δ)}
     → morTel {Γ = Γ} (S1._▶t_ {Γ} Δ A)
      ≡
      (morTel {Γ = Γ} Δ N.▶t tr N.Ty (ini^^ᴹ Γ Δ) (morTy {Γ = Γ S1.^^ Δ} A))

  ini▶tᴹ {Γ}{Δ}{A} =
    -- myadmit 1
    
    Telescope~path Γ (ΣmorCon Γ) (S1._▶t_ {Γ} Δ A) 
      (ΣmorTel {Γ = Γ}(S1._▶t_ {Γ} Δ A))
      (morTel {Γ = Γ} Δ N.▶t tr N.Ty (ini^^ᴹ Γ Δ) (morTy {Γ = Γ S1.^^ Δ} A))
      (ΣmorTel {Γ = Γ}Δ , (_ ,
      tr2 (Ty~' (₁ Γ ^^ ₁ Δ) (₁ A) (₂ A)) (ini^^ᴹ Γ Δ) refl (₂ (ΣmorTy {Γ = Γ S1.^^ Δ} A)))
        , refl)

-- explicit arguments because agda fails to infer them
  iniwkCᴹ : (Γ : S1.Con) (E : S1.Ty Γ)
        (Δ : S1.Telescope Γ) →
        morTel {Γ = Γ S1.▶ E} (S1.wkC Γ E Δ) ≡
        MM.wkC (morCon Γ) (morTy {Γ = Γ} E) (morTel {Γ = Γ} Δ)

  iniwkCᴹ Γ E Δ =
    -- myadmit 2
     Telescope~path (S1._▶_ Γ E) ((morCon Γ N.▶ morTy {Γ = Γ} E) ,
        ( ΣmorCon Γ) , ΣmorTy {Γ = Γ} E , refl)
       (S1.wkC Γ E Δ) (ΣmorTel {Γ = S1._▶_ Γ E} (S1.wkC Γ E Δ))
       (N.wkC (morCon Γ) (morTy {Γ = Γ} E) (morTel {Γ = Γ} Δ))
        (wkTelescope~ (₂ Γ) (ΣmorCon Γ) (₂ Δ) (ΣmorTel {Γ = Γ} Δ) (₂ E)
        (ΣmorTy {Γ = Γ} E))
   -- this was already defined in ModelMorphism
  ini▶wkCᴹ : ∀ Γ Δ E →
    morCon (Γ S1.▶ E S1.^^ S1.wkC Γ E Δ) ≡
    (morCon Γ N.▶ morTy {Γ} E N.^^ N.wkC (morCon Γ) (morTy {Γ} E) (morTel {Γ} Δ))
  ini▶wkCᴹ Γ Δ E =
      ini^^ᴹ (Γ S1.▶ E)(S1.wkC Γ E Δ) ◾ ap (MM._^^_ (morCon Γ MM.▶ morTy {Γ = Γ} E)) (iniwkCᴹ Γ E Δ)


  iniliftTᴹ : 
    (Γ : Σ Conp Conw) (Δ : Σ Conp (λ Δ₁ → Conw (₁ Γ ^^ Δ₁)))
    (E : Σ Typ (Tyw (₁ Γ))) (A : Σ Typ (Tyw (₁ Γ ^^ ₁ Δ))) →
    morTy {Γ = (Γ S1.▶ E) S1.^^ (S1.wkC Γ E Δ)} (S1.liftT Γ Δ E A) ≡
    MM.tr-Ty
    (! (ini▶wkCᴹ Γ Δ E ))

    (MM.liftT (morCon Γ) (morTel {Γ = Γ} Δ) (morTy {Γ = Γ} E)
      (MM.tr-Ty (ini^^ᴹ Γ Δ)  (morTy {Γ = Γ S1.^^ Δ} A)))

  iniliftTᴹ Γ Δ E A =
    -- myadmit 3
    Ty~path' _ (ΣmorCon ((Γ S1.▶ E) S1.^^ (S1.wkC Γ E Δ))) _ (ΣmorTy {Γ = (Γ S1.▶ E) S1.^^ (S1.wkC Γ E Δ)}(S1.liftT Γ Δ E A))
     _
     (
     tr2 (Ty~' _ _ _)
     (! (ini^^ᴹ (Γ S1.▶ E)(S1.wkC Γ E Δ) ◾ ap (MM._^^_ (morCon Γ MM.▶ morTy {Γ = Γ} E)) (iniwkCᴹ  Γ  E  Δ )))
     refl
      (liftT~ (₂ Γ) (ΣmorCon Γ) (₂ Δ) (ΣmorTel {Γ} Δ) _ (ΣmorTy {Γ} E)
     (₂ A) (liftTw (₂ E) (₁ Δ) (₂ A)) (tr N.Ty (ini^^ᴹ  Γ  Δ ) (₁ (ΣmorTy {Γ = Γ S1.^^ Δ}  A)))
     (tr2 (Ty~' _ _ _) (ini^^ᴹ  Γ  Δ ) refl (₂ (ΣmorTy A))))
       )
     

  inilifttᴹ : 
    (Γ : S1.Con) (Δ : S1.Telescope Γ) (E : S1.Ty Γ) (A : S1.Ty (Γ S1.^^ Δ) )
    (t : S1.Tm (Γ S1.^^ Δ) A) →
    morTm {(Γ S1.▶ E) S1.^^ (S1.wkC Γ E Δ)} {S1.liftT Γ Δ E A} (S1.liftt Γ Δ E A t)
      ≡
      tr2 N.Tm 
      (! (ini▶wkCᴹ Γ Δ E ))
      (! (iniliftTᴹ Γ Δ E A))
      (MM.liftt (morCon Γ) (morTel {Γ} Δ) (morTy {Γ} E)
      (MM.tr-Ty (ini^^ᴹ Γ Δ) (morTy {Γ S1.^^ Δ} A))
      (MM.tr2-Tm (ini^^ᴹ Γ Δ) (morTm {Γ S1.^^ Δ} {A} t)))
      
  inilifttᴹ  Γ  Δ  E  A  t  =
  -- myadmit 4
    Tm~path' _ (ΣmorCon ΓEΔ) lA
    lAm lt
    ltm
    _
    (tr3 (Tm~' (₁ ΓEΔ) (₁ lA) (₁ lt) (₂ lt)) (! eΓEΔ)
       (! (iniliftTᴹ Γ Δ E A))
       refl
       (liftt~ (ΣmorCon Γ) (₂ Δ) (ΣmorTel {Γ} Δ)
       _  ( ΣmorTy {Γ} E) (tr N.Ty (ini^^ᴹ Γ Δ) (morTy {Γ S1.^^ Δ} A) ) (₂ t) (₂ lt)
         (MM.tr2-Tm (ini^^ᴹ Γ Δ) (₁ tm)) 
         (
          J 
          (λ Γm' eΓ → 
          Tm~' (₁ Γ ^^ ₁ Δ) (₁ A) (₁ t) (₂ t) Γm' (tr N.Ty eΓ (₁ Am)) 
          (MM.tr2-Tm eΓ (₁ tm))) 
          (₂ tm) (ini^^ᴹ Γ Δ)
         )))

     where
      ΓΔ = Γ S1.^^ Δ
      ΓEΔ = ((Γ S1.▶ E) S1.^^ (S1.wkC Γ E Δ))
      eΓEΔ = (ini^^ᴹ (Γ S1.▶ E) (S1.wkC Γ E Δ) ◾
        ap (MM._^^_ (morCon Γ MM.▶ morTy {Γ} E)) (iniwkCᴹ Γ E Δ))
      lA = (S1.liftT Γ Δ E A)
      lt = S1.liftt Γ Δ E A t
      tm = ΣmorTm {Γ = ΓΔ} {A = A} t
      Am = ΣmorTy {Γ = ΓΔ} A
      ltm = (ΣmorTm {Γ = ΓEΔ}{A = lA}lt)
      lAm = (ΣmorTy {Γ = ΓEΔ} lA)

      p1 = ap (N.Tm _)
        (! (transpose-tr MM.Ty eΓEΔ (iniliftTᴹ Γ Δ E A)))
        -- these come from the definition of tr2
      p2 = ap (λ x → N.Tm (₁ x) (₂ x))
        (pair= (! eΓEΔ) (from-transp _ (! eΓEΔ)
        (! (transp-∙ eΓEΔ (! eΓEΔ) (₁ lAm ))
           ◾ ap (λ x → tr N.Ty x (₁ lAm ))
          (!-inv-r eΓEΔ) )))  
-- -}
  

  inisubTelᴹ : (Γ : S1.Con) (Ex : S1.Ty Γ) (Δ : S1.Telescope (Γ S1.▶ Ex))
    (z : S1.Tm Γ Ex) →
    morTel {Γ } (S1.subTel {Γ} Ex Δ z) ≡
    MM.subTel (morTy {Γ} Ex) (morTel {Γ S1.▶ Ex} Δ) (morTm {Γ} {Ex} z)

  inisubTelᴹ Γ E Δ z =
    -- myadmit 5
    Telescope~path Γ Γm _ sΔm
      (MM.subTel (morTy {Γ} E) (morTel {S1._▶_ Γ E} Δ) (morTm {Γ} {E} z))
      (subTel~ _ Γm _ Em _ Δm (₂ z) zm (subTelw (₂ z)(₂ Δ)))
    where
      Γm = ΣmorCon Γ
      Em = ΣmorTy {Γ} E
      Δm = ΣmorTel {Γ S1.▶ E} Δ
      zm = ΣmorTm {Γ} {E} z
      sΔm = ΣmorTel {Γ } (S1.subTel {Γ} E Δ z) 

  -- this lemma is defined in fact in ModelMorphism
  ^^subTel : ∀  Γ  E  Δ  z  → _
  ^^subTel Γ  E  Δ  z  = ini^^ᴹ Γ (S1.subTel  {Γ}  E Δ z) ◾ ap (MM._^^_ (morCon Γ)) (inisubTelᴹ Γ E Δ z)

  inil-subTᴹ : ∀ (Γ : S1.Con)(E : S1.Ty Γ)(Δ : S1.Telescope (Γ S1.▶ E)) (z : S1.Tm Γ E)
      (A : S1.Ty ((Γ S1.▶ E) S1.^^ Δ)) →
      morTy {Γ S1.^^ (S1.subTel {Γ} E Δ z)} (S1.l-subT {Γ} E Δ z A)
      ≡ MM.tr-Ty (! (^^subTel Γ E Δ z)) 
      (N.l-subT (morTy {Γ} E)  (morTel {Γ S1.▶ E} Δ) (morTm {Γ}{E} z)
      (MM.tr-Ty ( ini^^ᴹ (Γ S1.▶ E) Δ ) (morTy {(Γ S1.▶ E) S1.^^ Δ} A)))


  inil-subTᴹ Γ E Δ z A =
    -- myadmit 6
    Ty~path' _ ΓΔm _ sAm
      (MM.tr-Ty (! ^^subTel')
        (N.l-subT (₁ Em) (₁ Δm) (₁ zm)
          (MM.tr-Ty (ini^^ᴹ (S1._▶_ Γ E) Δ) (₁ Am))))
      (tr2
         (Ty~' (₁ ΓΔ) (l-subT ∣ ₁ Δ ∣ (₁ z) (₁ A)) (subTw (₂ z) (₂ A))
         -- (₁ ΓΔm)
         )
          (! ^^subTel' )
          (ap (λ x → MM.tr-Ty (! ^^subTel') (N.l-subT (₁ Em) (₁ Δm) (₁ zm) x))
          ( (tr-swap (λ x y → ₁ y) (ini^^ᴹ (Γ S1.▶ E) Δ)  Am)
            )
            )
         (l-subT~ _ Γm _ Em _ Δm (₂ A)
         (tr (λ Γm' → Σ (N.Ty Γm') (Ty~' (₁ Γ ▶p ₁ E ^^ ₁ Δ) (₁ A) (₂ A) Γm')) ▶^^ Am)
           (₂ z)
           zm
           (₂ sA)
           ))
    
    where
      Γm = ΣmorCon Γ
      -- ΓEΔ = ((Γ S1.▶ E) S1.^^ Δ)
      -- ΓEΔm = ΣmorCon ΓEΔ
      ΓΔ = Γ S1.^^ (S1.subTel {Γ} E Δ z)
      ΓEΔ = (Γ S1.▶ E) S1.^^ Δ
      ΓΔm = ΣmorCon ΓΔ
      Em = ΣmorTy {Γ} E
      Δm = ΣmorTel {Γ S1.▶ E} Δ
      zm = ΣmorTm {Γ} {E} z
      sΔm = ΣmorTel {Γ } (S1.subTel {Γ} E Δ z) 
      Am = ΣmorTy {(Γ S1.▶ E) S1.^^ Δ} A
      sA = (S1.l-subT {Γ} E Δ z A)
      sAm = ΣmorTy {Γ S1.^^ (S1.subTel {Γ} E Δ z)} sA

      -- these lemmas are defined in ModelMorphism
      ^^subTel' = ^^subTel Γ E Δ z 

      ▶^^ : morCon ΓEΔ  ≡ ((₁ Γm N.▶ ₁ Em) N.^^ ₁ Δm)
      ▶^^ = (ini^^ᴹ (Γ S1.▶ E) Δ)
--   -} 


  inil-subtᴹ : ∀ (Γ : S1.Con)(E : S1.Ty Γ)(Δ : S1.Telescope (Γ S1.▶ E)) (z : S1.Tm Γ E)
    (A : S1.Ty ((Γ S1.▶ E) S1.^^ Δ))(t : S1.Tm ((Γ S1.▶ E) S1.^^ Δ) A) →
      morTm {Γ S1.^^ (S1.subTel {Γ} E Δ z)} {S1.l-subT {Γ} E Δ z A}(S1.l-subt {Γ} E Δ z A t) ≡
      -- tr2 N.Tm (! ^^subTelᴹ)
      -- (! l-subTᴹ)
      -- (N.l-subt (Tyᴹ E)
      -- (tr N.Telescope ▶ᴹ (Telescopeᴹ Δ))(Tmᴹ z) (N.tr-Ty ▶^^ᴹ (Tyᴹ A))
      -- (N.tr2-Tm ▶^^ᴹ (Tmᴹ t)))
        tr2 N.Tm
          (! (^^subTel Γ E Δ z))
          (! (inil-subTᴹ Γ E Δ z A))
          (MM.l-subt (morTy {Γ} E) (morTel {Γ S1.▶ E} Δ) (morTm {Γ} {E} z)
            (MM.tr-Ty (ini^^ᴹ (Γ S1.▶ E) Δ) (morTy {(Γ S1.▶ E) S1.^^ Δ} A))
            (MM.tr2-Tm (ini^^ᴹ (Γ S1.▶ E) Δ) (morTm {(Γ S1.▶ E) S1.^^ Δ} {A} t)))

  inil-subtᴹ Γ E Δ z A t =
    Tm~path' _ ΓΔm _ sAm st stm r-h-s
    (tr3 (Tm~' (₁ ΓΔ) (₁ sA) (₁ st) (₂ st))
      (! ^^subTel')
      (! (inil-subTᴹ Γ E Δ z A))
      (ap (λ x → tr2 N.Tm
        (! (^^subTel Γ E Δ z))
        (! (inil-subTᴹ Γ E Δ z A))
        (N.l-subt (₁ Em) (₁ Δm) (₁ zm) (tr N.Ty ▶^^ (₁ Am)) x)
        )
        ( tr-swap (λ x y → ₁ y) (pair= ▶^^ (from-transp _ ▶^^ refl)) tm)
        )
      (l-subt~ _ Γm _ Em _ Δm 
        (tr N.Ty ▶^^ (₁ Am))
        (₂ t)
        (tr2 (λ a b → Σ (N.Tm a b) (Tm~' (₁ ΓEΔ) (₁ A) (₁ t) (₂ t) a b))
          ▶^^
           refl  tm)
        (₂ z)
        zm
        (₂ st)
      )
    )
    where
        Γm = ΣmorCon Γ
        ΓΔ = Γ S1.^^ (S1.subTel {Γ} E Δ z)
        ΓEΔ = (Γ S1.▶ E) S1.^^ Δ
        ΓΔm = ΣmorCon ΓΔ
        Em = ΣmorTy {Γ} E
        Δm = ΣmorTel {Γ S1.▶ E} Δ
        zm = ΣmorTm {Γ} {E} z
        sΔm = ΣmorTel {Γ } (S1.subTel {Γ} E Δ z) 
        Am = ΣmorTy {(Γ S1.▶ E) S1.^^ Δ} A
        sA = (S1.l-subT {Γ} E Δ z A)
        st = (S1.l-subt {Γ} E Δ z A t)
        sAm = ΣmorTy {ΓΔ} sA
        stm = ΣmorTm {ΓΔ} {sA} st
        tm = ΣmorTm {ΓEΔ} {A} t
        -- these lemmas are defined in ModelMorphism
        ^^subTel' = ^^subTel Γ E Δ z 
        -- the right hand side of the equation
        r-h-s =
          tr2 N.Tm
            (! (^^subTel Γ E Δ z))
            (! (inil-subTᴹ Γ E Δ z A))
            (MM.l-subt (morTy {Γ} E) (morTel {Γ S1.▶ E} Δ) (morTm {Γ} {E} z)
              (MM.tr-Ty (ini^^ᴹ (Γ S1.▶ E) Δ) (morTy {(Γ S1.▶ E) S1.^^ Δ} A))
              (MM.tr2-Tm (ini^^ᴹ (Γ S1.▶ E) Δ) (morTm {(Γ S1.▶ E) S1.^^ Δ} {A} t)))


        ▶^^ : morCon ΓEΔ  ≡ ((₁ Γm N.▶ ₁ Em) N.^^ ₁ Δm)
        ▶^^ = (ini^^ᴹ (Γ S1.▶ E) Δ)
      

  iniMor1 : ModelMorphism1 syntax2 (m2 {l})
  iniMor1 = record
        { Conᴹ = morCon
        ; Telescopeᴹ = λ {Γ} → morTel {Γ = Γ}
        ; Tyᴹ = λ {Γ} → morTy {Γ = Γ}
        ; Tmᴹ = λ {Γ} {A} → morTm {Γ = Γ} {A}
        ; ∙ᴹ = refl
        ; ▶ᴹ = refl
        ; ^^ᴹ = λ {Γ}{A} → ini^^ᴹ Γ A
        -- ini^^ᴹ {Γ} {A}
        ; ∙tᴹ = refl
        ; ▶tᴹ = λ {Γ} {Δ} {A} → ini▶tᴹ {Γ}{Δ}{A}

        ; Uᴹ = refl
        ; Elᴹ = refl
        ; ΠΠᴹ = refl

        ; wkCᴹ = λ {Γ}{E}{Δ} → iniwkCᴹ Γ E Δ
        ; liftTᴹ = λ {Γ}{Δ}{E}{A} → iniliftTᴹ Γ Δ E A
        ; lifttᴹ = λ {Γ} {Δ} {E} {A} t → inilifttᴹ Γ Δ E A t
        -- inilifttᴹ Γ Δ E A t

        ; subTelᴹ = λ {Γ}{E}{Δ}{z} → inisubTelᴹ Γ E Δ z
        ; l-subTᴹ = λ {Γ}{E}{Δ}{z}{A} → inil-subTᴹ Γ E Δ z A
        ; l-subtᴹ = λ {Γ}{E}{Δ}{z}{A}{t} → inil-subtᴹ Γ E Δ z A t
        }
