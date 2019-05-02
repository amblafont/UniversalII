-- copied from finitaryQiit/modelTemplate


open import Level 
open import Hott renaming (   fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )
  hiding (_∘_ ; _⁻¹ ; Π ; _$_)


-- open import HoTT using (ap)

open import monlib hiding (tr2)
-- open import Lib2 hiding (id; _∘_ )



module ModelMorphism   where

open import ModelRecord

-- the distinction between base and next is
-- the idea that the base will be postulated with rewrite rules,
-- and not the next (when postulating a morphism from the syntax to
-- a model)
record baseCwFMor
    {k : Level}{l : Level}(M : CwF {k} {l})
    {i : Level}{j : Level}(N : CwF {i} {j}) : Set (Level.suc (lmax (lmax i j)(lmax k l)) )
    where
 private
   module S = CwF M
 open CwF N
 field

  Conʳ : S.Con → Con
  Tyʳ  : ∀ {Γ} → S.Ty Γ → Ty (Conʳ Γ)
  Tmʳ  : ∀ {Γ A} → S.Tm Γ A → Tm (Conʳ Γ) (Tyʳ A)
  Subʳ : ∀ {Γ Δ} → S.Sub Γ Δ → Sub (Conʳ Γ) (Conʳ Δ)
  ,ʳ   : ∀ {Γ A} → Conʳ (Γ S.▶ A) ≡ (Conʳ Γ ▶ Tyʳ A)


record nextCwFMor
    {k : Level}{l : Level}{M : CwF {k} {l}}
    {i : Level}{j : Level}{N : CwF {i} {j}} (m : baseCwFMor M N)
    : Set (Level.suc (lmax (lmax i j)(lmax k l)) )
   where

 private
   module S = CwF M
 open CwF N
 open baseCwFMor m

 field

  ∙ʳ   : Conʳ S.∙ ≡ ∙
  []Tʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ Δ} →
            _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S._[_]T {Γ} {Δ} A σ))
            (_[_]T {Conʳ Γ} {Conʳ Δ} (Tyʳ {Δ} A) (Subʳ {Γ} {Δ} σ))
  -- these were rewrite rules

  []tʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {t : S.Tm Δ A} {σ : S.Sub Γ Δ} →
           Tmʳ {Γ}  (t S.[ σ ]t )
           == 
           (Tmʳ {Δ} {A} t) [ Subʳ σ ]t
            [ Tm _  ↓ []Tʳ ]

  idʳ  : {Γ : S.Con} →
           _≡_ {j} {Sub (Conʳ Γ) (Conʳ Γ)} (Subʳ {Γ} {Γ} (S.id {Γ}))
           (id {Conʳ Γ})

  ∘ʳ   : {Γ Δ : S.Con} {Σ : S.Con} {σ : S.Sub Δ Σ} {δ : S.Sub Γ Δ} →
           _≡_ {j} {Sub (Conʳ Γ) (Conʳ Σ)}
           (Subʳ {Γ} {Σ} (S._∘_ {Γ} {Δ} {Σ} σ δ))
           (_∘_ {Conʳ Γ} {Conʳ Δ} {Conʳ Σ} (Subʳ {Δ} {Σ} σ)
            (Subʳ {Γ} {Δ} δ))

  εʳ   : {Γ : S.Con} →
    (Subʳ {Γ} {S.∙} (S.ε {Γ})) == (ε {Conʳ Γ}) [ Sub _ ↓ ∙ʳ ]

  ,sʳ  : {Γ Δ : S.Con} {σ : S.Sub Γ Δ} {A : S.Ty Δ}
         {t : S.Tm Γ (S._[_]T {Γ} {Δ} A σ)} →
         (Subʳ {Γ} {Δ S.▶ A} (σ S.,s t))
         ==
         ((Subʳ {Γ} {Δ} σ) ,s tr (Tm _) []Tʳ (Tmʳ t))
          [ Sub _ ↓ ,ʳ  ]

{- 
 -- maybe this is needed for wkʳ ?
 π₁ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
           (Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))
           ≡
           (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))
 
 π₁ʳ {Γ}{Δ}{A}{σ} =
   
      (Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))

           =⟨ {!!} ⟩
       -- (π₁
       --    ((Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ)) ,s tr (Tm _) []Tʳ (Tmʳ (S.π₂ {Γ} {Δ} {A} σ))))
       {!!}


           =⟨ {!!} ⟩
       -- (π₁ (Subʳ (S.π₁ σ S.,s S.π₂ σ)))
       {!!}

           =⟨ {!ap↓!} ⟩
      (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))
      ∎

 wkʳ : ∀ {Γ : S.Con}{A : S.Ty Γ} →
    Subʳ (S.wk {A = A})== wk {A = Tyʳ A} [ (λ s → Sub s _) ↓ ,ʳ ]
 wkʳ {Γ}{A} =
    ≅↓
    (
      Subʳ (S.wk {A = A})

           ≅⟨ =≅ π₁ʳ ⟩
      (π₁   {A = Tyʳ  A} (tr (Sub _) ,ʳ (Subʳ   S.id)))

           ≅⟨ ↓≅
-- Sub (Conʳ (Γ S.▶ A)) (Conʳ Γ)
             (
             apd π₁ {x = (tr (Sub _) ,ʳ (Subʳ   S.id))}{y = id}{!!}
             -- (≅↓ (↓≅  (from-transp (Sub (Conʳ (Γ S.▶ A))) ,ʳ {u = id}refl ) !≅))
              
             -- ap↓ {B = λ s → Sub s _}{C = λ s → Sub s (Conʳ Γ)}
             
             -- (π₁ {A = Tyʳ A})
             -- {p = ,ʳ {A = A}}
             --   -- (≅↓ (↓≅ (from-transp (Sub (Conʳ (Γ S.▶ A))) ,ʳ {u = id}refl )))
             --   (≅↓ (↓≅ {!!}))
               
              )
              -- ((≅↓ (↓≅  (from-transp (Sub (Conʳ (Γ S.▶ A))) ,ʳ {u = id}refl ) !≅)))
-- Sub (Conʳ Γ ▶ Tyʳ A) (Conʳ Γ)
             ⟩
      (π₁   {A = Tyʳ  A} id)


      ≅∎
    )
    -}
    -- (↓-cst-in {p = refl}
     -- (π₁ʳ {σ = S.id {Γ = Γ S.▶ A}}) ◾  ap (λ x → π₁ (tr (Sub (Conʳ (Γ S.▶ A))) ,ʳ x)) idʳ ) ∙ᵈ
     -- {! 
     -- ap↓ {C = λ s → Sub s (Conʳ Γ)} (π₁ {A = Tyʳ A})
     --   -- (≅↓ (↓≅ {! from-transp (Sub (Conʳ (Γ S.▶ A))) ,ʳ {u = id}refl !} !≅))
     --   (≅↓ (↓≅  (from-transp (Sub (Conʳ (Γ S.▶ A))) ,ʳ {u = id}refl ) !≅))
     --   !}
    -- ≅↓ (↓≅ {! ap↓ {B = (Sub (Conʳ (Γ S.▶ A))) } π₁!})
    -- ≅↓ (↓≅ {! ap↓ π₁ {p = ,ʳ}!})
     -- {!J
     -- (λ B e →
     --  π₁ (tr (Sub (Conʳ (Γ S.▶ A))) e id)
     --  == π₁ (id {Γ = B})
     --  [ (λ s → Sub s (Conʳ Γ)) ↓ e ]
     -- )!}
    
    -- ≅↓ (↓≅ {! ap↓ π₁ (from-transp ? ,ʳ ?)!})
    
      -- (wk {A = Tyʳ A})

    -- -- ap↓ π₁ (from-transp _ _ {!!})
    -- ap↓ {B = λ s → Sub s _} π₁ {p = {!,ʳ!}}
    --   {u = tr (Sub (Conʳ (S._▶_ Γ A))) ,ʳ (Subʳ S.id)}
    --   {v = id {Γ = _▶_ (Conʳ Γ) (Tyʳ A)}}
    --    {!!}
    -- ∙ᵈ {! !}
 -- apd Subʳ {!π₁ʳ!} ∙ᵈ {!!}

 <>ʳ : ∀ {Γ : S.Con}{A : S.Ty Γ}{t : S.Tm Γ A} →
       Subʳ S.< t > == < Tmʳ t > [ Sub _ ↓ ,ʳ ]
 <>ʳ {Γ}{A}{t} =
   from-transp _ _
     (to-transp ,sʳ ◾
       ,s=
         idʳ
         -- here we use UIP
         (≅↓
           (
           ↓≅ ( from-transp (Tm (Conʳ Γ)) []Tʳ refl ) !≅
           ∘≅ (  ↓≅  (ap↓ Tmʳ {p = S.[id]T}(from-transp! _ _ refl))  
           ∘≅ ↓≅ (from-transp! (Tm (Conʳ Γ)) [id]T refl) !≅
           ))))

 [<>]T : ∀ {Γ : S.Con}{A : S.Ty Γ}{u : S.Tm Γ A}{B : S.Ty (Γ S.▶ A)}→
    Tyʳ (B S.[ S.< u > ]T) ≡ (Tyʳ B [  transport! (Sub _) ,ʳ  < Tmʳ u >  ]T)

      
 [<>]T {Γ}{A}{u} = []Tʳ ∙' ap (_[_]T _ ) (to-transp! <>ʳ) 


  


record CwFMor
    {k : Level}{l : Level}(M : CwF {k} {l})
    {i : Level}{j : Level}(N : CwF {i} {j}) 
    : Set (Level.suc (lmax (lmax i j)(lmax k l)) )
   where
  field
     basecwfmor : baseCwFMor M N
     nextcwfmor : nextCwFMor basecwfmor
  open baseCwFMor basecwfmor public
  open nextCwFMor nextcwfmor public
{-

I should do the proof, but now we can deduce that Subʳ commutes with π₁ and π₂
Indeed:
Let δ and t such that σ = (δ , t)

Then,
  Subʳ (δ , t) = (Subʳ δ , Tmʳ t)
So
  π₁ (Subʳ (δ , t)) = Subʳ δ
and
  π₂ (Subʳ (δ , t)) = Tmʳ t

or equivalently,
  π₁ (Subʳ σ) = Subʳ (π₁ σ)
  π₂ (Subʳ σ) = Tmʳ (π₂ σ)

TODO: formalize the proof (it begins after)
-}

{- 
module _
    {k : Level}{l : Level}{M : CwF {k} {l}}
    {i : Level}{j : Level}{N : CwF {i} {j}}{m : CwFMor M N} where
 private
   module S = CwF M
 open CwF N
 open CwFMor m

 π₁ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
           (Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))
           ≡
           (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))
 
 π₁ʳ {Γ}{Δ}{A}{σ} =
   
      (Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))

           =⟨ {!!} ⟩
       (π₁
          ((Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ)) ,s tr (Tm _) []Tʳ (Tmʳ (S.π₂ {Γ} {Δ} {A} σ))))

           =⟨ {!!} ⟩
       (π₁ (Subʳ (S.π₁ σ S.,s S.π₂ σ)))

           =⟨ {!!} ⟩
      (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))
      ∎

   
 
   -- version alternative
   -- π₁ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ Δ}{t : Tm Γ (A [ σ ]T)} →
   --         (Subʳ {Γ} {Δ} σ)
   --         ≡
   --         (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))
 
 π₂ʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
 
         (Tmʳ {Γ} {S._[_]T {Γ} {Δ} A (S.π₁ {Γ} {Δ} {A} σ)}
           (S.π₂ {Γ} {Δ} {A} σ))
           ==
         (π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A}
             (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))
         [ Tm _ ↓ []Tʳ ◾ ap ( _[_]T (Tyʳ _) ) π₁ʳ ]
 
 π₂ʳ {Γ}{Δ}{A}{σ} = {!!}
 -}

module _   {ll : Level}
    {k : Level}{l : Level}{M : CwF {k} {l}}(MM : UnivΠ {k = ll} M)
    {i : Level}{j : Level}{N : CwF {i} {j}}(NN : UnivΠ {k = ll} N)
    (mor : CwFMor M N)
     where
  open CwFMor mor
  open CwF N
  open UnivΠ NN
  private
    module S = CwFUnivΠ MM

-- I do Univ and Π parts in different records because
-- I need [<>^El]Tʳ before app
  record UnivMor  : Set (Level.suc (lmax (lmax i j)(lmax k l)) ) where
    field 
      Uʳ  : {Γ : S.Con} → _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S.U {Γ})) U

      Elʳ : {Γ : S.Con} {a : S.Tm Γ (S.U {Γ})} →
        (Tyʳ {Γ} (S.El  a)) ≡ (El  (tr (Tm _) Uʳ (Tmʳ   a)))

    [<>^El]Tʳ :
       ∀ {Γ}{a : S.Tm Γ S.U}{B : S.Ty (Γ S.▶ S.El a)}
            (u : S.Tm Γ (S.El a)) →
      Tyʳ (B S.[ S.< u > ]T) ≡
      (tr Ty (,ʳ ∙' ap (_▶_ (Conʳ Γ)) Elʳ) (Tyʳ B) [
       < tr (Tm (Conʳ Γ)) Elʳ (Tmʳ u) > ]T)

    [<>^El]Tʳ {Γ}{a}{B}u =
      [<>]T ∙'
      
      J (λ C e →
          (Tyʳ B [ transport! (Sub (Conʳ Γ)) ,ʳ < Tmʳ u > ]T) ≡
          (tr Ty (,ʳ ∙' ap (_▶_ (Conʳ Γ)) e) (Tyʳ B) [
          < tr (Tm (Conʳ Γ)) e (Tmʳ u) > ]T)
      )
      ( 
      J (λ C e → ∀ <u> →
        Tyʳ B [ transport! (Sub (Conʳ Γ)) e <u> ]T ≡
          tr Ty e (Tyʳ B) [ <u> ]T
      )
      (λ _ → refl)
      ,ʳ
      < Tmʳ u >
      )
      Elʳ


  record ΠMor (um : UnivMor) : Set (Level.suc (lmax ll (lmax (lmax i j)(lmax k l))) ) where
      -- module S = UnivΠ MM
    -- module NN = UnivΠ NN
    open UnivMor um

      
      

    field


      Πʳ : {Γ : S.Con} {a : S.Tm Γ (S.U {Γ})} {B : S.Ty (Γ S.▶ S.El {Γ} a)} →
        _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S.Π {Γ} a B))
        (Π {Conʳ Γ} (tr (Tm _) Uʳ (Tmʳ {Γ} {S.U {Γ}} a))
          (tr Ty (,ʳ ∙' ap ( _▶_ _ ) Elʳ) (Tyʳ {Γ S.▶ S.El {Γ} a} B)))

      -- appʳ : {Γ : S.Con} {a : S.Tm Γ (S.U {Γ})} {B : S.Ty (Γ S.▶ S.El {Γ} a)}
      --         {t : S.Tm Γ (S.Π {Γ} a B)} →
              
      --         (Tmʳ {Γ S.▶ S.El {Γ} a} {B} (S.app {Γ} {a} {B} t))
      --         ==
      --         (app {Conʳ Γ}  
      --           (tr (Tm _) Πʳ (Tmʳ {Γ} {S.Π {Γ} a B} t)))
      --           [ (λ x → Tm (₁ x)(₂ x)) ↓
      --             pair= (,ʳ ◾ ap ( _▶_ _ ) Elʳ) (from-transp _ _ refl) ]
      $ʳ : ∀ {Γ}{a : S.Tm Γ S.U}{B : S.Ty (Γ S.▶ S.El a)}(t : S.Tm Γ (S.Π a B))
      -- this q , e is to stop reduction
            (u : S.Tm Γ (S.El a))
            →
            let e = [<>^El]Tʳ u in
            -- {e}(q : e ≡ [<>^El]Tʳ u)→ 
          Tmʳ (t S.$ u) ==
            (tr (Tm _) Πʳ (Tmʳ t) $
            tr (Tm _) Elʳ (Tmʳ u)) [ Tm _ ↓  e
            -- [<>^El]Tʳ u
            ]
           -- []Tʳ ◾ ap (λ s → Tyʳ B [ s ]T) (to-transp! <>ʳ) ◾ {!!} ]

      ΠNIʳ : {Γ : S.Con} {T : Set ll} {B : T → S.Ty Γ} →
        _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (S.ΠNI B))
        (ΠNI {Conʳ Γ} {T = T} λ a → Tyʳ (B a))
          -- (tr Ty (,ʳ ∙' ap ( _▶_ _ ) Elʳ) (Tyʳ {Γ S.▶ S.El {Γ} a} B)))
      $NIʳ : ∀ {Γ}{T : Set ll}{B : T → S.Ty Γ}(t : S.Tm Γ (S.ΠNI B))
            (u : T)
            →
          Tmʳ (t S.$NI u) ≡ tr (Tm _) ΠNIʳ (Tmʳ t) $NI u

        -- {!Tmʳ (t S.$ u) == ((Tmʳ t) $ (Tmʳ u)) [ Tm _ ↓ ? ]!}
    -- $ʳ = {!!}
  record UnivΠMor : Set (Level.suc (lmax ll (lmax (lmax i j)(lmax k l)) )) where
    field
      univmor : UnivMor
      Πmor : ΠMor univmor
    open UnivMor univmor public
    open ΠMor Πmor public
