
-- copied from finitaryQiit/modelTemplate


open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )

  hiding (_∘_ ; _⁻¹ ; Π ; _$_)


-- open import HoTT using (ap)

open import monlib hiding (tr2)
-- open import Lib2 hiding (id; _∘_ )



module ModelMorphism   where

open import ModelRecord


record CwFMor {k : Level}{l : Level}(M : CwF {k} {l})
    {i : Level}{j : Level}(N : CwF {i} {j}) : Set (Level.suc (lmax (lmax i j)(lmax k l)) ) where

 private
   module S = CwF M
 open CwF N

 field

  Conʳ : S.Con → Con
  Tyʳ  : ∀ {Γ} → S.Ty Γ → Ty (Conʳ Γ)
  Tmʳ  : ∀ {Γ A} → S.Tm Γ A → Tm (Conʳ Γ) (Tyʳ A)
  Subʳ : ∀ {Γ Δ} → S.Sub Γ Δ → Sub (Conʳ Γ) (Conʳ Δ)

  ∙ʳ   : Conʳ S.∙ ≡ ∙
  ,ʳ   : ∀ {Γ A} → Conʳ (Γ S.▶ A) ≡ (Conʳ Γ ▶ Tyʳ A)
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

  π₁ʳ  : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
          (Subʳ {Γ} {Δ} (S.π₁ {Γ} {Δ} {A} σ))
          ≡
          (π₁ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A} (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))

  π₂ʳ : {Γ Δ : S.Con} {A : S.Ty Δ} {σ : S.Sub Γ (Δ S.▶ A)} →
          
          (Tmʳ {Γ} {S._[_]T {Γ} {Δ} A (S.π₁ {Γ} {Δ} {A} σ)}
           (S.π₂ {Γ} {Δ} {A} σ))
           ==
          (π₂ {Conʳ Γ} {Conʳ Δ} {Tyʳ {Δ} A}
             (tr (Sub _) ,ʳ (Subʳ {Γ} {Δ S.▶ A} σ)))
          [ Tm _ ↓ []Tʳ ◾ ap ( _[_]T (Tyʳ _) ) π₁ʳ ]

module _ 
    {k : Level}{l : Level}{M : CwF {k} {l}}(MM : UnivΠ M)
    {i : Level}{j : Level}{N : CwF {i} {j}}(NN : UnivΠ N) where


  record UnivΠMor (mor : CwFMor M N) : Set (Level.suc (lmax (lmax i j)(lmax k l)) ) where
    open CwFMor mor
    private
      module S = CwF M
      module SS = UnivΠ MM
    open CwF N
    open UnivΠ NN
    -- module NN = UnivΠ NN

    field 
      Uʳ  : {Γ : S.Con} → _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (SS.U {Γ})) U

      Elʳ : {Γ : S.Con} {a : S.Tm Γ (SS.U {Γ})} →
        (Tyʳ {Γ} (SS.El  a)) ≡ (El  (tr (Tm _) Uʳ (Tmʳ   a)))

      Πʳ : {Γ : S.Con} {a : S.Tm Γ (SS.U {Γ})} {B : S.Ty (Γ S.▶ SS.El {Γ} a)} →
        _≡_ {i} {Ty (Conʳ Γ)} (Tyʳ {Γ} (SS.Π {Γ} a B))
        (Π {Conʳ Γ} (tr (Tm _) Uʳ (Tmʳ {Γ} {SS.U {Γ}} a))
          (tr Ty (,ʳ ◾ ap ( _▶_ _ ) Elʳ) (Tyʳ {Γ S.▶ SS.El {Γ} a} B)))

      appʳ : {Γ : S.Con} {a : S.Tm Γ (SS.U {Γ})} {B : S.Ty (Γ S.▶ SS.El {Γ} a)}
              {t : S.Tm Γ (SS.Π {Γ} a B)} →
              
              (Tmʳ {Γ S.▶ SS.El {Γ} a} {B} (SS.app {Γ} {a} {B} t))
              ==
              (app {Conʳ Γ}  
                (tr (Tm _) Πʳ (Tmʳ {Γ} {SS.Π {Γ} a B} t)))
                [ (λ x → Tm (₁ x)(₂ x)) ↓
                  pair= (,ʳ ◾ ap ( _▶_ _ ) Elʳ) (from-transp _ _ refl) ]
