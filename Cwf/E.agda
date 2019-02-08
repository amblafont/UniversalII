{-

E part (eliminator)
Elimination/*
-}

-- C-j pour revenir à la ligne
-- M/C-fb
-- C-o pour faire une commande en mode edit


-- copied from InitialAlg/


open import SyntaxIsModel using () renaming (module Syn to S) 
import SyntaxIsModel as SM
-- open import Syntax using () renaming (keep to coucou)
open import Syntax using ()  renaming (keep to coucou)
-- renaming (keep to coucou)

open import monlib

module E (funext : ∀ {i}{j} → funext-statment {i}{j})(cheat : ∀{i}{A : Set i} → A)(Ω : S.Con)
  where







-- infixl 9 ap
open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )
  hiding (_∘_ ; _⁻¹ ; Π ; _$_ ; Lift ; Ω)



-- open import ADS using ( mkCon; mkTy; mkTm; mkSub ; i ; j)
open import ADS using ( i ; j ; ᴬ ; ᴰ ; ˢ)
open import  C funext cheat Ω
  using (  ᴬᴰˢ ; ᴬ ; ᴰ ; ˢ ; ⁱ ; ᶜ)
import C funext cheat Ω as C
-- open import ADS using ( i ; j )
-- import StrictLib hiding (id; _∘_)


open import ModelMorphism

open CwFMor C.CBaseMor

con : ᴬ  (Conʳ Ω )
con = ᶜ (Conʳ Ω) (tr (S.Sub Ω) cheat S.id)

module _ (ω : ᴰ  (Conʳ Ω)  con) where



  record Con : Set i where
    field
      ⁱ : S.Con
      ᴱ : (v : S.Sub Ω ⁱ) → ˢ  (Conʳ ⁱ) (ᴬ (Subʳ v) con) (ᴰ (Subʳ v) _ ω)

  open Con public

  record Ty (Γ : Con) : Set i where
    constructor mkTy
    field
      ⁱ : S.Ty (ⁱ Γ)
      ᴱ : (v : S.Sub Ω ( Con.ⁱ Γ)) → (t : S.Tm Ω (ⁱ  S.[ v ]T)) →
        ˢ (Tyʳ ⁱ) _ _ (ᴱ Γ v) _ {!ᴰ (Tmʳ t) _ ω!}
