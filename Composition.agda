-- composition: needed for the _[_]T case
-- identity : needed for

open import Level 
open import HoTT renaming (_==_ to _≡_ ; _∙_ to _◾_ ; idp to refl ; transport to tr ; fst to ₁ ; snd to ₂)
  hiding (_∘_)

open import Syntax

open import monlib

module Composition where

wkt-keep : ∀ s t →  (wkt t [ keep s ]t) ≡ wkt (t [ s ]t)
wkt-keep s t = wkₛt t (V 0) (wkS s) ◾ wkt=wkS s t
-- I can't find this in the HoTT library
-- TODO move to monlib.
map-∘ : ∀ {i j k} {A : Type i} {B : Type j} (f : A → B)
  {C : Type k} (g : B → C)  l → map g (map f l) ≡ map (λ x → g (f x)) l
map-∘ f g nil = refl
map-∘ f g (x :: l) = ap (g (f x) ::_) (map-∘ f g l)

pw-map= : ∀ {i j} {A : Type i} {B : Type j} (f g : A → B) (e : ∀ a → f a ≡ g a) →
  ∀ l → map f l ≡ map g l
pw-map= f g e nil = refl
pw-map= f g e (x :: l) = ap2 _::_ (e x) (pw-map= f g e l)

infix  6 _∘p_
-- s2: Γ → Δ et s1 : Δ → Y
-- alors s1 ∘ s2 : Γ → Y
_∘p_ : Subp → Subp → Subp
s1 ∘p s2 = map (_[ s2 ]t) s1

-- needed for keep∘
wkS∘ : ∀ s1 s2 → wkS (s1 ∘p s2) ≡ ((wkS s1) ∘p (keep s2))
wkS∘ s1 s2 = map-∘ (_[ s2 ]t) wkt s1 ◾
  pw-map= _ _ (λ x → ! (wkt-keep s2 x) ) _  ◾ ! (map-∘  wkt (_[ keep s2 ]t)s1)


-- for the Π case of [∘]T
keep∘ : ∀ s1 s2 → (keep (s1 ∘p s2)) ≡ (keep s1 ∘p keep s2)
keep∘ s1 s2 rewrite wkS∘ s1 s2 = refl

-- needed for the _[_]T case of setmodelCOmponents
[∘]V : ∀ x s1 s2 → (x [ s1 ∘p s2 ]V) ≡ (x [ s1 ]V [ s2 ]t)  
[∘]V x s1 s2 = olookup-map (_[ s2 ]t) x err s1

[∘]t : ∀ t s1 s2 → (t [ s1 ∘p s2 ]t) ≡ (t [ s1 ]t [ s2 ]t)  

[∘]t (V x) s1 s2 = [∘]V x s1 s2
[∘]t (app t u) s1 s2 rewrite [∘]t t s1 s2 | [∘]t u s1 s2 = refl
[∘]t err s1 s2 = refl


[∘]T : ∀ A s1 s2 → (A [ s1 ∘p s2 ]T) ≡ (A [ s1 ]T [ s2 ]T)  
-- [∘]T A s1 s2 = {!!}
[∘]T Up s1 s2 = refl
[∘]T (Elp x) s1 s2 = ap Elp ([∘]t x s1 s2)
[∘]T (ΠΠp A B) s1 s2
  rewrite [∘]T A s1 s2
  | keep∘ s1 s2
  | [∘]T B (keep s1) (keep s2)
  =
  -- ap (ΠΠp _) ( {!keep∘ _ _!} ◾)
   refl

--- needed for the ᶜ case of Sub in SetModelComponentsACDS
∘w : ∀ {Γ} {Δ σ} (σw : Subw Δ Γ σ)
   {Y}(Yw : Conw Y) {δ} (δw : Subw Y Δ δ) →
   Subw Y Γ (σ ∘p δ)
   -- ∘w σw δw = {!δw!}
∘w nilw Yw σw = nilw
∘w (,sw δw Aw tw) Yw σw  = 
  ,sw ( ∘w δw Yw σw ) Aw (tr (λ A → Tmw _ A _) (! ([∘]T _ _ _)) (Tmwₛ tw Yw σw))
