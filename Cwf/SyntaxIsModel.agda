{-  copied from finitaryQiit/modelTemplate
some complementary lemmas about the syntax
           -}


open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )

  hiding (_∘_ ; _⁻¹ ; Π ; _$_)



open import monlib hiding (tr2)



module SyntaxIsModel   where

open import ModelRecord

module _ {i : Level} {j : Level} (MM : CwF {i}{j}) where
  open CwF MM

  helper'' : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ ▶ A)} →
        ((B
           [ (id ∘ wk {A = A} ) ^ A ]T)
           -- [ {!!} ]T ) ≡ B
           [ < transport! (λ s → Tm _ (A [ s ]T)) idl vz > ]T ) ≡ B
  helper'' {Γ}{A}{B} =
     [][]T ◾ ap (_[_]T B ) aux ◾  [id]T 
     where
       aux : (( (id ∘ wk {A = A} ) ^ A ) ∘ < transport! (λ s → Tm _ (A [ s ]T)) idl vz  >) ≡ id
       aux = ^∘<> ◾ ,s= idl (from-transp! _ _ refl) ◾  πη

open import Syntax

-- Con = ∃ Conw

-- I defined it as a record rather than using Σ because otherwise
-- inferences may fail
-- I don't know if it helps though...
record Con : Set  where
  constructor _,_
  field
    ₁ : Conp
    ₂ : Conw ₁
open Con public

record Ty (Γ : Con) : Set  where
  constructor _,_
  field
    ₁ : Typ
    ₂ : Tyw (Con.₁ Γ ) ₁

open Ty public

Ty= : ∀ {Γ}{A B : Ty Γ}(e : ₁ A ≡ ₁ B) → A ≡ B
Ty= {Γ} {A , Aw} {B} e rewrite e | prop-has-all-paths Aw (₂ B) = refl

record Tm (Γ : Con)(A : Ty Γ) : Set  where
  constructor _,_
  field
    ₁ : Tmp
    ₂ : Tmw (Con.₁ Γ ) (Ty.₁ A) ₁

open Tm public

Tm= : ∀ {Γ}{A}{t u : Tm Γ A}(e : ₁ t ≡ ₁ u) → t ≡ u
Tm= {Γ} {A}{t , tw} {u} e rewrite e | prop-has-all-paths tw (₂ u) = refl

Tm=↓ : ∀ {Γ}{A}{t : Tm Γ A}{B}{u : Tm Γ B}(eT : A ≡ B)(e : ₁ t ≡ ₁ u) →
   t == u [ Tm Γ ↓ eT ]

Tm=↓ {Γ} {A} {t}{.A}{u} refl = Tm= {u = u} 

fstTm= : ∀ {Γ}{A}{t u : Tm Γ A}(e : t ≡ u) → ₁ t ≡ ₁ u
fstTm= {Γ}{A}{t}{u}  = ap ₁ 

Tm-tr=₁ : ∀ {Γ}{A}{t : Tm Γ A}{B : Ty Γ}{e : A ≡ B} →
  ₁ t ≡ ₁ (tr (Tm Γ) e t)
Tm-tr=₁ {e = refl} = refl

Tm-tr!=₁ : ∀ {Γ}{A}{t : Tm Γ A}{B : Ty Γ}{e : B ≡ A} →
  ₁ t ≡ ₁ (transport! (Tm Γ) e t)
Tm-tr!=₁ {t = t}{e = e} = forget-tr! (Tm _) e t (λ {A} u → ₁ u)

record Sub (Γ : Con)(Δ : Con) : Set  where
  constructor _,_
  field
    ₁ : Subp
    ₂ : Subw (Con.₁ Γ )(Con.₁ Δ ) ₁

open Sub public

Sub= : ∀ {Γ}{Δ}{σ δ : Sub Γ Δ}(e : ₁ σ ≡ ₁ δ) → σ ≡ δ
Sub= {Γ}{Δ} {σ , σw} {δ} e rewrite e | prop-has-all-paths σw (₂ δ) = refl

fstSub= : ∀ {Γ}{Δ}{σ δ : Sub Γ Δ}(e : σ ≡ δ) → ₁ σ ≡ ₁ δ
fstSub= {Γ}{A}{σ}{δ}  = ap ₁ 

open Sub public

syntaxCwF : CwF
syntaxCwF = record
              { basecwf =
                  record { Con = Con
                          ; Ty = Ty
                          ; Tm = Tm
                          ; Sub = Sub } ;
                nextcwf = record {
               ∙ = ∙p , ∙w
              ; _▶_ = λ Γ A → ((₁ Γ ▶p ₁ A ) , ▶w (₂ Γ) (₂ A))
              ; _[_]T = λ {Γ}{Δ}A σ → (_ , Tyw[] (₂ A)(₂ Γ)(₂ σ))
              ; id = λ {Γ} → _ , idpw (₂ Γ)
              ; _∘_ = λ {Γ}{Δ}{Y}σ δ → _ , ∘w (₂ σ)(₂ Γ)(₂ δ)
              ; ε = λ {Γ} → _ , nilw
              ; _,s_ = λ {Γ}{Δ}σ{A}t → (₁ t :: ₁ σ) , ,sw (₂ Δ) ((₂ σ)) (₂ A) (₂ t)
              ; π₁ = λ {Γ}{Δ}{A} →  λ { (_ , ,sw Δw σw Aw tw) → _ , σw }
              ; _[_]t = λ {Γ}{Δ}{A}t σ → _ , Tmw[](₂ t)(₂ Γ)(₂ σ)
              ; π₂ = λ {Γ}{Δ}{A} →  λ { (_ , ,sw Δw σw Aw tw) → _ , tw }

              ; [id]T = λ {Γ}{A}→ Ty= ([idp]T (₂ A))
              ; [][]T = λ {Γ}{Δ}{Y}{A}{σ}{δ} → Ty= (! ([∘]T _ _ _))
              ; idl = λ {Γ}{Δ}{σ} → Sub= (idl (₂ σ))
              ; idr = λ {Γ}{Δ}{σ} → Sub= (idr (₂ σ))
              ; ass = λ {Γ}{Δ}{Y}{O}{σ}{δ}{ν} → Sub= ass
              ; π₁,∘ = refl
              ; π₂,∘ = λ {Γ}{Δ}{Y}{δ}{σ}{A}{t} → Tm=↓ _ refl 
              ; π₁β = refl
              ; πη = λ {Γ}{Δ}{A} → λ { {_ , ,sw Δw σw Aw tw} → Sub= refl } 
              ; εη = λ {Γ} → (λ { {(_ , nilw)} → refl })
              ; π₂β = refl
              }
              }


-- -}

{- ------------

Now the UnivΠ part


------------- -}

wk : ∀ Γ → Subp
wk Γ = wkS (idp Γ )




wkS=∘wk : ∀ {Γ}{Δ}{σ}(σw : Subw Γ Δ σ){A}(Aw : Tyw Γ A) → wkS σ ≡ σ ∘p (wk ∣ Γ ∣)
wkS=∘wk {Γ}{Δ}{σ}σw{A}Aw = ! (idr {σ = wkS σ} (wkSw σw Aw)) ◾ wk∘, _ _ _

-- wkS (idp ∣ Γ ∣ ) ∘p  < ∣ Γ ▶p A ∣ ⊢ (V 0) >
private
  module S where
    open CwF syntaxCwF public

<>=<> : ∀ {Γ}{A}(t : Tm Γ A) →  < ∣ ₁ Γ ∣  ⊢ ₁ t > ≡ ₁ S.< t >
<>=<> {Γ}{A}t = ap (_:: _) (Tm-tr!=₁ {t = t})

wk=wk : ∀{Γ}{A : Ty Γ} → wk ∣ ₁ Γ ∣ ≡ ₁ (S.wk {A = A})
wk=wk = refl

keep=^ : ∀ {Γ}{Δ}{σ : Sub Γ Δ}{A : Ty Δ} →
  keep (₁ σ) ≡ ₁ (σ S.^ A)
keep=^ {Γ}{Δ}{σ}{A}  =
  let  p = S.[][]T  {Σ = Δ} 
       B = Tm ((₁ Γ ▶p (₁ A [ ₁ σ ]T)) , ▶w (₂ Γ) (Tyw[] (₂ A) (₂ Γ) (₂ σ)))
       v = tr B p S.vz
  in
  ap2 _::_
    (Tm-tr=₁ {t = S.vz {Γ = Γ}{A = A S.[ σ ]T}}{e = p})
        -- (↓-cst-out {p = p} ( ap↓ {B = B} Tm.₁ {p = p}{u = S.vz {Γ = Γ}{A = A S.[ σ ]T}} {v = v}
        --   (from-transp _ _ refl) ))
       
   (wkS=∘wk (₂ σ) (Tyw[] (₂ A) (₂ Γ) (₂ σ)))


helper : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ S.▶ A)} → subT (V 0) (liftT 1 (₁ B)) ≡ (₁ B)
helper {Γ}{A}{B} =
         (subT (V 0) (liftT 1 (₁ B)) 

            =⟨ ap (λ C → subT (V 0) (liftT 1 C)) (! ([idp]T (₂ B))) ⟩
         (subT (V 0) (liftT 1 ((₁ B) [ (idp ∣ ₁ Γ ▶p ₁ A ∣) ]T) ) )

            -- =⟨ ap (subT (V 0)) {!! ? liftT=wkS 1!} ⟩
            =⟨ ap (subT (V 0)) (! (liftT=wkS 1 (idp ∣ ₁ Γ ∣) (₁ B))) ⟩
          subT (V 0) ((₁ B) [ keep (wkS (idp ∣ ₁ Γ  ∣))]T)


            =⟨ ! ([<>]T  {Γ = ₁ Γ ▶p ₁ A}
              (transport! (Tyw _ )
                (liftT=wkS 1 (idp ∣ ₁ Γ ∣) (₁ B) ◾ ap (liftT 1) ([idp]T (₂ B)) )
               (liftTw  (₂ A)(∙p ▶p ₁ A) (₂ B) ) )
               (V 0)) ⟩
          (((₁ B) [  keep (wkS (idp ∣ ₁ Γ  ∣)) ]T) [ < ∣ ₁ Γ ▶p ₁ A ∣ ⊢ (V 0) > ]T )


            =⟨ ap2 (λ s1 s2 → (₁ B [ s1 ]T) [ s2 ]T)
             (ap keep (wkS=∘wk (idpw (₂ Γ))(₂ A)) ◾
                keep=^ {σ = S.id {Γ = Γ} S.∘ S.wk {A = A} }{A})
             (<>=<> ( S.vz {Γ = Γ}{A = A} ) ◾ ap (λ x → x :: _)
                (! ( Tm-tr!=₁ {t = (S.vz {A = A})}{e = S.[id]T}) ◾
                  forget-tr! (λ s → Tm _ (A S.[ s ]T)) S.idl (S.vz {A = A}) (λ t → ₁ t) ◾
                  forget-tr! (Tm _) S.[id]T ( transport! (λ s → Tm _ (A S.[ s ]T)) S.idl (S.vz {Γ = Γ}{A = A}) )
                     (λ t → ₁ t) 
                )
              )
             ⟩
          -- (((₁ B) [ ₁ ((S.id {Γ = Γ} S.∘ S.wk {A = A} ) S.^ A) ]T) [ ₁ S.< S.vz {Γ = Γ}{A = A} > ]T )
          (((₁ B) [ ₁ ((S.id {Γ = Γ} S.∘ S.wk {A = A} ) S.^ A) ]T)
            [ ₁ S.< transport! (λ s → Tm _ (A S.[ s ]T)) S.idl (S.vz {Γ = Γ}{A = A}) > ]T )
          -- < transport! (λ s → Tm _ (A [ s ]T)) idl vz >

            =⟨ ap ₁ (helper'' syntaxCwF {B = B})  ⟩
          ₁ B



        ∎)







wkt[^] : ∀ {Γ}{Δ}{σ : Sub Γ Δ}{A}{t : Tm Δ A}{B} → (wkt (₁ t) [ ₁ (σ S.^ B) ]t) ≡ wkt  (₁ t [ ₁ σ ]t)
wkt[^] {Γ}{Δ}{σ}{A}{t}{B} =
         (wkt (₁ t) [ ₁ (σ S.^ B) ]t)

              =⟨  wk[,]t (₁ t) _ (₁ σ ∘p wk ∣ ₁ Γ ∣)  ⟩
         (₁ t [ ₁ σ ∘p wk ∣ ₁ Γ ∣ ]t)

              =⟨ ap (₁ t [_]t) (! (wkS=∘wk (₂ σ) (₂ (B S.[ σ ]T)))) ⟩
         (₁ t [ wkS (₁ σ )]t)

              =⟨ wkt=wkS  (₁ σ)(₁ t) ⟩
          wkt  (₁ t [ ₁ σ ]t)
        ∎

-- Goal: (wkt (₁ t) [ ₁ (σ S.^ (Elp (₁ a) , Elw (₂ Δ) (₂ a))) ]t) ==

U : ∀ {Γ : Con} → Ty Γ
U {Γ} = _ , Uw _ (₂ Γ)

El : {Γ : Con} → Tm Γ U → Ty Γ
El {Γ} a = _ , Elw (₂ Γ)(₂ a)

Π : {Γ : Con} (a : Tm Γ U) →
   Ty (Γ S.▶ El a) → Ty Γ
Π {Γ} a B = _ , Πw (₂ Γ) (₂ a)(₂ B)



syntaxUnivΠ : UnivΠ syntaxCwF
syntaxUnivΠ = record
                { U = U
                ; U[] = refl
                ; El = El
                -- λ {Γ}t → _ , Elw (₂ Γ) (₂ t)
                ; El[] = refl
                ; Π = Π
                -- λ {Γ}a B → _ , Πw (₂ Γ)(₂ a)(₂ B)
                ; Π[] = λ {Γ}{Δ}{σ}{a}{B} →
                  Ty=
                    ( (ap (λ s → ΠΠp (Elp ((₁ a) [ ₁ σ ]t)) (₁ B [ s ]T))
                       (keep=^ {Γ = Γ}{Δ = Δ}{A =  El a})) )
                ; app = λ {Γ}{a}{B}t  →
                   (app (wkt (₁ t)) (V 0)) ,
                    -- {!appw
                     -- (₁ Γ ▶p Elp (₁ a)) (▶w (₂ Γ) (Elw (₂ Γ)(₂ a)))
                     -- _ (wktw (Elw (₂ Γ)(₂ a)) (₂ a))
                     -- (liftT 1 (₁ B)) (liftTw (Elw (₂ Γ)(₂ a)) (∙p ▶p _) (₂ B))
                     -- (wkt (₁ t)) (wktw (Elw (₂ Γ)(₂ a) ) (₂ t))
                     -- (V 0) (vw (V0w _ (₂ Γ) _ (Elw (₂ Γ)(₂ a)) ))!}
                    tr
                     (λ B' → Tmw _ B' _)
                     (helper {B = B})
                     (appw
                     (₁ Γ ▶p Elp (₁ a)) (▶w (₂ Γ) (Elw (₂ Γ)(₂ a)))
                     _ (wktw (Elw (₂ Γ)(₂ a)) (₂ a))
                     (liftT 1 (₁ B)) (liftTw (Elw (₂ Γ)(₂ a)) (∙p ▶p _) (₂ B))
                     (wkt (₁ t)) (wktw (Elw (₂ Γ)(₂ a) ) (₂ t))
                     (V 0) (vw (V0w _ (₂ Γ) _ (Elw (₂ Γ)(₂ a)) ))
                     )
                ; app[] = λ {Γ}{Δ}{σ}{a}{B}{t} →
                  Tm=
                   (ap2 app
                     ( wkt[^] {σ = σ}{t = t}{B =  El a}
                        ◾
                        
                             ap wkt
                           ( Tm-tr=₁
                           {t = t S.[ σ ]t}
                           {e = (Ty= {Γ = Γ}
                           {A = (Π a B) S.[ σ ]T}
                           {B = Π (a S.[ σ ]t)(B S.[ σ S.^ El a ]T) }
                           (ap (λ s → ΠΠp (Elp (₁ a [ ₁ σ ]t)) (₁ B [ s ]T))
                             (keep=^ {Γ = Γ}{A =  El a})
                             ))}
                           )
                           
                           
                           
                           )
                     -- (wk[,]t (₁ t)_ _ ◾ ap (₁ t [_]t) {x = ₁ σ ∘p ₁ S.wk} (! (wkS=∘wk (₂ σ) {!!})) ◾ {!!})
                     ( ap (0 [_]V) (! (keep=^ {σ = σ}{A = El a})) ))
-- Goal: (0 [ ₁ (σ S.^ (Elp (₁ a) , Elw (₂ Δ) (₂ a))) ]V) == V 0
                }

module Syn where
  open CwF syntaxCwF public
  open UnivΠ syntaxUnivΠ public
  -- open Telescope RewCwF public
