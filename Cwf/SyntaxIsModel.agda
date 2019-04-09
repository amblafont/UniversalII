{-  copied from finitaryQiit/modelTemplate
some complementary lemmas about the syntax
           -}


open import Level 
open import HoTT renaming (  idp to refl ;  fst to ₁ ; snd to ₂ ;  _∙_ to _◾_ ; transport to tr )

  hiding (_∘_ ; _⁻¹ ; Π ; _$_)



open import monlib hiding (tr2)



module SyntaxIsModel {k : Level}  where

open import ModelRecord
open import Syntax {i = k}

module _ {i : Level} {j : Level} (MM : CwF {i}{j}) where
  open CwF MM
  {-

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
       -}


-- Con = ∃ Conw

-- I defined it as a record rather than using Σ because otherwise
-- inferences may fail
-- I don't know if it helps though...
record Con : Set (suc k)  where
  constructor _,_
  field
    ₁ : Conp
    ₂ : Conw ₁
open Con public

record Ty (Γ : Con) : Set (suc k)  where
  constructor _,_
  field
    ₁ : Typ
    ₂ : Tyw (Con.₁ Γ ) ₁

open Ty public

Ty= : ∀ {Γ}{A B : Ty Γ}(e : ₁ A ≡ ₁ B) → A ≡ B
Ty= {Γ} {A} {B} refl = ap (_ ,_) (prop-has-all-paths _ _)
-- rewrite e | prop-has-all-paths Aw (₂ B) = refl

record Tm (Γ : Con)(A : Ty Γ) : Set (suc k) where
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

record Sub (Γ : Con)(Δ : Con) : Set (suc k)  where
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



{- ------------

Now the UnivΠ part


------------- -}





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


{- 
private
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


-}





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


Π[] : ∀{Γ}{Δ}{σ : Sub Γ Δ}{a}{B} →
   (Π a B) S.[ σ ]T ≡ Π (a S.[ σ ]t) (B S.[ σ S.^ El a ]T)


Π[]{Γ}{Δ}{σ} {a}{B} = 
    Ty=
      ( (ap (λ s → ΠΠp (Elp ((₁ a) [ ₁ σ ]t)) (₁ B [ s ]T))
          (keep=^ {Γ = Γ}{Δ = Δ}{A =  El a})) )

Π-NI : {Γ : Con} {T : Set k} →
   (T → Ty Γ) → Ty Γ
Π-NI {Γ} {T} B = _ , ΠNIw (₂ Γ) (λ a → (₂ (B a)))


-- (! ([<>]T (₂ B) (₁ u)) ◾ ap (_[_]T (₁ B)) (<>=<>  u))
₁[<>]T : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ S.▶ A)}{u : Tm Γ A} →
  subT (₁ u) (₁ B) == ₁ (B S.[ S.< u > ]T)

₁[<>]T {Γ}{A}{B}{u} = ! ([<>]T (₂ B) (₁ u)) ◾ ap (_[_]T (₁ B)) (<>=<>  u)


syntaxUnivΠ : UnivΠ {k = k} syntaxCwF
syntaxUnivΠ = record
                { U = U
                ; U[] = refl
                ; El = El
                -- λ {Γ}t → _ , Elw (₂ Γ) (₂ t)
                ; El[] = refl
                ; Π = Π
                -- λ {Γ}a B → _ , Πw (₂ Γ)(₂ a)(₂ B)
                ; Π[] = λ {Γ}{Δ}{σ}{a}{B} → Π[]
                ; ΠNI = Π-NI 
                -- λ {Γ}a B → _ , Πw (₂ Γ)(₂ a)(₂ B)
                ; ΠNI[] = refl
                       
                ; _$_ = λ {Γ}{a}{B}t u  →
                   (app (₁ t) (₁ u)) ,
                    
                    tr (λ B' → Tmw _ B' _ )
                    (₁[<>]T {A = El a}{B = B}{u} )
                    (appw
                     (₁ Γ ) (₂ Γ)
                     _ (₂ a)
                     _ (₂ B)
                     _ (₂ t)
                     _ (₂ u)
                     )

                     
                ; $[] = λ {Γ}{Δ}{σ}{a}{B}{t}{u} →
                   Tm=↓ (S.[<>][]T {u = u}{B = B}{σ = σ})
                   (ap (λ x → app x _)
                   ( (Tm-tr=₁ {t = t S.[ σ ]t } {e = Π[]})))
                ; _$NI_ =  λ {Γ}{T}{B}t u → appNI (₁ t) u , appNIw (₂ Γ) (λ a → ₂ (B a)) (₂ t) u 
                ; $NI[] = refl
                           

                           
                }


module Syn where
  open CwF syntaxCwF public
  open UnivΠ syntaxUnivΠ public
  -- open Telescope RewCwF public

-- -}
private
  module M = Syn

-- simple arrow
S→ : {Γ : M.Con} (A : M.Tm Γ M.U)(B : M.Ty Γ) → M.Ty Γ
S→ {Γ} A B = M.Π A (B M.[ M.wk {A = M.El A}]T)
-- (S1.wkT Γ (S1.El Γ A) B)

--non dependent application
Sa : {Γ : M.Con} {A : M.Tm Γ (M.U )}{B : M.Ty Γ}
    (t : M.Tm Γ (S→ A B))
    (u : M.Tm Γ (M.El A)) → M.Tm Γ B
Sa {Γ} {A} {B} t u = tr (Tm _)
   (M.[][]T {σ =  M.< u >}{δ = M.wk {A = M.El A}} ◾ ap (λ s → B M.[ s ]T) M.wk∘<> ◾ M.[id]T) (t M.$ u)
--   = 
--     tr (λ B' → Σ Tmp (Tmw (₁ Γ) B'))
--     (Syntax.subT-wkT (₁ B) (₁ u))
--     (S1.app Γ A (S1.wkT Γ (S1.El Γ A) B) t u )

-- A: U, B : A -> U , ∙ : A , ▶ : (Γ : A) → B Γ → A , u : (Γ:A) → B Γ , el (Γ : A) →
{- 
ex1 : M.Con 
-- ex1 = M.∙ M.▶ {!? M.▶ ?!}
A,B,∙ = M.∙ M.▶ M.U M.▶ M.Π M.vz M.U M.▶
   M.El (M.vs M.vz)

A,B,∙⊢A : M.Tm A,B,∙ M.U
A,B,∙⊢A = (M.vs (M.vs M.vz))

ex1 = A,B,∙
   M.▶
   M.Π A,B,∙⊢A
   (S→ (Sa (M.vs (M.vs M.vz)) M.vz) (M.El (M.vs A,B,∙⊢A)))
   M.▶
   -- u
   M.Π (M.vs A,B,∙⊢A) (M.El {!!})
   M.▶
   {!!}
   -}


