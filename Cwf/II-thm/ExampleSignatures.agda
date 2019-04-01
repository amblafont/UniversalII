{-
Paper: sections 1.1-1.3, 3.2

This file contains some example QIIT signatures.
-}

{-# OPTIONS --rewriting #-}

module ExampleSignatures where

open import StrictLib hiding (id; _∘_)
open import Syntax

-- Abbreviations for de Bruijn variables and function spaces
--------------------------------------------------------------------------------

v0 : ∀ {Γ A} → Tm (Γ ▶ A) (A [ wk ]T)
v0 = vz

v1 : ∀ {Γ A B} → Tm (Γ ▶ A ▶ B) (A [ wk ∘ wk ]T)
v1 = vs v0

v2 : ∀ {Γ A B C} → Tm (Γ ▶ A ▶ B ▶ C) (A [ _ ]T)
v2 = vs v1

-- non-dependent inductive function
infixr 4 _⇒_
_⇒_ : ∀{Γ} → Tm Γ U → Ty Γ → Ty Γ
a ⇒ B = Π a (B [ wk ]T)

-- non-dependent metatheoretic function
infixr 4 _⇒̂_
_⇒̂_ : ∀ {Γ} → Set → Ty Γ → Ty Γ
T ⇒̂ B = ΠNI T (λ _ → B)

-- note: inductive function application is _$_
-- _@_ is not a syntactically valid Agda operator.

-- metatheoretic application
infixl 8 _$̂_
_$̂_ : ∀{Γ A}{B : A → Ty Γ} → Tm Γ (ΠNI A B) → (α : A) → Tm Γ (B α)
t $̂ α = appNI t α

--------------------------------------------------------------------------------

-- Natural numbers
Nat : Con
Nat = ∙
    ▶ U
    ▶ El v0
    ▶ (v1 ⇒ El v1)

open import Data.Nat

-- Integers (we import natural numbers from the metatheory)
Int : Con
Int = ∙
    ▶ U
    ▶ ℕ ⇒̂ ℕ ⇒̂ El v0
    ▶ ΠNI (ℕ × ℕ × ℕ × ℕ) λ {(a , b , c , d)   -- we bind 4 numbers at once for brevity
      → (a + d ≡ b + c) ⇒̂ Id v1 (v0 $̂ a $̂ b) (v0 $̂ c $̂ d)}

-- The ConTy example from section 3.2 doesn't typecheck in reasonable time.
-- Context extension _▶_ already kills Agda.

-- ConTy : Con
-- ConTy =
--       ∙
--     ▶ U                                -- Con : U
--     ▶ Π v0 U                           -- Ty  : Con → U
--     ▶ El v1                            -- ∙   : Con
--     ▶ Π v2 (Π (v2 $ v0) (El v4))       -- _▶_ : (Γ : Con) → Ty Γ → Con

-- Length-indexed vectors
Vec : Set → Con
Vec A =
      ∙
    ▶ ℕ ⇒̂ U
    ▶ El (v0 $̂ 0)
    ▶ ΠNI ℕ λ n → v1 $̂ n ⇒ El (v1 $̂ (1 + n))

-- Pointed type families
Fam* : Con
Fam* = ∙
     ▶ U             -- A : U
     ▶ v0 ⇒ U        -- B : A → U
     ▶ El v1         -- a : A
     ▶ El (v1 $ v0)  -- b : B a
