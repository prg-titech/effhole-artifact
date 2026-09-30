{-# OPTIONS --safe #-}

module Syntax where
open import Data.Nat
open import Data.Fin as F using (Fin; cast; _↑ʳ_; toℕ; fromℕ)

infixr 10 ƛ_
infixl 60 _∙_
infix 60 _⟨_⨟_⟩

private
  variable
    n : ℕ
    m : ℕ
    n' : ℕ

data Value : ℕ → Set
data Computation : ℕ → Set

Subst : ℕ → ℕ → Set
Subst m n = Fin m → Value n

Renaming : ℕ → ℕ → Set
Renaming m n = Fin m → Fin n

data Value where
  ⁇ : (i : ℕ) (σ : Subst m n) → Value n
  ‵ : (x : Fin n) → Value n
  ƛ_ : (c : Computation (suc n)) → Value n
  #handler⟨_⨟_,_⟩ : (cᵣ : Computation (suc n)) → (op : ℕ) → (cₒₚ : Computation (2+ n)) → Value n

data Computation where
  #ret : (v : Value n) → Computation n
  ⦃⁇⦄ : (i : ℕ) (σ : Subst m n) → Computation n
  #with_#handle_ : (h : Value n) → (c : Computation n) → Computation n
  _⟨_⨟_⟩ : (op : ℕ) → (v : Value n) → (k : Computation (suc n)) → Computation n
  _∙_ : (v₁ : Value n) → (v₂ : Value n) → Computation n
  #let_#in_ : (c₁ : Computation n) → (c₂ : Computation (suc n)) → Computation n
