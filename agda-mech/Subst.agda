{-# OPTIONS --safe #-}

open import Axiom.Extensionality.Propositional as Ext
open import Agda.Primitive using (lzero)
module Subst (extensionality : Ext.Extensionality lzero lzero) where

open import Syntax
open import Data.Nat
open import Data.Fin as F using (Fin; cast; _↑ʳ_; toℕ; fromℕ)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_; refl; _≢_; cong; cong₂; sym; trans)

private
  variable
    n : ℕ
    m : ℕ
    n' : ℕ

-- lift by 1, zero remains unmoved
ext : Renaming m n → Renaming (suc m) (suc n)
ext ρ F.zero = F.zero
ext ρ (F.suc x) = F.suc (ρ x)

mutual
  renameV : Renaming m n → Value m → Value n
  renameV ρ (⁇ i σ) = ⁇ i (renameV ρ ∘ σ)
  renameV ρ (‵ x₁) = ‵ (ρ x₁)
  renameV ρ (ƛ x₁) = ƛ renameC (ext ρ) x₁
  renameV ρ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ = #handler⟨ renameC (ext ρ) cᵣ ⨟ op , renameC (ext (ext ρ)) cₒₚ ⟩
  renameC : Renaming m n → Computation m → Computation n
  renameC ρ (#ret v) = #ret (renameV ρ v)
  renameC ρ (v ∙ x₁) = renameV ρ v ∙ renameV ρ x₁
  renameC ρ (#let x₁ #in x₂) = #let renameC ρ x₁ #in renameC (ext ρ) x₂
  renameC ρ (⦃⁇⦄ i σ) = ⦃⁇⦄ i (renameV ρ ∘ σ)
  renameC ρ (#with h #handle x₁) = #with renameV ρ h #handle renameC ρ x₁
  renameC ρ (op ⟨ v ⨟ k ⟩) = op ⟨ renameV ρ v ⨟ renameC (ext ρ) k ⟩

liftV : Value n → Value (suc n)
liftV = renameV F.suc
liftC : Computation n → Computation (suc n)
liftC = renameC F.suc

-- lift a return clause into a handler resumption, preserving its binder
liftC-ret : Computation (suc n) → Computation (suc (suc n))
liftC-ret = renameC (ext F.suc)

-- lift an operation clause into a handler resumption, preserving its two binders
liftC-op : Computation (2+ n) → Computation (suc (2+ n))
liftC-op = renameC (ext (ext F.suc))

-- lift a substitution by 1
exts : Subst m n → Subst (suc m) (suc n)
exts σ F.zero = ‵ F.zero
exts σ (F.suc x) = liftV (σ x)

-- ext distribute rename composition 
ext-comp : ∀ {a b c} (ρ₂ : Renaming b c) (ρ₁ : Renaming a b) (t : Fin (suc a))
         → (ext ρ₂ ∘ ext ρ₁) t ≡ ext (ρ₂ ∘ ρ₁) t
ext-comp ρ₂ ρ₁ F.zero = refl
ext-comp ρ₂ ρ₁ (F.suc t) = refl

ext-comp-ex : ∀ {a b c} (ρ₂ : Renaming b c) (ρ₁ : Renaming a b) 
            → (ext ρ₂ ∘ ext ρ₁) ≡ ext (ρ₂ ∘ ρ₁)
ext-comp-ex ρ₂ ρ₁ = extensionality (ext-comp ρ₂ ρ₁)

-- rename composition
renameV-comp : ∀ {a b c} (ρ₂ : Renaming b c) (ρ₁ : Renaming a b) (v : Value a)
             → renameV ρ₂ (renameV ρ₁ v) ≡ renameV (ρ₂ ∘ ρ₁) v
renameC-comp : ∀ {a b c} (ρ₂ : Renaming b c) (ρ₁ : Renaming a b) (c : Computation a)
             → renameC ρ₂ (renameC ρ₁ c) ≡ renameC (ρ₂ ∘ ρ₁) c
-- lemma for binders
renameC-comp-ext : ∀ {a b c} (ρ₂ : Renaming b c) (ρ₁ : Renaming a b) (c : Computation (suc a))
                 → renameC (ext ρ₂) (renameC (ext ρ₁) c) ≡ renameC (ext (ρ₂ ∘ ρ₁)) c
renameC-comp-ext ρ₂ ρ₁ c rewrite renameC-comp (ext ρ₂) (ext ρ₁) c | ext-comp-ex ρ₂ ρ₁ = refl
renameV-comp ρ₂ ρ₁ (⁇ i σ) = cong (⁇ i) (extensionality λ t → renameV-comp ρ₂ ρ₁ (σ t))
renameV-comp ρ₂ ρ₁ (‵ x) = refl
renameV-comp ρ₂ ρ₁ (ƛ c) = cong ƛ_ (renameC-comp-ext ρ₂ ρ₁ c)
renameV-comp ρ₂ ρ₁ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ rewrite renameC-comp-ext ρ₂ ρ₁ cᵣ
                                                   | renameC-comp-ext (ext ρ₂) (ext ρ₁) cₒₚ
                                                   | ext-comp-ex ρ₂ ρ₁
                                                   = refl
renameC-comp ρ₂ ρ₁ (#ret v) = cong #ret (renameV-comp ρ₂ ρ₁ v)
renameC-comp ρ₂ ρ₁ (v ∙ w) = cong₂ _∙_ (renameV-comp ρ₂ ρ₁ v) (renameV-comp ρ₂ ρ₁ w)
renameC-comp ρ₂ ρ₁ (#let c₁ #in c₂) = cong₂ #let_#in_ (renameC-comp ρ₂ ρ₁ c₁) (renameC-comp-ext ρ₂ ρ₁ c₂)
renameC-comp ρ₂ ρ₁ (⦃⁇⦄ i σ) = cong (⦃⁇⦄ i) (extensionality λ t → renameV-comp ρ₂ ρ₁ (σ t))
renameC-comp ρ₂ ρ₁ (#with h #handle c) = cong₂ #with_#handle_ (renameV-comp ρ₂ ρ₁ h) (renameC-comp ρ₂ ρ₁ c)
renameC-comp ρ₂ ρ₁ (op ⟨ v ⨟ c ⟩) rewrite renameV-comp ρ₂ ρ₁ v | renameC-comp-ext ρ₂ ρ₁ c = refl

renameV-ext-lift-comm : ∀ {m n} (ρ : Renaming m n) (v : Value m)
                     → liftV (renameV ρ v) ≡ renameV (ext ρ) (liftV v)
renameV-ext-lift-comm ρ v rewrite renameV-comp F.suc ρ v | renameV-comp (ext ρ) F.suc v = refl

exts-comp-rename : ∀ {m n k} (σ : Subst n k) (ρ : Renaming m n) (t : Fin (suc m))
                 → exts (σ ∘ ρ) t ≡ (exts σ ∘ ext ρ) t
exts-comp-rename σ ρ F.zero = refl
exts-comp-rename σ ρ (F.suc t) = refl
exts-comp-rename-ex : ∀ {m n k} (σ : Subst n k) (ρ : Renaming m n) 
                    → exts (σ ∘ ρ) ≡ (exts σ ∘ ext ρ) 
exts-comp-rename-ex σ ρ = extensionality (exts-comp-rename σ ρ)

exts-rename-subst : ∀ {m n k} (ρ : Renaming n k) (σ : Subst m n) (t : Fin (suc m))
  → exts (renameV ρ ∘ σ) t ≡ renameV (ext ρ) (exts σ t)
exts-rename-subst ρ σ F.zero = refl
exts-rename-subst ρ σ (F.suc t) = renameV-ext-lift-comm ρ (σ t)
exts-rename-subst-ex : ∀ {m n k} (ρ : Renaming n k) (σ : Subst m n) 
  → exts (renameV ρ ∘ σ) ≡ renameV (ext ρ) ∘ exts σ
exts-rename-subst-ex ρ σ = extensionality (exts-rename-subst ρ σ)

mutual
  -- substitution composition σ₁[ σ₂ ], σ₁ : n' → m, σ₂ : m → n
  _∘ₛ_ : Subst m n → Subst n' m → Subst n' n
  σ₂ ∘ₛ σ₁ = substV σ₂ ∘ σ₁ 

  substV : Subst m n → Value m → Value n
  substV σ (⁇ i σ') = ⁇ i (σ ∘ₛ σ')
  substV σ (‵ x) = σ x
  substV σ (ƛ x) = ƛ substC (exts σ) x
  substV σ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ = #handler⟨ substC (exts σ) cᵣ ⨟ op , substC (exts (exts σ)) cₒₚ ⟩

  substC : Subst m n → Computation m → Computation n
  substC σ (#ret v) = #ret (substV σ v)
  substC σ (v ∙ x₁) = substV σ v ∙ substV σ x₁
  substC σ (#let x₁ #in x₂) = #let substC σ x₁ #in substC (exts σ) x₂
  substC σ (⦃⁇⦄ i σ') = ⦃⁇⦄ i (σ ∘ₛ σ')
  substC σ (#with h #handle x₁) = #with substV σ h #handle substC σ x₁ 
  substC σ (op ⟨ v ⨟ k ⟩) = op ⟨ substV σ v ⨟ substC (exts σ) k ⟩
  
substV-rename : ∀ {m n k} (σ : Subst n k) (ρ : Renaming m n) (v : Value m)
  → substV σ (renameV ρ v) ≡ substV (σ ∘ ρ) v
substC-rename : ∀ {m n k} (σ : Subst n k) (ρ : Renaming m n) (c : Computation m)
  → substC σ (renameC ρ c) ≡ substC (σ ∘ ρ) c

substV-rename σ ρ (⁇ i σᵢ) = cong (⁇ i) (extensionality λ t → substV-rename σ ρ (σᵢ t))
substV-rename σ ρ (‵ x) = refl
substV-rename σ ρ (ƛ c) rewrite exts-comp-rename-ex σ ρ | substC-rename (exts σ) (ext ρ) c = refl
substV-rename σ ρ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ rewrite exts-comp-rename-ex σ ρ 
                                                 | substC-rename (exts σ) (ext ρ) cᵣ
                                                 | exts-comp-rename-ex (exts σ) (ext ρ) 
                                                 | substC-rename (exts (exts σ)) (ext (ext ρ)) cₒₚ = refl
substC-rename σ ρ (#ret v) = cong #ret (substV-rename σ ρ v)
substC-rename σ ρ (v ∙ w) = cong₂ _∙_ (substV-rename σ ρ v) (substV-rename σ ρ w)
substC-rename σ ρ (#let c₁ #in c₂) rewrite exts-comp-rename-ex σ ρ 
                                         | substC-rename σ ρ c₁ 
                                         | substC-rename (exts σ) (ext ρ) c₂ = refl
substC-rename σ ρ (⦃⁇⦄ i σ₁) = cong (⦃⁇⦄ i) (extensionality λ t → substV-rename σ ρ (σ₁ t))
substC-rename σ ρ (#with h #handle c) = cong₂ #with_#handle_ (substV-rename σ ρ h) (substC-rename σ ρ c)
substC-rename σ ρ (op ⟨ v ⨟ k ⟩) rewrite substV-rename σ ρ v 
                                      | exts-comp-rename-ex σ ρ 
                                      | substC-rename (exts σ) (ext ρ) k = refl

-- rename-subst comm
renameV-subst : ∀ {m n k} (ρ : Renaming n k) (σ : Subst m n) (v : Value m)
  → renameV ρ (substV σ v) ≡ substV (renameV ρ ∘ σ) v
renameC-subst : ∀ {m n k} (ρ : Renaming n k) (σ : Subst m n) (c : Computation m)
  → renameC ρ (substC σ c) ≡ substC (renameV ρ ∘ σ) c

renameV-subst ρ σ (⁇ i σᵢ) = cong (⁇ i) (extensionality λ t → renameV-subst ρ σ (σᵢ t))
renameV-subst ρ σ (‵ x) = refl
renameV-subst ρ σ (ƛ c) rewrite exts-rename-subst-ex ρ σ | renameC-subst (ext ρ) (exts σ) c = refl
renameV-subst ρ σ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ rewrite exts-rename-subst-ex ρ σ 
                                                 | renameC-subst (ext ρ) (exts σ) cᵣ 
                                                 | exts-rename-subst-ex (ext ρ) (exts σ) 
                                                 | renameC-subst (ext (ext ρ)) (exts (exts σ)) cₒₚ
                                                 = refl
renameC-subst ρ σ (#ret v) = cong #ret (renameV-subst ρ σ v)
renameC-subst ρ σ (v ∙ w) = cong₂ _∙_ (renameV-subst ρ σ v) (renameV-subst ρ σ w)
renameC-subst ρ σ (#let c₁ #in c₂) rewrite exts-rename-subst-ex ρ σ 
                                         | renameC-subst ρ σ c₁
                                         | renameC-subst (ext ρ) (exts σ) c₂
                                         = refl
renameC-subst ρ σ (⦃⁇⦄ i σ₁) = cong (⦃⁇⦄ i) (extensionality λ t → renameV-subst ρ σ (σ₁ t))
renameC-subst ρ σ (#with h #handle c) = cong₂ #with_#handle_ (renameV-subst ρ σ h) (renameC-subst ρ σ c)
renameC-subst ρ σ (op ⟨ v ⨟ c ⟩) rewrite renameV-subst ρ σ v 
                                      | exts-rename-subst-ex ρ σ 
                                      | renameC-subst (ext ρ) (exts σ) c = refl

substV-exts-lift : ∀ {m n}
  → (σ : Subst m n)
  → (v : Value m)
  → substV (exts σ) (liftV v) ≡ liftV (substV σ v)
substV-exts-lift σ v rewrite substV-rename (exts σ) F.suc v | renameV-subst F.suc σ v = refl

-- substitution commutes with the resumption lifts used in handler rules
private
  exts-ext-suc : ∀ {m n} (σ : Subst m n) (x : Fin (suc m))
    → exts (exts σ) (ext F.suc x) ≡ renameV (ext F.suc) (exts σ x)
  exts-ext-suc σ F.zero = refl
  exts-ext-suc σ (F.suc x) = renameV-ext-lift-comm F.suc (σ x)

  exts²-ext²-suc : ∀ {m n} (σ : Subst m n) (x : Fin (2+ m))
    → exts (exts (exts σ)) (ext (ext F.suc) x) ≡ renameV (ext (ext F.suc)) (exts (exts σ) x)
  exts²-ext²-suc σ F.zero = refl
  exts²-ext²-suc σ (F.suc F.zero) = refl
  exts²-ext²-suc σ (F.suc (F.suc x)) =
    trans
      (cong liftV (renameV-ext-lift-comm F.suc (σ x)))
      (renameV-ext-lift-comm (ext F.suc) (liftV (σ x)))

substC-exts-liftC-ret : ∀ {m n}
  → (σ : Subst m n)
  → (c : Computation (suc m))
  → substC (exts (exts σ)) (liftC-ret c) ≡ liftC-ret (substC (exts σ) c)
substC-exts-liftC-ret σ c rewrite substC-rename (exts (exts σ)) (ext F.suc) c
                                  | renameC-subst (ext F.suc) (exts σ) c
                                  | extensionality (exts-ext-suc σ) = refl

substC-exts²-liftC-op : ∀ {m n}
  → (σ : Subst m n)
  → (c : Computation (2+ m))
  → substC (exts (exts (exts σ))) (liftC-op c) ≡ liftC-op (substC (exts (exts σ)) c)
substC-exts²-liftC-op σ c rewrite substC-rename (exts (exts (exts σ))) (ext (ext F.suc)) c
                                   | renameC-subst (ext (ext F.suc)) (exts (exts σ)) c
                                   | extensionality (exts²-ext²-suc σ) = refl

exts-comp : ∀ {m n k}
  → (σ₂ : Subst n k)
  → (σ₁ : Subst m n)
  → (t : Fin (suc m))
  → (exts σ₂ ∘ₛ exts σ₁) t ≡ exts (σ₂ ∘ₛ σ₁) t
exts-comp σ₂ σ₁ F.zero = refl
exts-comp σ₂ σ₁ (F.suc t) = substV-exts-lift σ₂ (σ₁ t)
exts-comp-ex : ∀ {m n k}
  → (σ₂ : Subst n k)
  → (σ₁ : Subst m n)
  → (exts σ₂ ∘ₛ exts σ₁) ≡ exts (σ₂ ∘ₛ σ₁) 
exts-comp-ex σ₂ σ₁ = extensionality (exts-comp σ₂ σ₁)

-- substitution composition
substV-comp : ∀ {a b c} (σ₂ : Subst b c) (σ₁ : Subst a b) (v : Value a)
            → substV σ₂ (substV σ₁ v) ≡ substV (σ₂ ∘ₛ σ₁) v
substC-comp : ∀ {a b c} (σ₂ : Subst b c) (σ₁ : Subst a b) (c : Computation a)
            → substC σ₂ (substC σ₁ c) ≡ substC (σ₂ ∘ₛ σ₁) c
substV-comp σ₂ σ₁ (⁇ i σᵢ) = cong (⁇ i) (extensionality λ t → substV-comp σ₂ σ₁ (σᵢ t))
substV-comp σ₂ σ₁ (‵ x) = refl
substV-comp σ₂ σ₁ (ƛ c) rewrite substC-comp (exts σ₂) (exts σ₁) c | exts-comp-ex σ₂ σ₁ = refl
substV-comp σ₂ σ₁ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ rewrite substC-comp (exts σ₂) (exts σ₁) cᵣ 
                                                 | substC-comp (exts (exts σ₂)) (exts (exts σ₁)) cₒₚ 
                                                 | exts-comp-ex (exts σ₂) (exts σ₁) 
                                                 | exts-comp-ex σ₂ σ₁ = refl
substC-comp σ₂ σ₁ (#ret v) = cong #ret (substV-comp σ₂ σ₁ v)
substC-comp σ₂ σ₁ (v ∙ w) = cong₂ _∙_ (substV-comp σ₂ σ₁ v) (substV-comp σ₂ σ₁ w)
substC-comp σ₂ σ₁ (#let c₁ #in c₂) rewrite substC-comp σ₂ σ₁ c₁ 
                                         | substC-comp (exts σ₂) (exts σ₁) c₂ 
                                         | exts-comp-ex σ₂ σ₁ = refl
substC-comp σ₂ σ₁ (⦃⁇⦄ i σ) = cong (⦃⁇⦄ i) (extensionality λ t → substV-comp σ₂ σ₁ (σ t))
substC-comp σ₂ σ₁ (#with h #handle c) rewrite substV-comp σ₂ σ₁ h | substC-comp σ₂ σ₁ c = refl
substC-comp σ₂ σ₁ (op ⟨ v ⨟ c ⟩) rewrite substV-comp σ₂ σ₁ v 
                                      | substC-comp (exts σ₂) (exts σ₁) c 
                                      | exts-comp-ex σ₂ σ₁ = refl

-- rename/subst interaction lemmas used by hole-filling commutativity proofs.
rename-subst-v : ∀ {m n k}
  → (ρ : Renaming n k)
  → (σ : Subst m n)
  → (v : Value m)
  → substV (renameV ρ ∘ σ) v ≡ renameV ρ (substV σ v)
rename-subst-v ρ σ v = sym (renameV-subst ρ σ v)

--   rename-subst-c : ∀ {m n k}
--     → (ρ : Renaming n k)
--     → (c : Computation m)
--     → (σ : Subst m n)
--     → substC (renameV ρ ∘ σ) c ≡ renameC ρ (substC σ c)

-- substitute index 0
subst-zero : Value n → Fin (suc n) → Value n
subst-zero x F.zero = x
subst-zero x (F.suc x₁) = ‵ x₁

infix 70 _[_]v
infix 70 _[_]c
infix 70 _[_⨟_]c
infix 70 _[_]ₛ
-- substitute index 0
_[_]v : Value (suc n) → Value n → Value n
N [ M ]v = substV (subst-zero M) N

-- substitute index 0
_[_]c : Computation (suc n) → Value n → Computation n
N [ M ]c = substC (subst-zero M) N

-- substitute index 0 and 1
_[_⨟_]c : Computation (2+ n) → Value n → Value n → Computation n
N [ M1 ⨟ M2 ]c = substC (subst-zero M2 ∘ₛ exts (subst-zero M1)) N

-- substitute index 0 for substitions
_[_]ₛ : Subst m (suc n) → Value n → Subst m n
σ [ M ]ₛ = subst-zero M ∘ₛ σ

-- iterated weakening of renamings and substitutions
ext^ : ∀ k {n m} → Renaming n m → Renaming (k + n) (k + m)
ext^ zero    ρ = ρ
ext^ (suc k) ρ = ext (ext^ k ρ)

exts^ : ∀ k {n m} → Subst n m → Subst (k + n) (k + m)
exts^ zero    σ = σ
exts^ (suc k) σ = exts (exts^ k σ)

-- iterated lifting of a single-variable substitution;
-- its domain is written as (suc (k + n)) so that the outer ext used
-- in the renaming side has a matching index.
exts-subst-zero^ : ∀ k {n} → Value n → Subst (suc (k + n)) (k + n)
exts-subst-zero^ zero    V = subst-zero V
exts-subst-zero^ (suc k) V = exts (exts-subst-zero^ k V)

-- renaming commutes with iterated substitution: variable case
renameV-ext-subst-var :
  ∀ k {n m} (ρ : Renaming n m) (V : Value n) (x : Fin (suc (k + n)))
  → renameV (ext^ k ρ) ((exts-subst-zero^ k V) x)
  ≡ (exts-subst-zero^ k (renameV ρ V)) (ext (ext^ k ρ) x)
renameV-ext-subst-var zero    ρ V F.zero    = refl
renameV-ext-subst-var zero    ρ V (F.suc y) = refl
renameV-ext-subst-var (suc k) ρ V F.zero    = refl
renameV-ext-subst-var (suc k) ρ V (F.suc y) =
  trans
    (sym (renameV-ext-lift-comm (ext^ k ρ) ((exts-subst-zero^ k V) y)))
    (cong liftV (renameV-ext-subst-var k ρ V y))

-- renaming commutes with iterated single-variable substitution
mutual
  renameV-ext-subst : ∀ {n m k} {ρ : Renaming n m} {V : Value n} {v : Value (suc (k + n))}
    → renameV (ext^ k ρ) (substV (exts-subst-zero^ k V) v)
    ≡ substV (exts-subst-zero^ k (renameV ρ V)) (renameV (ext (ext^ k ρ)) v)
  renameV-ext-subst {k = k} {ρ = ρ} {V} {‵ x} =
    renameV-ext-subst-var k ρ V x
  renameV-ext-subst {k = k} {ρ = ρ} {V} {⁇ i σ} =
    cong (⁇ i) (extensionality λ t → renameV-ext-subst {k = k} {ρ = ρ} {V} {v = σ t})
  renameV-ext-subst {k = k} {ρ = ρ} {V} {ƛ c} =
    cong ƛ_ (renameC-ext-subst {k = suc k} {ρ = ρ} {V} {c})
  renameV-ext-subst {k = k} {ρ = ρ} {V} {#handler⟨ cᵣ ⨟ op , cₒₚ ⟩} =
    cong₂ (λ cᵣ' cₒₚ' → #handler⟨ cᵣ' ⨟ op , cₒₚ' ⟩)
      (renameC-ext-subst {k = suc k} {ρ = ρ} {V} {cᵣ})
      (renameC-ext-subst {k = suc (suc k)} {ρ = ρ} {V} {cₒₚ})

  renameC-ext-subst : ∀ {n m k} {ρ : Renaming n m} {V : Value n} {c : Computation (suc (k + n))}
    → renameC (ext^ k ρ) (substC (exts-subst-zero^ k V) c)
    ≡ substC (exts-subst-zero^ k (renameV ρ V)) (renameC (ext (ext^ k ρ)) c)
  renameC-ext-subst {k = k} {ρ = ρ} {V} {#ret v} =
    cong #ret (renameV-ext-subst {k = k} {ρ = ρ} {V} {v})
  renameC-ext-subst {k = k} {ρ = ρ} {V} {v₁ ∙ v₂} =
    cong₂ _∙_ (renameV-ext-subst {k = k} {ρ = ρ} {V} {v₁}) (renameV-ext-subst {k = k} {ρ = ρ} {V} {v₂})
  renameC-ext-subst {k = k} {ρ = ρ} {V} {#let M #in N} =
    cong₂ #let_#in_
      (renameC-ext-subst {k = k} {ρ = ρ} {V} {M})
      (renameC-ext-subst {k = suc k} {ρ = ρ} {V} {N})
  renameC-ext-subst {k = k} {ρ = ρ} {V} {⦃⁇⦄ i σ} =
    cong (⦃⁇⦄ i) (extensionality λ t → renameV-ext-subst {k = k} {ρ = ρ} {V} {v = σ t})
  renameC-ext-subst {k = k} {ρ = ρ} {V} {#with h #handle c} =
    cong₂ #with_#handle_
      (renameV-ext-subst {k = k} {ρ = ρ} {V} {h})
      (renameC-ext-subst {k = k} {ρ = ρ} {V} {c})
  renameC-ext-subst {k = k} {ρ = ρ} {V} {op ⟨ v ⨟ k' ⟩} =
    cong₂ (λ v'' k'' → op ⟨ v'' ⨟ k'' ⟩)
      (renameV-ext-subst {k = k} {ρ = ρ} {V} {v})
      (renameC-ext-subst {k = suc k} {ρ = ρ} {V} {k'})

-- ext and suc commute
ext-suc-comm : ∀ {n m} (ρ : Renaming n m) (x : Fin n)
  → (ext ρ ∘ F.suc) x ≡ (F.suc ∘ ρ) x
ext-suc-comm ρ F.zero = refl
ext-suc-comm ρ (F.suc x) = refl

ext-suc-comm-ex : ∀ {n m} (ρ : Renaming n m)
  → ext ρ ∘ F.suc ≡ F.suc ∘ ρ
ext-suc-comm-ex ρ = extensionality (ext-suc-comm ρ)

-- two nested ext and one suc commute
ext-ext-suc-comm : ∀ {n m} (ρ : Renaming n m) (x : Fin (suc n))
  → (ext (ext ρ) ∘ ext F.suc) x ≡ (ext F.suc ∘ ext ρ) x
ext-ext-suc-comm ρ F.zero = refl
ext-ext-suc-comm ρ (F.suc x) = refl

ext-ext-suc-comm-ex : ∀ {n m} (ρ : Renaming n m)
  → ext (ext ρ) ∘ ext F.suc ≡ ext F.suc ∘ ext ρ
ext-ext-suc-comm-ex ρ = extensionality (ext-ext-suc-comm ρ)

-- two nested ext/one suc commute (used in op-let case)
renameC-ext-comm-suc : ∀ {n m} (ρ : Renaming n m) (c : Computation (suc n))
  → renameC (ext (ext ρ)) (renameC (ext F.suc) c) ≡ renameC (ext F.suc) (renameC (ext ρ) c)
renameC-ext-comm-suc ρ c =
  trans
    (renameC-comp (ext (ext ρ)) (ext F.suc) c)
    (trans
      (cong (λ ρ' → renameC ρ' c) (ext-ext-suc-comm-ex ρ))
      (sym (renameC-comp (ext F.suc) (ext ρ) c)))

-- renaming commutes with the resumption lifts used in handler rules
renameC-liftC-ret-comm : ∀ {n m} (ρ : Renaming n m) (c : Computation (suc n))
  → renameC (ext (ext ρ)) (liftC-ret c) ≡ liftC-ret (renameC (ext ρ) c)
renameC-liftC-ret-comm ρ c = renameC-ext-comm-suc ρ c

renameC-liftC-op-comm : ∀ {n m} (ρ : Renaming n m) (c : Computation (2+ n))
  → renameC (ext (ext (ext ρ))) (liftC-op c) ≡ liftC-op (renameC (ext (ext ρ)) c)
renameC-liftC-op-comm ρ c =
  trans
    (renameC-comp (ext (ext (ext ρ))) (ext (ext F.suc)) c)
    (trans
      (cong (λ ρ' → renameC ρ' c)
        (trans
          (ext-comp-ex (ext (ext ρ)) (ext F.suc))
          (trans
            (cong ext (ext-ext-suc-comm-ex ρ))
            (sym (ext-comp-ex (ext F.suc) (ext ρ))))))
      (sym (renameC-comp (ext (ext F.suc)) (ext (ext ρ)) c)))

-- rename commutes with single-variable substitution at index 0
renameV-subst-zero-comm : ∀ {n m} (ρ : Renaming n m) (M : Value n) (x : Fin (suc n))
  → (renameV ρ ∘ subst-zero M) x ≡ (subst-zero (renameV ρ M) ∘ ext ρ) x
renameV-subst-zero-comm ρ M F.zero = refl
renameV-subst-zero-comm ρ M (F.suc x) = refl

renameV-subst-zero-comm-ex : ∀ {n m} (ρ : Renaming n m) (M : Value n)
  → renameV ρ ∘ subst-zero M ≡ subst-zero (renameV ρ M) ∘ ext ρ
renameV-subst-zero-comm-ex ρ M = extensionality (renameV-subst-zero-comm ρ M)

-- renaming commutes with double single-variable substitution
renameC-ext-subst-⨟ : ∀ {n m} {ρ : Renaming n m} {M1 M2 : Value n} {N : Computation (2+ n)}
  → renameC ρ (N [ M1 ⨟ M2 ]c)
  ≡ (renameC (ext (ext ρ)) N) [ renameV ρ M1 ⨟ renameV ρ M2 ]c
renameC-ext-subst-⨟ {ρ = ρ} {M1} {M2} {N} =
  trans
    (renameC-subst ρ (subst-zero M2 ∘ₛ exts (subst-zero M1)) N)
    (trans
      (cong (λ σ → substC σ N) (extensionality helper))
      (sym (substC-rename (subst-zero (renameV ρ M2) ∘ₛ exts (subst-zero (renameV ρ M1))) (ext (ext ρ)) N)))
  where
    helper : ∀ x
      → (renameV ρ ∘ (subst-zero M2 ∘ₛ exts (subst-zero M1))) x
      ≡ ((subst-zero (renameV ρ M2) ∘ₛ exts (subst-zero (renameV ρ M1))) ∘ ext (ext ρ)) x
    helper F.zero = refl
    helper (F.suc F.zero) =
      trans
        (renameV-subst ρ (subst-zero M2) (renameV F.suc M1))
        (trans
          (cong (λ σ → substV σ (renameV F.suc M1)) (renameV-subst-zero-comm-ex ρ M2))
          (trans
            (sym (substV-rename (subst-zero (renameV ρ M2)) (ext ρ) (renameV F.suc M1)))
            (cong (substV (subst-zero (renameV ρ M2)))
              (trans
                (renameV-comp (ext ρ) F.suc M1)
                (trans
                  (cong (λ f → renameV f M1) (ext-suc-comm-ex ρ))
                  (sym (renameV-comp F.suc ρ M1)))))))
    helper (F.suc (F.suc y)) = refl

