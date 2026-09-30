{-# OPTIONS --safe #-}

open import Axiom.Extensionality.Propositional as Ext
open import Agda.Primitive using (lzero)
module Scope (extensionality : Ext.Extensionality lzero lzero) where


open import Syntax
open import Subst extensionality
open import Data.Nat
open import Data.Fin as F using (Fin; cast; _↑ʳ_; toℕ; fromℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality as PE using (_≡_; refl; _≢_)
open import Data.Empty using (⊥; ⊥-elim)

private
  variable
    n : ℕ
    m : ℕ
    n' : ℕ

-- we still need a predicate if hole context matches term context
-- we need a type system for holes
-- checking whether all holes are in the context and have the same type (context length)
HoleContext : Set
HoleContext = ℕ → Maybe ℕ

infix 3 _⟨_↦_⟩
-- extend hole context
_⟨_↦_⟩ : HoleContext → ℕ → ℕ → HoleContext
(σ ⟨ u ↦ n ⟩) x with x ≟ u
...                | yes refl = just n
...                | no _     = σ x

⟨↦⟩≡ : ∀ (Δ : HoleContext) (u n : ℕ) → (Δ ⟨ u ↦ n ⟩) u ≡ just n
⟨↦⟩≡ Δ u n with u ≟ u
... | yes refl = refl
... | no k = ⊥-elim (k refl)

⟨↦⟩≢ : ∀ (Δ : HoleContext) (u u' n : ℕ) → u' ≢ u → (Δ ⟨ u ↦ n ⟩) u' ≡ Δ u'
⟨↦⟩≢ Δ u u' n u'≢u with u' ≟ u
... | yes eq = ⊥-elim (u'≢u eq)
... | no _ = refl

infix 2 _⨟_⨟_⊢v_
infix 2 _⨟_⨟_⊢c_
infix 2 _⨟_⨟_⊢_⦂_

-- we need to define it separately because it is not the same set of terms as the runtime one
data _⨟_⨟_⊢v_ : (Δv : HoleContext) → (Δc : HoleContext) → (n : ℕ) → Value n → Set
data _⨟_⨟_⊢c_ : (Δv : HoleContext) → (Δc : HoleContext) → (n : ℕ) → Computation n → Set
data _⨟_⨟_⊢_⦂_ : (Δv : HoleContext) → (Δc : HoleContext) → (n : ℕ) → Subst m n → ℕ → Set

data _⨟_⨟_⊢_⦂_ where
  sub : ∀ {Δv Δc} {σ : Subst m n} → (∀ {t} → Δv ⨟ Δc ⨟ n ⊢v σ t) → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m

data _⨟_⨟_⊢v_ where
  hole : ∀ {Δv Δc u} {σ : Subst n' n}
    → Δv u ≡ just n'
    → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ n'
    ----------------
    → Δv ⨟ Δc ⨟ n ⊢v ⁇ u σ

  var : ∀ {Δv Δc x} → Δv ⨟ Δc ⨟ n ⊢v ‵ x

  abs : ∀ {Δv Δc c}
   → Δv ⨟ Δc ⨟ suc n ⊢c c
   ---------------
   → Δv ⨟ Δc ⨟ n ⊢v ƛ c
  
  hand : ∀ {Δv Δc cᵣ cₒₚ op}
    → Δv ⨟ Δc ⨟ suc n ⊢c cᵣ
    → Δv ⨟ Δc ⨟ 2+ n ⊢c cₒₚ
    -----------------------------------
    → Δv ⨟ Δc ⨟ n ⊢v #handler⟨ cᵣ ⨟ op , cₒₚ ⟩

data _⨟_⨟_⊢c_ where
  ret : ∀ {Δv Δc v}
    → Δv ⨟ Δc ⨟ n ⊢v v
    ---------------
    → Δv ⨟ Δc ⨟ n ⊢c #ret v
  
  hole-c : ∀ {Δv Δc u} {σ : Subst n' n}
       → Δc u ≡ just n'
       → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ n'
       ----------------
       → Δv ⨟ Δc ⨟ n ⊢c ⦃⁇⦄ u σ

  #with : ∀ {Δv Δc h c}
      → Δv ⨟ Δc ⨟ n ⊢v h
      → Δv ⨟ Δc ⨟ n ⊢c c
      ----------------------------
      → Δv ⨟ Δc ⨟ n ⊢c #with h #handle c

  opcall : ∀ {Δv Δc v k op}
      → Δv ⨟ Δc ⨟ n ⊢v v
      → Δv ⨟ Δc ⨟ suc n ⊢c k
      ----------------------
      → Δv ⨟ Δc ⨟ n ⊢c op ⟨ v ⨟ k ⟩ 

  app : ∀ {Δv Δc v₁ v₂}
    → Δv ⨟ Δc ⨟ n ⊢v v₁
    → Δv ⨟ Δc ⨟ n ⊢v v₂
    ----------------
    → Δv ⨟ Δc ⨟ n ⊢c v₁ ∙ v₂

  bind : ∀ {Δv Δc c₁ c₂}
    → Δv ⨟ Δc ⨟ n ⊢c c₁
    → Δv ⨟ Δc ⨟ suc n ⊢c c₂
    ----------------
    → Δv ⨟ Δc ⨟ n ⊢c #let c₁ #in c₂

just≡ : ∀ {n} → just n ≡ just m → n ≡ m
just≡ refl = refl

-- renaming preserves type
mutual
  rename-value-typed : ∀ {Δv Δc m n} {v : Value m}
                    → (ρ : Renaming m n)
                    → Δv ⨟ Δc ⨟ m ⊢v v
                    → Δv ⨟ Δc ⨟ n ⊢v renameV ρ v

  rename-comp-typed : ∀ {Δv Δc m n} {c : Computation m}
                     → (ρ : Renaming m n)
                     → Δv ⨟ Δc ⨟ m ⊢c c
                     → Δv ⨟ Δc ⨟ n ⊢c renameC ρ c

  rename-value-typed {v = ⁇ u σ} ρ (hole h (sub p)) = hole h (sub (λ {t} → rename-value-typed ρ (p {t})))
  rename-value-typed ρ var = var
  rename-value-typed ρ (abs t-ok) = abs (rename-comp-typed (ext ρ) t-ok)
  rename-value-typed ρ (hand x x₁) = hand (rename-comp-typed (ext ρ) x) (rename-comp-typed (ext (ext ρ)) x₁)

  rename-comp-typed ρ (ret v-ok) = ret (rename-value-typed ρ v-ok)
  rename-comp-typed ρ (app l-ok r-ok) = app (rename-value-typed ρ l-ok) (rename-value-typed ρ r-ok)
  rename-comp-typed ρ (bind c₁-ok c₂-ok) = bind (rename-comp-typed ρ c₁-ok) (rename-comp-typed (ext ρ) c₂-ok)
  rename-comp-typed {c = ⦃⁇⦄ i σ} ρ (hole-c x (sub x₁)) = hole-c x (sub λ {t} → rename-value-typed ρ x₁)
  rename-comp-typed ρ (#with x x₁) = #with (rename-value-typed ρ x) (rename-comp-typed ρ x₁)
  rename-comp-typed ρ (opcall x x₁) = opcall (rename-value-typed ρ x) (rename-comp-typed (ext ρ) x₁)

  exts-typed : ∀ {Δv Δc m n} {σ : Subst m n}
    → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m
    → Δv ⨟ Δc ⨟ suc n ⊢ exts σ ⦂ suc m
  exts-typed (sub p) = sub (λ { {F.zero} → var; {F.suc x} → rename-value-typed F.suc (p {x})})

-- subst-zero preserves type
subst-zero-typed : ∀ {Δv Δc n} {v' : Value n}
                   → Δv ⨟ Δc ⨟ n ⊢v v'
                   → Δv ⨟ Δc ⨟ n ⊢ subst-zero v' ⦂ suc n
subst-zero-typed {Δv} {Δc} {n} {v'} v'-ok = sub (λ { {F.zero} → v'-ok ; {F.suc x} → var }) 

mutual
  subst-value-gen : ∀ {Δv Δc m n} {v : Value m} {σ : Subst m n}
    → Δv ⨟ Δc ⨟ m ⊢v v
    → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m
    → Δv ⨟ Δc ⨟ n ⊢v substV σ v

  subst-comp-gen : ∀ {Δv Δc m n} {c : Computation m} {σ : Subst m n}
    → Δv ⨟ Δc ⨟ m ⊢c c
    → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m
    → Δv ⨟ Δc ⨟ n ⊢c substC σ c

  subst-subst-gen : ∀ {Δv Δc m n n'} {σ₂ : Subst m n} {σ₁ : Subst n' m}
    → Δv ⨟ Δc ⨟ m ⊢ σ₁ ⦂ n'
    → Δv ⨟ Δc ⨟ n ⊢ σ₂ ⦂ m
    → Δv ⨟ Δc ⨟ n ⊢ (σ₂ ∘ₛ σ₁) ⦂ n'

  subst-value-gen (hole h σ₁-ok) σ₂-ok = hole h (subst-subst-gen σ₁-ok σ₂-ok)
  subst-value-gen var (sub p) = p
  subst-value-gen (abs t-ok) σ-ok = abs (subst-comp-gen t-ok (exts-typed σ-ok))
  subst-value-gen (hand x x₂) σ-ok = hand (subst-comp-gen x (exts-typed σ-ok)) 
                                          (subst-comp-gen x₂ (exts-typed (exts-typed σ-ok)))
  subst-comp-gen (ret v-ok) σ-ok = ret (subst-value-gen v-ok σ-ok)
  subst-comp-gen (app l-ok r-ok) σ-ok = app (subst-value-gen l-ok σ-ok) (subst-value-gen r-ok σ-ok)
  subst-comp-gen (bind c₁-ok c₂-ok) σ-ok = bind (subst-comp-gen c₁-ok σ-ok) (subst-comp-gen c₂-ok (exts-typed σ-ok))
  subst-comp-gen (hole-c x σ₁-ok) σ₂-ok = hole-c x (subst-subst-gen σ₁-ok σ₂-ok)
  subst-comp-gen (#with x x₁) σ-ok = #with (subst-value-gen x σ-ok) (subst-comp-gen x₁ σ-ok)
  subst-comp-gen (opcall x x₁) σ-ok = opcall (subst-value-gen x σ-ok) (subst-comp-gen x₁ (exts-typed σ-ok))
  subst-subst-gen (sub p) σ₂-ok = sub (λ {t} → subst-value-gen (p {t}) σ₂-ok)

-- substitution lemma
subst-subst : ∀ {Δv Δc} {σ : Subst m (suc n)} {v'}
  → Δv ⨟ Δc ⨟ suc n ⊢ σ ⦂ m
  → Δv ⨟ Δc ⨟ n ⊢v v'
  ------------------------
  → Δv ⨟ Δc ⨟ n ⊢ σ [ v' ]ₛ ⦂ m
subst-subst σ-ok v'-ok = subst-subst-gen σ-ok (subst-zero-typed v'-ok)

subst-value : ∀ {Δv Δc v v'}
  → Δv ⨟ Δc ⨟ suc n ⊢v v
  → Δv ⨟ Δc ⨟ n ⊢v v'
  ------------------
  → Δv ⨟ Δc ⨟ n ⊢v v [ v' ]v
subst-value v-ok v'-ok = subst-value-gen v-ok (subst-zero-typed v'-ok)

subst-comp : ∀ {Δv Δc c v}
  → Δv ⨟ Δc ⨟ suc n ⊢c c
  → Δv ⨟ Δc ⨟ n ⊢v v
  ------------------
  → Δv ⨟ Δc ⨟ n ⊢c c [ v ]c
subst-comp c-ok v-ok = subst-comp-gen c-ok (subst-zero-typed v-ok)
