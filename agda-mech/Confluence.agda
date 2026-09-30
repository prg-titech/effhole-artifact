{-# OPTIONS --safe #-}

open import Axiom.Extensionality.Propositional as Ext
open import Agda.Primitive using (lzero)
module Confluence (extensionality : Ext.Extensionality lzero lzero) where

open import Syntax
open import Subst extensionality
open import Semantics extensionality
open import Data.Nat
open import Data.Nat.Properties using (_≟_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_; refl; _≢_; cong; cong₂; sym; trans)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Data.Fin as F using (Fin; cast; _↑ʳ_; toℕ; fromℕ)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Empty using (⊥-elim)


infix 2 _⇛v_
infix 2 _⇛s_
infix 2 _⇛_

data _⇛v_ : ∀ {n} → Value n → Value n → Set
data _⇛_  : ∀ {n} → Computation n → Computation n → Set

-- Pointwise parallel reduction on substitutions.
record _⇛s_ {m n} (σ σ' : Subst m n) : Set where
  inductive
  field
    pf : ∀ {t} → σ t ⇛v σ' t

open _⇛s_ public


data _⇛v_ where
  p-var : ∀ {n} {x : Fin n}
        → ‵ x ⇛v ‵ x

  p-hole-v : ∀ {m n} {u} {σ σ' : Subst m n}
           → σ ⇛s σ' 
           → ⁇ u σ ⇛v ⁇ u σ'

  p-lam : ∀ {n} {M M' : Computation (suc n)}
        → M ⇛ M'
        → (ƛ M) ⇛v (ƛ M')

  p-handler : ∀ {n} {Nᵣ Nᵣ' : Computation (suc n)} {Nₒ Nₒ' : Computation (2+ n)} {op}
            → Nᵣ ⇛ Nᵣ'
            → Nₒ ⇛ Nₒ'
            → #handler⟨ Nᵣ ⨟ op , Nₒ ⟩ ⇛v #handler⟨ Nᵣ' ⨟ op , Nₒ' ⟩

data _⇛_ where
  p-ret : ∀ {n} {V V' : Value n}
        → V ⇛v V'
        → #ret V ⇛ #ret V'

  p-hole-c : ∀ {m n} {u} {σ σ' : Subst m n}
           → σ ⇛s σ'
           → ⦃⁇⦄ u σ ⇛ ⦃⁇⦄ u σ'

  p-app : ∀ {n} {V₁ V₁' V₂ V₂' : Value n}
        → V₁ ⇛v V₁'
        → V₂ ⇛v V₂'
        → V₁ ∙ V₂ ⇛ V₁' ∙ V₂'

  p-β : ∀ {n} {M M' : Computation (suc n)} {V V' : Value n}
      → M ⇛ M'
      → V ⇛v V'
      → (ƛ_ M) ∙ V ⇛ M' [ V' ]c

  p-let-cong : ∀ {n} {M₁ M₁' : Computation n} {M₂ M₂' : Computation (suc n)}
             → M₁ ⇛ M₁'
             → M₂ ⇛ M₂'
             → #let M₁ #in M₂ ⇛ #let M₁' #in M₂'

  p-β-let : ∀ {n} {V V' : Value n} {M₂ M₂' : Computation (suc n)}
          → V ⇛v V'
          → M₂ ⇛ M₂'
          → #let (#ret V) #in M₂ ⇛ M₂' [ V' ]c

  p-op-let : ∀ {n} {V V' : Value n} {K K' : Computation (suc n)} {M₂ M₂' : Computation (suc n)} {op}
           → V ⇛v V'
           → K ⇛ K'
           → M₂ ⇛ M₂'
           → #let (op ⟨ V ⨟ K ⟩) #in M₂ ⇛ op ⟨ V' ⨟ #let K' #in renameC (ext F.suc) M₂' ⟩

  p-with-cong : ∀ {n} {H H' : Value n} {M M' : Computation n}
              → H ⇛v H'
              → M ⇛ M'
              → #with H #handle M ⇛ #with H' #handle M'

  p-β-ret : ∀ {n} {Nᵣ Nᵣ' : Computation (suc n)} {Nₒ : Computation (2+ n)} {op} {V V' : Value n}
          → Nᵣ ⇛ Nᵣ'
          → V ⇛v V'
          → #with #handler⟨ Nᵣ ⨟ op , Nₒ ⟩ #handle #ret V ⇛ Nᵣ' [ V' ]c

  p-β-op-eq : ∀ {n} {Nᵣ Nᵣ' : Computation (suc n)} {Nₒ Nₒ' : Computation (2+ n)} {op}
                {V V' : Value n} {K K' : Computation (suc n)}
            → Nᵣ ⇛ Nᵣ'
            → Nₒ ⇛ Nₒ'
            → V ⇛v V'
            → K ⇛ K'
            → #with #handler⟨ Nᵣ ⨟ op , Nₒ ⟩ #handle op ⟨ V ⨟ K ⟩
              ⇛ Nₒ' [ V' ⨟ ƛ #with #handler⟨ liftC-ret Nᵣ' ⨟ op , liftC-op Nₒ' ⟩ #handle K' ]c

  p-β-op-neq : ∀ {n} {Nᵣ Nᵣ' : Computation (suc n)} {Nₒ Nₒ' : Computation (2+ n)} {op op'}
                 {V V' : Value n} {K K' : Computation (suc n)}
             → Nᵣ ⇛ Nᵣ'
             → Nₒ ⇛ Nₒ'
             → V ⇛v V'
             → K ⇛ K'
             → op ≢ op'
             → #with #handler⟨ Nᵣ ⨟ op , Nₒ ⟩ #handle op' ⟨ V ⨟ K ⟩
               ⇛ op' ⟨ V' ⨟ #with #handler⟨ liftC-ret Nᵣ' ⨟ op , liftC-op Nₒ' ⟩ #handle K' ⟩

  p-op : ∀ {n} {V V' : Value n} {K K' : Computation (suc n)} {op}
       → V ⇛v V'
       → K ⇛ K'
       → op ⟨ V ⨟ K ⟩ ⇛ op ⟨ V' ⨟ K' ⟩


-- Basic properties of parallel reduction

mutual
  ⇛v-refl : ∀ {n} {V : Value n} → V ⇛v V
  ⇛v-refl {n} {⁇ i σ} = p-hole-v (⇛s-refl {σ = σ})
  ⇛v-refl {n} {‵ x} = p-var
  ⇛v-refl {n} {ƛ c} = p-lam ⇛-refl
  ⇛v-refl {n} {#handler⟨ cᵣ ⨟ op , cₒₚ ⟩} = p-handler ⇛-refl ⇛-refl

  ⇛-refl : ∀ {n} {M : Computation n} → M ⇛ M
  ⇛-refl {n} {#ret v} = p-ret ⇛v-refl
  ⇛-refl {n} {⦃⁇⦄ i σ} = p-hole-c (⇛s-refl {σ = σ})
  ⇛-refl {n} {#with h #handle M} = p-with-cong ⇛v-refl ⇛-refl
  ⇛-refl {n} {op ⟨ v ⨟ M ⟩} = p-op ⇛v-refl ⇛-refl
  ⇛-refl {n} {v₁ ∙ v₂} = p-app ⇛v-refl ⇛v-refl
  ⇛-refl {n} {#let M #in M₁} = p-let-cong ⇛-refl ⇛-refl

  ⇛s-refl : ∀ {m n} {σ : Subst m n} → σ ⇛s σ
  ⇛s-refl = record { pf = λ {t} → ⇛v-refl }


-- Reflexive-transitive closure of parallel reduction.
data _>v=_⇛v_ {n} : Value n → ℕ → Value n → Set where
  ⇛vZ : ∀ {V : Value n} → V >v= 0 ⇛v V
  _⇛vS_ : ∀ {V W V' : Value n} {k : ℕ}
        → V ⇛v W
        → W >v= k ⇛v V'
        → V >v= suc k ⇛v V'

_⇛v*_ : ∀ {n} → Value n → Value n → Set
V ⇛v* V' = ∃[ k ] (V >v= k ⇛v V')

infixr 2 _⇛vS_
infix 2 _⇛v*_


data _>=_⇛_ {n} : Computation n → ℕ → Computation n → Set where
  ⇛Z : ∀ {M : Computation n} → M >= 0 ⇛ M
  _⇛S_ : ∀ {L M N : Computation n} {k : ℕ}
       → L ⇛ M
       → M >= k ⇛ N
       → L >= suc k ⇛ N

_⇛*_ : ∀ {n} → Computation n → Computation n → Set
M' ⇛* N' = ∃[ k ] (M' >= k ⇛ N')

infixr 2 _⇛S_
infix 2 _⇛*_


-- Conversion between single-step parallel reduction and its closure
⇛v-to⇛v* : ∀ {n} {V V' : Value n}
          → V ⇛v V'
          → V ⇛v* V'
⇛v-to⇛v* r = 1 , (r ⇛vS ⇛vZ)

⇛-to⇛* : ∀ {n} {M M' : Computation n}
        → M ⇛ M'
        → M ⇛* M'
⇛-to⇛* r = 1 , (r ⇛S ⇛Z)


-- Transitivity of the closures
trans⇛v* : ∀ {n} {V W V' : Value n}
          → V ⇛v* W
          → W ⇛v* V'
          → V ⇛v* V'
trans⇛v* (zero , ⇛vZ) x₁ = x₁
trans⇛v* (suc n , (x ⇛vS snd)) x₁ with trans⇛v* (n , snd) x₁
... | fst , snd₁ = suc fst , (x ⇛vS snd₁)

trans⇛* : ∀ {n} {L M N : Computation n}
         → L ⇛* M
         → M ⇛* N
         → L ⇛* N
trans⇛* (zero , ⇛Z) x₁ = x₁
trans⇛* (suc n , (x ⇛S snd)) x₁ with trans⇛* (n , snd) x₁
... | fst , snd₁ = suc fst , (x ⇛S snd₁)


-- Relating one-step / multi-step reduction with parallel reduction
-- One-step reduction is contained in parallel reduction
mutual
  -→v-to-⇛v : ∀ {n} {V V' : Value n}
            → V -→v V'
            → V ⇛v V'
  -→v-to-⇛v (ξ-ƛ x) = p-lam (-→-to-⇛ x)
  -→v-to-⇛v (ξ-hand₁ x) = p-handler (-→-to-⇛ x) ⇛-refl
  -→v-to-⇛v (ξ-hand₂ x) = p-handler ⇛-refl (-→-to-⇛ x)
  -→v-to-⇛v (ξ-hole-v x) = p-hole-v (-→s-to-⇛s x)

  -→-to-⇛ : ∀ {n} {M M' : Computation n}
          → M -→ M'
          → M ⇛ M'
  -→-to-⇛ β = p-β ⇛-refl ⇛v-refl
  -→-to-⇛ β-let = p-β-let ⇛v-refl ⇛-refl
  -→-to-⇛ op-let = p-op-let ⇛v-refl ⇛-refl ⇛-refl
  -→-to-⇛ β-ret = p-β-ret ⇛-refl ⇛v-refl
  -→-to-⇛ β-op-eq = p-β-op-eq ⇛-refl ⇛-refl ⇛v-refl ⇛-refl
  -→-to-⇛ (β-op-neq x) = p-β-op-neq ⇛-refl ⇛-refl ⇛v-refl ⇛-refl x
  -→-to-⇛ (ξ-ret x) = p-ret (-→v-to-⇛v x)
  -→-to-⇛ (ξ-hole-c x) = p-hole-c (-→s-to-⇛s x)
  -→-to-⇛ (ξ-app₁ x) = p-app (-→v-to-⇛v x) ⇛v-refl
  -→-to-⇛ (ξ-app₂ x) = p-app ⇛v-refl (-→v-to-⇛v x)
  -→-to-⇛ (ξ-let r) = p-let-cong (-→-to-⇛ r) ⇛-refl
  -→-to-⇛ (ξ-in r) = p-let-cong ⇛-refl (-→-to-⇛ r)
  -→-to-⇛ (ξ-with₁ x) = p-with-cong (-→v-to-⇛v x) ⇛-refl
  -→-to-⇛ (ξ-with₂ r) = p-with-cong ⇛v-refl (-→-to-⇛ r)
  -→-to-⇛ (ξ-op₁ x) = p-op (-→v-to-⇛v x) ⇛-refl
  -→-to-⇛ (ξ-op₂ r) = p-op ⇛v-refl (-→-to-⇛ r)

  -→s-to-⇛s : ∀ {m n} {σ σ' : Subst m n}
            → σ -→s σ'
            → σ ⇛s σ'
  -→s-to-⇛s r = record { pf = λ {t} → helper r t }
    where
      helper : ∀ {m n} {σ σ' : Subst m n}
             → σ -→s σ'
             → (t : Fin m) → σ t ⇛v σ' t
      helper (ξ-σ x x₁ x₂) t with t F.≟ x
      ... | yes refl = -→v-to-⇛v x₁
      ... | no k rewrite x₂ t k = ⇛v-refl


-- Multi-step reduction is contained in the reflexive-transitive closure of ⇛
-→v*-to⇛v* : ∀ {n} {V V' : Value n}
            → V -→v* V'
            → V ⇛v* V'
-→v*-to⇛v* (zero , -→vZ) = 0 , ⇛vZ
-→v*-to⇛v* (suc k , (x -→vS snd)) with -→v*-to⇛v* (k , snd)
... | (n , chain) = suc n , (-→v-to-⇛v x ⇛vS chain)

-→*-to⇛* : ∀ {n} {M M' : Computation n}
          → M -→* M'
          → M ⇛* M'
-→*-to⇛* (zero , -→Z) = 0 , ⇛Z
-→*-to⇛* (suc k , (x -→S snd)) with -→*-to⇛* (k , snd)
... | (n , chain) = suc n , (-→-to-⇛ x ⇛S chain)

-→s*-to-⇛s* : ∀ {m n} {σ σ' : Subst m n}
            → σ -→s* σ'
            → ∀ {t} → σ t ⇛v* σ' t
-→s*-to-⇛s* {m} {n} {σ} {σ'} r {t} = -→v*-to⇛v* (r t)


-- Parallel reduction is contained in multi-step reduction
mutual
  ⇛v-to-→v* : ∀ {n} {V V' : Value n}
            → V ⇛v V'
            → V -→v* V'
  ⇛v-to-→v* p-var = 0 , -→vZ
  ⇛v-to-→v* (p-hole-v x) = hole-v-multistep (⇛s-to-→s* x)
  ⇛v-to-→v* (p-lam x) = ξ-ƛ* (⇛-to-→* x)
  ⇛v-to-→v* (p-handler x x₁) = trans-→v* (ξ-hand₁* (⇛-to-→* x)) (ξ-hand₂* (⇛-to-→* x₁))

  ⇛-to-→* : ∀ {n} {M M' : Computation n}
          → M ⇛ M'
          → M -→* M'
  ⇛-to-→* (p-ret x) = ξ-ret* (⇛v-to-→v* x)
  ⇛-to-→* (p-hole-c x) = hole-c-multistep (⇛s-to-→s* x)
  ⇛-to-→* (p-app x x₁) = trans-→* (ξ-app₁* (⇛v-to-→v* x)) (ξ-app₂* (⇛v-to-→v* x₁))
  ⇛-to-→* (p-β p x) = trans-→* (ξ-app₁* (⇛v-to-→v* (p-lam p))) (trans-→* (ξ-app₂* (⇛v-to-→v* x)) (1 , (β -→S -→Z)))
  ⇛-to-→* (p-let-cong p p₁) = trans-→* (ξ-let* (⇛-to-→* p)) (ξ-in* (⇛-to-→* p₁))
  ⇛-to-→* (p-β-let x p) = trans-→* (ξ-let* (⇛-to-→* (p-ret x))) (trans-→* (ξ-in* (⇛-to-→* p)) (1 , (β-let -→S -→Z)))
  ⇛-to-→* (p-op-let x p p₁) = trans-→* (ξ-let* (ξ-op₁* (⇛v-to-→v* x))) 
                             (trans-→* (ξ-let* (ξ-op₂* (⇛-to-→* p))) 
                             (trans-→* (ξ-in* (⇛-to-→* p₁)) (1 , (op-let -→S -→Z))))
  ⇛-to-→* (p-with-cong x p) = trans-→* (ξ-with₁* (⇛v-to-→v* x)) (ξ-with₂* (⇛-to-→* p)) 
  ⇛-to-→* (p-β-ret p x) = trans-→* (ξ-with₁* (ξ-hand₁* (⇛-to-→* p))) 
                          (trans-→* (ξ-with₂* (ξ-ret* (⇛v-to-→v* x))) (1 , (β-ret -→S -→Z)))
  ⇛-to-→* (p-β-op-eq p p₁ x p₂) = trans-→* (ξ-with₁* (ξ-hand₁* (⇛-to-→* p))) 
                                  (trans-→* (ξ-with₁* (ξ-hand₂* (⇛-to-→* p₁))) 
                                  (trans-→* (ξ-with₂* (ξ-op₁* (⇛v-to-→v* x))) 
                                  (trans-→* (ξ-with₂* (ξ-op₂* (⇛-to-→* p₂))) (1 , (β-op-eq -→S -→Z)))))
  ⇛-to-→* (p-β-op-neq p p₁ x p₂ x₁) = trans-→* (ξ-with₁* (ξ-hand₁* (⇛-to-→* p))) 
                                      (trans-→* (ξ-with₁* (ξ-hand₂* (⇛-to-→* p₁)))
                                      (trans-→* (ξ-with₂* (ξ-op₁* (⇛v-to-→v* x))) 
                                      (trans-→* (ξ-with₂* (ξ-op₂* (⇛-to-→* p₂))) (1 , (β-op-neq x₁ -→S -→Z)))))
  ⇛-to-→* (p-op x p) = trans-→* (ξ-op₁* (⇛v-to-→v* x)) (ξ-op₂* (⇛-to-→* p))

  ⇛s-to-→s* : ∀ {m n} {σ σ' : Subst m n}
            → σ ⇛s σ'
            → σ -→s* σ'
  ⇛s-to-→s* p x = ⇛v-to-→v* (p .pf {x})


-- Parallel multi-step reduction is contained in multi-step reduction
⇛v*-to-→v* : ∀ {n} {V V' : Value n}
           → V ⇛v* V'
           → V -→v* V'
⇛v*-to-→v* (zero , ⇛vZ) = 0 , -→vZ
⇛v*-to-→v* (suc k , (x ⇛vS snd)) = trans-→v* (⇛v-to-→v* x) (⇛v*-to-→v* (k , snd))

⇛*-to-→* : ∀ {n} {M M' : Computation n}
         → M ⇛* M'
         → M -→* M'
⇛*-to-→* (zero , ⇛Z) = 0 , -→Z
⇛*-to-→* (suc k , (x ⇛S snd)) = trans-→* (⇛-to-→* x) (⇛*-to-→* (k , snd))


-- Renaming and lifting preserve parallel reduction
mutual
  renameV-preserves-⇛v : ∀ {n m} {V V' : Value n} {ρ : Renaming n m}
                       → V ⇛v V'
                       → renameV ρ V ⇛v renameV ρ V'
  renameV-preserves-⇛v p-var = p-var
  renameV-preserves-⇛v {ρ = ρ} (p-hole-v {σ = σ} {σ' = σ'} ps) =
    p-hole-v (record { pf = λ {t} → renameV-preserves-⇛v (ps .pf {t}) })
  renameV-preserves-⇛v (p-lam p) = p-lam (renameC-preserves-⇛ p)
  renameV-preserves-⇛v (p-handler p₁ p₂) =
    p-handler (renameC-preserves-⇛ p₁) (renameC-preserves-⇛ p₂)

  renameC-preserves-⇛ : ∀ {n m} {M M' : Computation n} {ρ : Renaming n m}
                      → M ⇛ M'
                      → renameC ρ M ⇛ renameC ρ M'
  renameC-preserves-⇛ (p-ret p) = p-ret (renameV-preserves-⇛v p)
  renameC-preserves-⇛ {ρ = ρ} (p-hole-c {σ = σ} {σ' = σ'} ps) =
    p-hole-c (record { pf = λ {t} → renameV-preserves-⇛v (ps .pf {t}) })
  renameC-preserves-⇛ (p-app p₁ p₂) =
    p-app (renameV-preserves-⇛v p₁) (renameV-preserves-⇛v p₂)
  renameC-preserves-⇛ {ρ = ρ} (p-β {M' = M'} {V' = V'} p x) rewrite
    renameC-ext-subst {k = 0} {ρ = ρ} {V = V'} {c = M'} =
    p-β (renameC-preserves-⇛ p) (renameV-preserves-⇛v x)
  renameC-preserves-⇛ (p-let-cong p p₁) =
    p-let-cong (renameC-preserves-⇛ p) (renameC-preserves-⇛ p₁)
  renameC-preserves-⇛ {ρ = ρ} (p-β-let {V' = V'} {M₂' = M₂'} x p) rewrite
    renameC-ext-subst {k = 0} {ρ = ρ} {V = V'} {c = M₂'} =
    p-β-let (renameV-preserves-⇛v x) (renameC-preserves-⇛ p)
  renameC-preserves-⇛ {ρ = ρ} (p-op-let {M₂' = M₂'} x p p₁) rewrite
    renameC-ext-comm-suc ρ M₂' =
    p-op-let (renameV-preserves-⇛v x) (renameC-preserves-⇛ p) (renameC-preserves-⇛ p₁)
  renameC-preserves-⇛ (p-with-cong p p₁) =
    p-with-cong (renameV-preserves-⇛v p) (renameC-preserves-⇛ p₁)
  renameC-preserves-⇛ {ρ = ρ} (p-β-ret {Nᵣ' = Nᵣ'} {V' = V'} p x) rewrite
    renameC-ext-subst {k = 0} {ρ = ρ} {V = V'} {c = Nᵣ'} =
    p-β-ret (renameC-preserves-⇛ p) (renameV-preserves-⇛v x)
  renameC-preserves-⇛ {ρ = ρ} (p-β-op-eq {Nᵣ' = Nᵣ'} {Nₒ' = Nₒ'} {op = op} {V' = V'} {K' = K'} p p₁ x p₂) rewrite
    renameC-ext-subst-⨟ {ρ = ρ} {M1 = V'}
      {M2 = ƛ #with #handler⟨ liftC-ret Nᵣ' ⨟ op , liftC-op Nₒ' ⟩ #handle K'}
      {N = Nₒ'}
    | renameC-liftC-ret-comm ρ Nᵣ'
    | renameC-liftC-op-comm ρ Nₒ' =
    p-β-op-eq (renameC-preserves-⇛ p) (renameC-preserves-⇛ p₁)
      (renameV-preserves-⇛v x) (renameC-preserves-⇛ p₂)
  renameC-preserves-⇛ {ρ = ρ} (p-β-op-neq {Nᵣ' = Nᵣ'} {Nₒ' = Nₒ'} {op = op} {op' = op'} {V' = V'} {K' = K'} p p₁ x p₂ x₁) rewrite
    renameC-liftC-ret-comm ρ Nᵣ'
    | renameC-liftC-op-comm ρ Nₒ' =
    p-β-op-neq (renameC-preserves-⇛ p) (renameC-preserves-⇛ p₁)
      (renameV-preserves-⇛v x) (renameC-preserves-⇛ p₂) x₁
  renameC-preserves-⇛ (p-op p p₁) =
    p-op (renameV-preserves-⇛v p) (renameC-preserves-⇛ p₁)

liftV-preserves-⇛v : ∀ {n} {V V' : Value n}
                   → V ⇛v V'
                   → liftV V ⇛v liftV V'
liftV-preserves-⇛v p = renameV-preserves-⇛v p

liftC-ret-preserves-⇛ : ∀ {n} {M M' : Computation (suc n)}
                      → M ⇛ M'
                      → liftC-ret M ⇛ liftC-ret M'
liftC-ret-preserves-⇛ p = renameC-preserves-⇛ p

liftC-op-preserves-⇛ : ∀ {n} {M M' : Computation (2+ n)}
                     → M ⇛ M'
                     → liftC-op M ⇛ liftC-op M'
liftC-op-preserves-⇛ p = renameC-preserves-⇛ p


-- Substitution lifting preserves parallel substitution
exts-preserves-⇛s : ∀ {m n} {σ σ' : Subst m n}
                  → σ ⇛s σ'
                  → exts σ ⇛s exts σ'
exts-preserves-⇛s p =
  record { pf = λ { {F.zero} → p-var
                  ; {F.suc x} → liftV-preserves-⇛v (p .pf {x}) } }

exts²-preserves-⇛s : ∀ {m n} {σ σ' : Subst m n}
                    → σ ⇛s σ'
                    → exts (exts σ) ⇛s exts (exts σ')
exts²-preserves-⇛s p =
  record { pf = λ { {F.zero} → p-var
                  ; {F.suc F.zero} → p-var
                  ; {F.suc (F.suc x)} → liftV-preserves-⇛v (liftV-preserves-⇛v (p .pf {x})) } }


-- Substitution preserves parallel reduction
private
  exts-id-lemma : ∀ {n} {σ : Subst n n} → (∀ x → σ x ≡ ‵ x) → ∀ x → exts σ x ≡ ‵ x
  exts-id-lemma p F.zero = refl
  exts-id-lemma p (F.suc x) = cong liftV (p x)

  mutual
    substV-id' : ∀ {n} {σ : Subst n n} → (∀ x → σ x ≡ ‵ x) → (v : Value n) → substV σ v ≡ v
    substV-id' p (⁇ i σᵢ) = cong (⁇ i) (extensionality λ t → substV-id' p (σᵢ t))
    substV-id' p (‵ x) = p x
    substV-id' p (ƛ c) = cong ƛ_ (substC-id' (exts-id-lemma p) c)
    substV-id' p #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ =
      cong₂ (λ cᵣ' cₒₚ' → #handler⟨ cᵣ' ⨟ op , cₒₚ' ⟩)
        (substC-id' (exts-id-lemma p) cᵣ)
        (substC-id' (exts-id-lemma (exts-id-lemma p)) cₒₚ)

    substC-id' : ∀ {n} {σ : Subst n n} → (∀ x → σ x ≡ ‵ x) → (c : Computation n) → substC σ c ≡ c
    substC-id' p (#ret v) = cong #ret (substV-id' p v)
    substC-id' p (v ∙ w) = cong₂ _∙_ (substV-id' p v) (substV-id' p w)
    substC-id' p (#let c₁ #in c₂) =
      cong₂ #let_#in_ (substC-id' p c₁) (substC-id' (exts-id-lemma p) c₂)
    substC-id' p (⦃⁇⦄ i σ) = cong (⦃⁇⦄ i) (extensionality λ t → substV-id' p (σ t))
    substC-id' p (#with h #handle c) =
      cong₂ #with_#handle_ (substV-id' p h) (substC-id' p c)
    substC-id' p (op ⟨ v ⨟ k ⟩) =
      cong₂ (λ v' k' → op ⟨ v' ⨟ k' ⟩) (substV-id' p v) (substC-id' (exts-id-lemma p) k)

  substV-id : ∀ {n} (v : Value n) → substV (λ x → ‵ x) v ≡ v
  substV-id v = substV-id' (λ x → refl) v

  substC-id : ∀ {n} (c : Computation n) → substC (λ x → ‵ x) c ≡ c
  substC-id c = substC-id' (λ x → refl) c

  rename-suc² : ∀ {n} → Renaming n (suc (suc n))
  rename-suc² x = F.suc (F.suc x)

  substV-double-lift : ∀ {n} (V₂ V₁ : Value n) (v : Value n)
    → substV (subst-zero V₂ ∘ₛ exts (subst-zero V₁)) (liftV (liftV v)) ≡ v
  substV-double-lift V₂ V₁ v =
    trans
      (substV-rename (subst-zero V₂ ∘ₛ exts (subst-zero V₁)) F.suc (renameV F.suc v))
      (trans
        (substV-rename ((subst-zero V₂ ∘ₛ exts (subst-zero V₁)) ∘ F.suc) F.suc v)
        (substV-id v))

  subst-zero-∘-exts : ∀ {m n} (σ : Subst m n) (V : Value m)
    → σ ∘ₛ subst-zero V ≡ subst-zero (substV σ V) ∘ₛ exts σ
  subst-zero-∘-exts σ V = extensionality helper
    where
      helper : ∀ t → (σ ∘ₛ subst-zero V) t ≡ (subst-zero (substV σ V) ∘ₛ exts σ) t
      helper F.zero = refl
      helper (F.suc t) =
        sym
          (trans
            (substV-rename (subst-zero (substV σ V)) F.suc (σ t))
            (substV-id (σ t)))

  substC-subst-zero-comm : ∀ {m n} (σ : Subst m n) (V : Value m) (M : Computation (suc m))
    → substC σ (M [ V ]c) ≡ substC (exts σ) M [ substV σ V ]c
  substC-subst-zero-comm σ V M =
    trans
      (substC-comp σ (subst-zero V) M)
      (trans
        (cong (λ τ → substC τ M) (subst-zero-∘-exts σ V))
        (sym (substC-comp (subst-zero (substV σ V)) (exts σ) M)))

  exts²-suc-comm : ∀ {m n} (σ : Subst m n) (t : Fin (suc m))
    → exts (exts σ) (ext F.suc t) ≡ renameV (ext F.suc) (exts σ t)
  exts²-suc-comm σ F.zero = refl
  exts²-suc-comm σ (F.suc t) =
    trans
      (renameV-comp F.suc F.suc (σ t))
      (trans
        (cong (λ ρ → renameV ρ (σ t)) (sym (ext-suc-comm-ex F.suc)))
        (sym (renameV-comp (ext F.suc) F.suc (σ t))))

  substC-exts-rename-comm : ∀ {m n} (σ : Subst m n) (M : Computation (suc m))
    → substC (exts (exts σ)) (renameC (ext F.suc) M) ≡ renameC (ext F.suc) (substC (exts σ) M)
  substC-exts-rename-comm σ M =
    trans
      (substC-rename (exts (exts σ)) (ext F.suc) M)
      (trans
        (cong (λ τ → substC τ M) (extensionality λ t → exts²-suc-comm σ t))
        (sym (renameC-subst (ext F.suc) (exts σ) M)))

  subst-zero-⨟-∘-exts² : ∀ {m n} (σ : Subst m n) (V₁ V₂ : Value m)
    → σ ∘ₛ (subst-zero V₂ ∘ₛ exts (subst-zero V₁))
    ≡ (subst-zero (substV σ V₂) ∘ₛ exts (subst-zero (substV σ V₁))) ∘ₛ exts (exts σ)
  subst-zero-⨟-∘-exts² σ V₁ V₂ = extensionality helper
    where
      helper : ∀ t → (σ ∘ₛ (subst-zero V₂ ∘ₛ exts (subst-zero V₁))) t
                   ≡ ((subst-zero (substV σ V₂) ∘ₛ exts (subst-zero (substV σ V₁))) ∘ₛ exts (exts σ)) t
      helper F.zero = refl
      helper (F.suc F.zero) =
        trans
          (cong (substV σ)
            (trans
              (substV-rename (subst-zero V₂) F.suc V₁)
              (substV-id V₁)))
          (sym
            (trans
              (substV-rename (subst-zero (substV σ V₂)) F.suc (substV σ V₁))
              (substV-id (substV σ V₁))))
      helper (F.suc (F.suc t)) =
        sym (substV-double-lift (substV σ V₂) (substV σ V₁) (σ t))

  substC-subst-⨟-comm : ∀ {m n} (σ : Subst m n) (V₁ V₂ : Value m) (M : Computation (2+ m))
    → substC σ (M [ V₁ ⨟ V₂ ]c) ≡ substC (exts (exts σ)) M [ substV σ V₁ ⨟ substV σ V₂ ]c
  substC-subst-⨟-comm σ V₁ V₂ M =
    trans
      (substC-comp σ (subst-zero V₂ ∘ₛ exts (subst-zero V₁)) M)
      (trans
        (cong (λ τ → substC τ M) (subst-zero-⨟-∘-exts² σ V₁ V₂))
        (sym (substC-comp (subst-zero (substV σ V₂) ∘ₛ exts (subst-zero (substV σ V₁))) (exts (exts σ)) M)))

private
  ⇛-resp-≡ : ∀ {n} {M N N' : Computation n} → M ⇛ N → N ≡ N' → M ⇛ N'
  ⇛-resp-≡ p refl = p

  substV-handler-σ : ∀ {m n} (σ' : Subst m n) (op : ℕ)
                       (Nᵣ' : Computation (suc m)) (Nₒ' : Computation (2+ m)) (K' : Computation (suc m))
                     → substV σ' (ƛ #with #handler⟨ liftC-ret Nᵣ' ⨟ op , liftC-op Nₒ' ⟩ #handle K')
                     ≡ ƛ #with #handler⟨ liftC-ret (substC (exts σ') Nᵣ') ⨟ op , liftC-op (substC (exts (exts σ')) Nₒ') ⟩ #handle substC (exts σ') K'
  substV-handler-σ σ' op Nᵣ' Nₒ' K' =
    cong ƛ_
      (cong₂ #with_#handle_
        (cong₂ (λ cᵣ cₒₚ → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩)
          (substC-exts-liftC-ret σ' Nᵣ')
          (substC-exts²-liftC-op σ' Nₒ'))
        refl)

  substC-handler-σ : ∀ {m n} (σ' : Subst m n) (op : ℕ)
                       (Nᵣ' : Computation (suc m)) (Nₒ' : Computation (2+ m)) (K' : Computation (suc m))
                     → #with #handler⟨ liftC-ret (substC (exts σ') Nᵣ') ⨟ op , liftC-op (substC (exts (exts σ')) Nₒ') ⟩ #handle substC (exts σ') K'
                     ≡ substC (exts σ') (#with #handler⟨ liftC-ret Nᵣ' ⨟ op , liftC-op Nₒ' ⟩ #handle K')
  substC-handler-σ σ' op Nᵣ' Nₒ' K' =
    sym
      (cong₂ #with_#handle_
        (cong₂ (λ cᵣ cₒₚ → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩)
          (substC-exts-liftC-ret σ' Nᵣ')
          (substC-exts²-liftC-op σ' Nₒ'))
        refl)

mutual
  substV-preserves-⇛v : ∀ {m n} {σ σ' : Subst m n} {V V'}
                      → σ ⇛s σ'
                      → V ⇛v V'
                      → substV σ V ⇛v substV σ' V'
  substV-preserves-⇛v {σ = σ} {σ' = σ'} ps p-var = ps .pf
  substV-preserves-⇛v {σ = σ} {σ' = σ'} ps (p-hole-v pσ) =
    p-hole-v (record { pf = λ {t} → substV-preserves-⇛v {σ = σ} {σ' = σ'} ps (pσ .pf {t}) })
  substV-preserves-⇛v {σ = σ} {σ' = σ'} ps (p-lam p) =
    p-lam (substC-preserves-⇛ (exts-preserves-⇛s ps) p)
  substV-preserves-⇛v {σ = σ} {σ' = σ'} ps (p-handler p₁ p₂) =
    p-handler (substC-preserves-⇛ (exts-preserves-⇛s ps) p₁)
              (substC-preserves-⇛ (exts²-preserves-⇛s ps) p₂)

  substC-preserves-⇛ : ∀ {m n} {σ σ' : Subst m n} {M M'}
                     → σ ⇛s σ'
                     → M ⇛ M'
                     → substC σ M ⇛ substC σ' M'
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-ret p) = p-ret (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps p)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-hole-c pσ) =
    p-hole-c (record { pf = λ {t} → substV-preserves-⇛v {σ = σ} {σ' = σ'} ps (pσ .pf {t}) })
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-app p₁ p₂) =
    p-app (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps p₁) (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps p₂)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-β {M' = M'} {V' = V'} p x) rewrite
    substC-subst-zero-comm σ' V' M' =
    p-β (substC-preserves-⇛ (exts-preserves-⇛s ps) p) (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps x)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-let-cong p p₁) =
    p-let-cong (substC-preserves-⇛ ps p) (substC-preserves-⇛ (exts-preserves-⇛s ps) p₁)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-β-let {V' = V'} {M₂' = M₂'} x p) rewrite
    substC-subst-zero-comm σ' V' M₂' =
    p-β-let (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps x) (substC-preserves-⇛ (exts-preserves-⇛s ps) p)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-op-let {M₂' = M₂'} x p p₁) rewrite
    substC-exts-rename-comm σ' M₂' =
    p-op-let (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps x)
             (substC-preserves-⇛ (exts-preserves-⇛s ps) p)
             (substC-preserves-⇛ (exts-preserves-⇛s ps) p₁)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-with-cong p p₁) =
    p-with-cong (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps p) (substC-preserves-⇛ ps p₁)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-β-ret {Nᵣ' = Nᵣ'} {V' = V'} p x) rewrite
    substC-subst-zero-comm σ' V' Nᵣ' =
    p-β-ret (substC-preserves-⇛ (exts-preserves-⇛s ps) p) (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps x)
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-β-op-eq {Nᵣ' = Nᵣ'} {Nₒ' = Nₒ'} {op = op} {V' = V'} {K' = K'} p p₁ x p₂) =
    let W = ƛ #with #handler⟨ liftC-ret Nᵣ' ⨟ op , liftC-op Nₒ' ⟩ #handle K'
    in ⇛-resp-≡
         (p-β-op-eq (substC-preserves-⇛ (exts-preserves-⇛s ps) p)
                    (substC-preserves-⇛ (exts²-preserves-⇛s ps) p₁)
                    (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps x)
                    (substC-preserves-⇛ (exts-preserves-⇛s ps) p₂))
         (sym
           (trans
             (substC-subst-⨟-comm σ' V' W Nₒ')
             (cong (λ w → substC (exts (exts σ')) Nₒ' [ substV σ' V' ⨟ w ]c)
               (substV-handler-σ σ' op Nᵣ' Nₒ' K'))))
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-β-op-neq {Nᵣ' = Nᵣ'} {Nₒ' = Nₒ'} {op = op} {op' = op'} {V' = V'} {K' = K'} p p₁ x p₂ x₁) =
    ⇛-resp-≡
      (p-β-op-neq (substC-preserves-⇛ (exts-preserves-⇛s ps) p)
                  (substC-preserves-⇛ (exts²-preserves-⇛s ps) p₁)
                  (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps x)
                  (substC-preserves-⇛ (exts-preserves-⇛s ps) p₂) x₁)
      (cong (λ c → op' ⟨ substV σ' V' ⨟ c ⟩)
        (substC-handler-σ σ' op Nᵣ' Nₒ' K'))
  substC-preserves-⇛ {σ = σ} {σ' = σ'} ps (p-op p p₁) =
    p-op (substV-preserves-⇛v {σ = σ} {σ' = σ'} ps p) (substC-preserves-⇛ (exts-preserves-⇛s ps) p₁)


-- Single-variable substitution lemmas (derived from the general ones)
subst-val-⇛v : ∀ {n} {V V' : Value (suc n)} {W W' : Value n}
             → V ⇛v V'
             → W ⇛v W'
             → V [ W ]v ⇛v V' [ W' ]v
subst-val-⇛v pv pw = substV-preserves-⇛v (record { pf = λ { {F.zero} → pw ; {F.suc x} → p-var } }) pv

subst-comp-⇛ : ∀ {n} {M M' : Computation (suc n)} {V V' : Value n}
             → M ⇛ M'
             → V ⇛v V'
             → M [ V ]c ⇛ M' [ V' ]c
subst-comp-⇛ pm pv = substC-preserves-⇛ (record { pf = λ { {F.zero} → pv ; {F.suc x} → p-var } }) pm

subst-comp-⨟-⇛ : ∀ {n} {M M' : Computation (2+ n)} {V₁ V₁' V₂ V₂' : Value n}
                 → M ⇛ M'
                 → V₁ ⇛v V₁'
                 → V₂ ⇛v V₂'
                 → M [ V₁ ⨟ V₂ ]c ⇛ M' [ V₁' ⨟ V₂' ]c
subst-comp-⨟-⇛ {V₁ = V₁} {V₁' = V₁'} {V₂ = V₂} {V₂' = V₂'} pm pv₁ pv₂ =
  substC-preserves-⇛ (record { pf = λ { {F.zero} → pv₂
                                        ; {F.suc F.zero} →
                                            substV-preserves-⇛v
                                                (record { pf = λ { {F.zero} → pv₂ ; {F.suc x} → p-var } })
                                                (liftV-preserves-⇛v pv₁)
                                        ; {F.suc (F.suc x)} → p-var } })
                     pm


-- Complete development (Takahashi's "M*")
mutual
  ⇛v-complete : ∀ {n} → Value n → Value n
  ⇛v-complete (‵ x) = ‵ x
  ⇛v-complete (⁇ u σ) = ⁇ u (λ t → ⇛v-complete (σ t))
  ⇛v-complete (ƛ_ M) = ƛ_ (⇛-complete M)
  ⇛v-complete #handler⟨ Nᵣ ⨟ op , Nₒ ⟩ = #handler⟨ ⇛-complete Nᵣ ⨟ op , ⇛-complete Nₒ ⟩

  ⇛-complete : ∀ {n} → Computation n → Computation n
  ⇛-complete ((ƛ_ M) ∙ V) = ⇛-complete M [ ⇛v-complete V ]c
  ⇛-complete (#let (#ret V) #in M₂) = ⇛-complete M₂ [ ⇛v-complete V ]c
  ⇛-complete (#let (op ⟨ V ⨟ K ⟩) #in M₂) =
    op ⟨ ⇛v-complete V ⨟ #let ⇛-complete K #in renameC (ext F.suc) (⇛-complete M₂) ⟩
  ⇛-complete (#with #handler⟨ Nᵣ ⨟ op , Nₒ ⟩ #handle (#ret V)) =
    ⇛-complete Nᵣ [ ⇛v-complete V ]c
  ⇛-complete (#with #handler⟨ Nᵣ ⨟ op , Nₒ ⟩ #handle (op' ⟨ V ⨟ K ⟩)) with op ≟ op'
  ... | yes _ =
    ⇛-complete Nₒ [ ⇛v-complete V
                  ⨟ ƛ #with #handler⟨ liftC-ret (⇛-complete Nᵣ) ⨟ op , liftC-op (⇛-complete Nₒ) ⟩
                      #handle ⇛-complete K ]c
  ... | no _ =
    op' ⟨ ⇛v-complete V
        ⨟ #with #handler⟨ liftC-ret (⇛-complete Nᵣ) ⨟ op , liftC-op (⇛-complete Nₒ) ⟩
            #handle ⇛-complete K ⟩
  ⇛-complete (#ret V) = #ret (⇛v-complete V)
  ⇛-complete (⦃⁇⦄ u σ) = ⦃⁇⦄ u (λ t → ⇛v-complete (σ t))
  ⇛-complete (V₁ ∙ V₂) = ⇛v-complete V₁ ∙ ⇛v-complete V₂
  ⇛-complete (#let M₁ #in M₂) = #let ⇛-complete M₁ #in ⇛-complete M₂
  ⇛-complete (#with H #handle M) = #with ⇛v-complete H #handle ⇛-complete M
  ⇛-complete (op ⟨ V ⨟ K ⟩) = op ⟨ ⇛v-complete V ⨟ ⇛-complete K ⟩


-- Triangle property

mutual
  triangle-⇛v : ∀ {n} {V V' : Value n}
              → V ⇛v V'
              → V' ⇛v ⇛v-complete V
  triangle-⇛v p-var = p-var
  triangle-⇛v (p-hole-v pσ) = p-hole-v (record { pf = λ {t} → triangle-⇛v (pσ .pf {t}) })
  triangle-⇛v (p-lam p) = p-lam (triangle-⇛ p)
  triangle-⇛v (p-handler p₁ p₂) = p-handler (triangle-⇛ p₁) (triangle-⇛ p₂)

  triangle-app : ∀ {n} {V₁ V₁' V₂ V₂' : Value n}
               → V₁ ⇛v V₁'
               → V₂ ⇛v V₂'
               → V₁' ∙ V₂' ⇛ ⇛-complete (V₁ ∙ V₂)
  triangle-app {V₁ = ƛ _} {V₁' = ƛ _} (p-lam p) q = p-β (triangle-⇛ p) (triangle-⇛v q)
  triangle-app {V₁ = ⁇ _ _} p q = p-app (triangle-⇛v p) (triangle-⇛v q)
  triangle-app {V₁ = ‵ _} p q = p-app (triangle-⇛v p) (triangle-⇛v q)
  triangle-app {V₁ = #handler⟨ _ ⨟ _ , _ ⟩} p q = p-app (triangle-⇛v p) (triangle-⇛v q)

  triangle-let : ∀ {n} {M₁ M₁' : Computation n} {M₂ M₂' : Computation (suc n)}
               → M₁ ⇛ M₁'
               → M₂ ⇛ M₂'
               → #let M₁' #in M₂' ⇛ ⇛-complete (#let M₁ #in M₂)
  triangle-let {M₁ = #ret _} {M₁' = #ret _} (p-ret p) q = p-β-let (triangle-⇛v p) (triangle-⇛ q)
  triangle-let {M₁ = _ ⟨ _ ⨟ _ ⟩} {M₁' = _ ⟨ _ ⨟ _ ⟩} (p-op p r) q = p-op-let (triangle-⇛v p) (triangle-⇛ r) (triangle-⇛ q)
  triangle-let {M₁ = ⦃⁇⦄ _ _} p q = p-let-cong (triangle-⇛ p) (triangle-⇛ q)
  triangle-let {M₁ = #with _ #handle _} p q = p-let-cong (triangle-⇛ p) (triangle-⇛ q)
  triangle-let {M₁ = _ ∙ _} p q = p-let-cong (triangle-⇛ p) (triangle-⇛ q)
  triangle-let {M₁ = #let _ #in _} p q = p-let-cong (triangle-⇛ p) (triangle-⇛ q)

  triangle-with : ∀ {n} {H H' : Value n} {M M' : Computation n}
                → H ⇛v H'
                → M ⇛ M'
                → #with H' #handle M' ⇛ ⇛-complete (#with H #handle M)
  triangle-with {H = #handler⟨ _ ⨟ _ , _ ⟩} {H' = #handler⟨ _ ⨟ _ , _ ⟩} {M = #ret _} {M' = #ret _} (p-handler pᵣ pₒ) (p-ret p) =
    p-β-ret (triangle-⇛ pᵣ) (triangle-⇛v p)
  triangle-with {H = #handler⟨ _ ⨟ op , _ ⟩} {H' = #handler⟨ _ ⨟ _ , _ ⟩} {M = op' ⟨ _ ⨟ _ ⟩} {M' = _ ⟨ _ ⨟ _ ⟩} 
                (p-handler pᵣ pₒ) (p-op pV pK) with op ≟ op'
  ... | yes refl = p-β-op-eq (triangle-⇛ pᵣ) (triangle-⇛ pₒ) (triangle-⇛v pV) (triangle-⇛ pK)
  ... | no neq  = p-β-op-neq (triangle-⇛ pᵣ) (triangle-⇛ pₒ) (triangle-⇛v pV) (triangle-⇛ pK) neq
  triangle-with {H = #handler⟨ _ ⨟ _ , _ ⟩} {M = ⦃⁇⦄ _ _} p q = p-with-cong (triangle-⇛v p) (triangle-⇛ q)
  triangle-with {H = #handler⟨ _ ⨟ _ , _ ⟩} {M = #with _ #handle _} p q = p-with-cong (triangle-⇛v p) (triangle-⇛ q)
  triangle-with {H = #handler⟨ _ ⨟ _ , _ ⟩} {M = _ ∙ _} p q = p-with-cong (triangle-⇛v p) (triangle-⇛ q)
  triangle-with {H = #handler⟨ _ ⨟ _ , _ ⟩} {M = #let _ #in _} p q = p-with-cong (triangle-⇛v p) (triangle-⇛ q)
  triangle-with {H = ⁇ _ _} p q = p-with-cong (triangle-⇛v p) (triangle-⇛ q)
  triangle-with {H = ‵ _} p q = p-with-cong (triangle-⇛v p) (triangle-⇛ q)
  triangle-with {H = ƛ _} p q = p-with-cong (triangle-⇛v p) (triangle-⇛ q)

  triangle-⇛ : ∀ {n} {M M' : Computation n}
             → M ⇛ M'
             → M' ⇛ ⇛-complete M
  triangle-⇛ (p-ret p) = p-ret (triangle-⇛v p)
  triangle-⇛ (p-hole-c pσ) = p-hole-c (record { pf = λ {t} → triangle-⇛v (pσ .pf {t}) })
  triangle-⇛ (p-app p₁ p₂) = triangle-app p₁ p₂
  triangle-⇛ (p-β p x) = subst-comp-⇛ (triangle-⇛ p) (triangle-⇛v x)
  triangle-⇛ (p-let-cong p₁ p₂) = triangle-let p₁ p₂
  triangle-⇛ (p-β-let x p) = subst-comp-⇛ (triangle-⇛ p) (triangle-⇛v x)
  triangle-⇛ (p-op-let x p p₁) =
    p-op (triangle-⇛v x)
         (p-let-cong (triangle-⇛ p)
                     (renameC-preserves-⇛ (triangle-⇛ p₁)))
  triangle-⇛ (p-with-cong p p₁) = triangle-with p p₁
  triangle-⇛ (p-β-ret p x) = subst-comp-⇛ (triangle-⇛ p) (triangle-⇛v x)
  triangle-⇛ (p-β-op-eq {op = op} p p₁ x p₂) with op ≟ op
  ... | yes refl =
    subst-comp-⨟-⇛ (triangle-⇛ p₁)
                   (triangle-⇛v x)
                   (p-lam (p-with-cong
                            (p-handler (liftC-ret-preserves-⇛ (triangle-⇛ p))
                                       (liftC-op-preserves-⇛ (triangle-⇛ p₁)))
                            (triangle-⇛ p₂)))
  ... | no neq = ⊥-elim (neq refl)

  triangle-⇛ (p-β-op-neq {op = op} {op' = op'} p p₁ x p₂ x₁) with op ≟ op'
  ... | yes refl = ⊥-elim (x₁ refl)
  ... | no _ =
    p-op (triangle-⇛v x)
         (p-with-cong
           (p-handler (liftC-ret-preserves-⇛ (triangle-⇛ p))
                      (liftC-op-preserves-⇛ (triangle-⇛ p₁)))
           (triangle-⇛ p₂))
  triangle-⇛ (p-op p p₁) = p-op (triangle-⇛v p) (triangle-⇛ p₁)


-- Diamond property for parallel reduction
-- Direct corollary of the triangle property: join both reductions at the
-- complete development of the source term.
diamond-⇛ : ∀ {n} {M M₁ M₂ : Computation n}
          → M ⇛ M₁              → M ⇛ M₂
          ---------------------------------
          → ∃[ M' ] ((M₁ ⇛ M') × (M₂ ⇛ M'))
diamond-⇛ {M = M} p q = ⇛-complete M , triangle-⇛ p , triangle-⇛ q


-- Confluence of parallel reduction and the small-step relation
-- Strip lemma: a single ⇛ step can be pushed past a ⇛* closure
strip-⇛ : ∀ {n} {M N P : Computation n}
        → M ⇛ N            → M ⇛* P
        ----------------------------
        → ∃[ Q ] ((N ⇛* Q) × (P ⇛ Q))
strip-⇛ r (zero , ⇛Z) = _ , ⇛-to⇛* ⇛-refl , r
strip-⇛ {M = M} r (suc k , (r' ⇛S rest)) =
  let (Q' , s , s') = diamond-⇛ r r'
      (Q , t , t') = strip-⇛ s' (k , rest)
  in Q , trans⇛* (⇛-to⇛* s) t , t'

-- Confluence of the reflexive-transitive closure of ⇛
confluence⇛* : ∀ {n} {M P Q : Computation n}
              → M ⇛* P          → M ⇛* Q
              ----------------------------
              → ∃[ R ] ((P ⇛* R) × (Q ⇛* R))
confluence⇛* (zero , ⇛Z) q = _ , q , ⇛-to⇛* ⇛-refl
confluence⇛* {M = M} (suc k , (r ⇛S rest)) q =
  let (P' , s , s') = strip-⇛ r q
      (R , t , t') = confluence⇛* (k , rest) s
  in R , t , trans⇛* (⇛-to⇛* s') t'

-- Confluence of the small-step relation
confluence : ∀ {n} {M M₁ M₂ : Computation n}
           → M -→* M₁      → M -→* M₂
           ----------------------------
           → ∃[ M' ] ((M₁ -→* M') × (M₂ -→* M'))
confluence {M = M} r₁ r₂ =
  let (M' , s₁ , s₂) = confluence⇛* (-→*-to⇛* r₁) (-→*-to⇛* r₂)
  in M' , ⇛*-to-→* s₁ , ⇛*-to-→* s₂
