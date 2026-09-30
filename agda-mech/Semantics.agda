{-# OPTIONS --safe #-}

open import Axiom.Extensionality.Propositional as Ext
open import Agda.Primitive using (lzero)
module Semantics (extensionality : Ext.Extensionality lzero lzero) where

open import Syntax
open import Subst extensionality
open import Data.Nat
open import Data.Fin as F using (Fin; cast; _↑ʳ_; toℕ; fromℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_; refl; _≢_; cong; cong₂; sym; trans; subst)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax; _,_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Empty using (⊥-elim)

private
  variable
    n : ℕ
    m : ℕ
    n' : ℕ

infix 2 _-→v_
infix 2 _-→s_
infix 2 _-→_

data _-→v_ : ∀ {n} → Value n → Value n → Set
data _-→s_ : ∀ {m n} → Subst m n → Subst m n → Set
data _-→_  : ∀ {n} → Computation n → Computation n → Set

data _-→v_ where
  ξ-ƛ : ∀ {n} {c c' : Computation (suc n)}
      → c -→ c'
      ---------------------------
      → ƛ c -→v ƛ c'

  ξ-hand₁ : ∀ {n} {cᵣ cᵣ' : Computation (suc n)} {cₒₚ : Computation (2+ n)} {op}
           → cᵣ -→ cᵣ'
           --------------------------------------------------
           → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ -→v #handler⟨ cᵣ' ⨟ op , cₒₚ ⟩

  ξ-hand₂ : ∀ {n} {cᵣ : Computation (suc n)} {cₒₚ cₒₚ' : Computation (2+ n)} {op}
           → cₒₚ -→ cₒₚ'
           --------------------------------------------------
           → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ -→v #handler⟨ cᵣ ⨟ op , cₒₚ' ⟩

  ξ-hole-v : ∀ {m n} {i} {σ σ' : Subst m n}
         → σ -→s σ'
         -------------------------
         → ⁇ i σ -→v ⁇ i σ'

data _-→s_ where
  ξ-σ : ∀ {m n} {σ σ' : Subst m n} (x : Fin m)
        → σ x -→v σ' x
        → (∀ (y : Fin m) → y ≢ x → σ y ≡ σ' y)
        -------------------------
        → σ -→s σ'

data _-→_ where

  -- ===== base redexes =====

  β : ∀ {N : Computation (suc n)} {V : Value n}
      -----------------------
      → (ƛ N) ∙ V -→ N [ V ]c

  β-let : ∀ {V : Value n} {N : Computation (suc n)}
          ---------------------------------
          → #let (#ret V) #in N -→ N [ V ]c

  op-let : ∀ {v : Value n} {k : Computation (suc n)} {c : Computation (suc n)} {op}
          ----------------------------------------------------------
          → #let op ⟨ v ⨟ k ⟩ #in c -→ op ⟨ v ⨟ #let k #in renameC (ext F.suc) c ⟩

  β-ret : ∀ {cᵣ : Computation (suc n)} {cₒₚ : Computation (2+ n)} {op} {v : Value n}
          ----------------------------------------------------------------
          → #with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle #ret v -→ cᵣ [ v ]c

  β-op-eq :  ∀ {cᵣ : Computation (suc n)} {cₒₚ : Computation (2+ n)} {op}
               {v : Value n} {k : Computation (suc n)}
            ----------------------------------------------------------------------
             →  #with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op ⟨ v ⨟ k ⟩
             -→ cₒₚ [ v ⨟ ƛ #with #handler⟨ liftC-ret cᵣ ⨟ op , liftC-op cₒₚ ⟩ #handle k ]c

  β-op-neq :  ∀ {cᵣ : Computation (suc n)} {cₒₚ : Computation (2+ n)} {op op'}
                {v : Value n} {k : Computation (suc n)}
              → op ≢ op'
             ----------------------------------------------------------------------
              →  #with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op' ⟨ v ⨟ k ⟩
              -→ op' ⟨ v ⨟ #with #handler⟨ liftC-ret cᵣ ⨟ op , liftC-op cₒₚ ⟩ #handle k ⟩

  -- ===== structural / contextual rules =====

  ξ-ret : ∀ {v v' : Value n}
      → v -→v v'
      -------------------------
      → #ret v -→ #ret v'

  ξ-hole-c : ∀ {m n} {i} {σ σ' : Subst m n}
         → σ -→s σ'
         -------------------------
         → ⦃⁇⦄ i σ -→ ⦃⁇⦄ i σ'

  ξ-app₁ : ∀ {v₁ v₁' v₂ : Value n}
       → v₁ -→v v₁'
       -------------------------
       → v₁ ∙ v₂ -→ v₁' ∙ v₂

  ξ-app₂ : ∀ {v₁ v₂ v₂' : Value n}
       → v₂ -→v v₂'
       -------------------------
       → v₁ ∙ v₂ -→ v₁ ∙ v₂'

  ξ-let : ∀ {C C' : Computation n} {D : Computation (suc n)}
      → C -→ C'
      -------------------------------
      → #let C #in D -→ #let C' #in D

  ξ-in : ∀ {C : Computation n} {D D' : Computation (suc n)}
      → D -→ D'
      -------------------------------
      → #let C #in D -→ #let C #in D'

  ξ-with₁ : ∀ {h h' : Value n} {c : Computation n}
        → h -→v h'
        -----------------------------------------
        → #with h #handle c -→ #with h' #handle c

  ξ-with₂ : ∀ {c c' : Computation n} {h : Value n}
         → c -→ c'
         -----------------------------------------
         → #with h #handle c -→ #with h #handle c'

  ξ-op₁ : ∀ {v v' : Value n} {k : Computation (suc n)} {op}
      → v -→v v'
      -------------------------------
      → op ⟨ v ⨟ k ⟩ -→ op ⟨ v' ⨟ k ⟩

  ξ-op₂ : ∀ {v : Value n} {k k' : Computation (suc n)} {op}
      → k -→ k'
      -------------------------------
      → op ⟨ v ⨟ k ⟩ -→ op ⟨ v ⨟ k' ⟩

infixr  2 _-→S_
data _>-_-→_ : Computation n → ℕ → Computation n → Set where
  -→Z : ∀ {M : Computation n}
    → M >- 0 -→  M
  
  _-→S_ : ∀ {L M N : Computation m} {n : ℕ}
    → L -→ M 
    → M >- n -→ N 
    → L >- suc n -→ N

_-→*_ : Computation n → Computation n → Set 
M' -→* N' = ∃[ n ] (M' >- n -→ N')
  
form-→* : ∀ {M N : Computation m} {n : ℕ}  
  → M >- n -→ N 
  → M -→* N
form-→* -→Z = 0 , -→Z
form-→* s@(_-→S_ {n = n} _ _) = suc n , s 

-→*-refl : ∀ {M : Computation n}
  ---------
  → M -→* M
-→*-refl = 0 , -→Z

trans-→* : ∀ {L M N : Computation n}
  → L -→* M
  → M -→* N 
  ----------
  → L -→* N 
trans-→* (zero , -→Z) x₁ = x₁
trans-→* (suc n , (x -→S snd)) x₁ with trans-→* (n , snd) x₁
... | fst , snd₁ = suc fst , (x -→S snd₁)

-→trans-→* : ∀ {L M N : Computation n}
  → L -→ M
  → M -→* N
  ----------
  → L -→* N
-→trans-→* x (zero , snd) = 1 , (x -→S snd)
-→trans-→* x (suc fst , snd) = 2+ fst , (x -→S snd)

-- value-level and substitution-level multi-step closures

infixr 2 _-→vS_
infix 2 _-→v*_
infix 2 _-→s*_

data _>v-_-→v_ : Value n → ℕ → Value n → Set where
  -→vZ : ∀ {V : Value n}
    → V >v- 0 -→v V

  _-→vS_ : ∀ {V W V' : Value m} {k : ℕ}
    → V -→v W
    → W >v- k -→v V'
    → V >v- suc k -→v V'

_-→v*_ : Value n → Value n → Set
V -→v* V' = ∃[ k ] (V >v- k -→v V')

-- substitution multi-step: pointwise value multi-step
_-→s*_ : ∀ {m n} (σ σ' : Subst m n) → Set
_-→s*_ {m} σ σ' = ∀ (x : Fin m) → σ x -→v* σ' x

form-→v* : ∀ {V W : Value m} {k : ℕ}
  → V >v- k -→v W
  → V -→v* W
form-→v* -→vZ = 0 , -→vZ
form-→v* s@(_-→vS_ {k = k} _ _) = suc k , s

-→v*-refl : ∀ {V : Value n}
  ---------
  → V -→v* V
-→v*-refl = 0 , -→vZ

-→s*-refl : ∀ {σ : Subst m n}
  ---------
  → σ -→s* σ
-→s*-refl _ = -→v*-refl

trans-→v* : ∀ {V W V' : Value n}
  → V -→v* W
  → W -→v* V'
  ----------
  → V -→v* V'
trans-→v* (zero , -→vZ) x₁ = x₁
trans-→v* (suc n , (x -→vS snd)) x₁ with trans-→v* (n , snd) x₁
... | fst , snd₁ = suc fst , (x -→vS snd₁)

-→s*-trans : ∀ {σ θ σ' : Subst m n}
  → σ -→s* θ
  → θ -→s* σ'
  ----------
  → σ -→s* σ'
-→s*-trans s t x = trans-→v* (s x) (t x)

-→vtrans-→v* : ∀ {V W V' : Value n}
  → V -→v W
  → W -→v* V'
  ----------
  → V -→v* V'
-→vtrans-→v* x (zero , snd) = 1 , (x -→vS snd)
-→vtrans-→v* x (suc fst , snd) = 2+ fst , (x -→vS snd)

-→s*-point : ∀ {m n} {σ σ' : Subst m n} {x : Fin m}
  → σ x -→v* σ' x
  → (∀ (y : Fin m) → y ≢ x → σ y ≡ σ' y)
  → σ -→s* σ'
-→s*-point {m} {n} {σ} {σ'} {x = x} s rest y = helper (y F≟ x)
  where
    helper : Dec (y ≡ x) → σ y -→v* σ' y
    helper (yes refl) = s
    helper (no neq) rewrite rest y neq = -→v*-refl

-→strans-→s* : ∀ {m n} {σ θ σ' : Subst m n}
  → σ -→s θ
  → θ -→s* σ'
  ----------
  → σ -→s* σ'
-→strans-→s* {m} {n} {σ} {θ} {σ'} (ξ-σ x s rest) h y = helper (y F≟ x)
  where
    helper : Dec (y ≡ x) → σ y -→v* σ' y
    helper (yes refl) = -→vtrans-→v* s (h y)
    helper (no neq) rewrite rest y neq = h y

count : ∀ {m n : ℕ} → (p : m < n) → Fin n
count {zero}  {suc n} (s≤s z≤n) = F.zero
count {suc m} {suc n} (s≤s p)    = F.suc (count {m = m} {n = n} p)


# : ∀ (m : ℕ) → {n∈Γ : True (suc m ≤? n)} → Value n
# n {n∈Γ}  =  ‵ (count (toWitness n∈Γ))


-- utlc examples
twoᶜ : Value n
twoᶜ = ƛ #ret (ƛ (#let # 1 ∙ # 0 #in # 2 ∙ # 0))

fourᶜ : Value n
fourᶜ = ƛ #ret (ƛ (
  #let (#let # 1 ∙ # 0 #in # 2 ∙ # 0)
  #in (ƛ #let # 3 ∙ # 0 #in # 4 ∙ # 0) ∙ # 0))

plusᶜ : Value n
plusᶜ = ƛ #ret (ƛ #ret (ƛ #ret (ƛ
  #let # 3 ∙ # 1 #in
  #let # 3 ∙ # 2 #in
  #let # 0 ∙ # 2 #in
  # 2 ∙ # 0)))

2+2ᶜ : Computation n
2+2ᶜ = #let plusᶜ ∙ twoᶜ #in # 0 ∙ twoᶜ

_ : 2+2ᶜ -→* #ret (fourᶜ {n})
_ = form-→* (ξ-let β -→S β-let -→S β -→S ξ-ret (ξ-ƛ (ξ-ret (ξ-ƛ (ξ-let β)))) 
  -→S ξ-ret (ξ-ƛ (ξ-ret (ξ-ƛ β-let))) -→S ξ-ret (ξ-ƛ (ξ-ret (ξ-ƛ (ξ-let β)))) 
  -→S ξ-ret (ξ-ƛ (ξ-ret (ξ-ƛ β-let))) -→S ξ-ret (ξ-ƛ (ξ-ret (ξ-ƛ (ξ-let β)))) -→S -→Z)

mutual
  rename-preserves-→v : ∀ {v v' : Value n} {ρ : Renaming n m} → v -→v v' → renameV ρ v -→v renameV ρ v'
  rename-preserves-→v (ξ-ƛ x) = ξ-ƛ (rename-preserves-→ x)
  rename-preserves-→v (ξ-hand₁ x) = ξ-hand₁ (rename-preserves-→ x)
  rename-preserves-→v (ξ-hand₂ x) = ξ-hand₂ (rename-preserves-→ x)
  rename-preserves-→v (ξ-hole-v x) = ξ-hole-v (rename-preserves-→s x)

  rename-preserves-→s : ∀ {k} {σ σ' : Subst m n} {ρ : Renaming n k}
    → σ -→s σ' → (λ x → renameV ρ (σ x)) -→s (λ x → renameV ρ (σ' x))
  rename-preserves-→s {σ = σ} {σ'} {ρ} (ξ-σ x s rest) =
    ξ-σ x (rename-preserves-→v s) (λ y neq → cong (renameV ρ) (rest y neq))

  rename-preserves-→ : ∀ {c c' : Computation n} {ρ : Renaming n m}
                       → c -→ c' → renameC ρ c -→ renameC ρ c'
  rename-preserves-→ {n} {m} {(ƛ N) ∙ V} {c'} {ρ} β rewrite renameC-ext-subst {k = 0} {ρ = ρ} {V = V} {c = N} = β
  rename-preserves-→ {n} {m} {#let #ret V #in N} {c'} {ρ} β-let rewrite renameC-ext-subst {k = 0} {ρ = ρ} {V = V} {c = N} = β-let
  rename-preserves-→ {n} {m} {#let op ⟨ v ⨟ k ⟩ #in c₁} {c'} {ρ} op-let rewrite renameC-ext-comm-suc ρ c₁ = op-let
  rename-preserves-→ {n} {m} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle #ret v} {c'} {ρ} β-ret rewrite renameC-ext-subst {k = 0} {ρ = ρ} {V = v} {c = cᵣ} = β-ret
  rename-preserves-→ {n} {m} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op ⟨ v ⨟ k ⟩} {c'} {ρ} β-op-eq
    rewrite renameC-ext-subst-⨟ {ρ = ρ} {M1 = v} {M2 = ƛ #with #handler⟨ liftC-ret cᵣ ⨟ op , liftC-op cₒₚ ⟩ #handle k} {N = cₒₚ}
    | renameC-liftC-ret-comm ρ cᵣ
    | renameC-liftC-op-comm ρ cₒₚ
    = β-op-eq
  rename-preserves-→ {n} {m} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op' ⟨ v ⨟ k ⟩} {c'} {ρ} (β-op-neq x)
    rewrite renameC-liftC-ret-comm ρ cᵣ
    | renameC-liftC-op-comm ρ cₒₚ
    = β-op-neq x
  rename-preserves-→ (ξ-ret x) = ξ-ret (rename-preserves-→v x)
  rename-preserves-→ (ξ-hole-c x) = ξ-hole-c (rename-preserves-→s x)
  rename-preserves-→ (ξ-app₁ x) = ξ-app₁ (rename-preserves-→v x)
  rename-preserves-→ (ξ-app₂ x) = ξ-app₂ (rename-preserves-→v x)
  rename-preserves-→ (ξ-let x) = ξ-let (rename-preserves-→ x)
  rename-preserves-→ (ξ-in x) = ξ-in (rename-preserves-→ x)
  rename-preserves-→ (ξ-with₁ x) = ξ-with₁ (rename-preserves-→v x)
  rename-preserves-→ (ξ-with₂ x) = ξ-with₂ (rename-preserves-→ x)
  rename-preserves-→ (ξ-op₁ x) = ξ-op₁ (rename-preserves-→v x)
  rename-preserves-→ (ξ-op₂ x) = ξ-op₂ (rename-preserves-→ x)

-- multi-step versions of renaming preservation
rename-preserves-→v* : ∀ {v v' : Value n} {ρ : Renaming n m}
  → v -→v* v'
  → renameV ρ v -→v* renameV ρ v'
rename-preserves-→v* (zero , -→vZ) = -→v*-refl
rename-preserves-→v* (suc k , (s -→vS rest)) =
  -→vtrans-→v* (rename-preserves-→v s) (rename-preserves-→v* (k , rest))

rename-preserves-→* : ∀ {c c' : Computation n} {ρ : Renaming n m}
  → c -→* c'
  → renameC ρ c -→* renameC ρ c'
rename-preserves-→* (zero , -→Z) = -→*-refl
rename-preserves-→* (suc k , (s -→S rest)) =
  -→trans-→* (rename-preserves-→ s) (rename-preserves-→* (k , rest))

liftV-preserves-→v* : ∀ {v v' : Value n}
  → v -→v* v'
  → liftV v -→v* liftV v'
liftV-preserves-→v* = rename-preserves-→v*

-- multi-step contextual closures

map-c→v* : ∀ {m} (f : Computation m → Value n)
          → (∀ {x y} → x -→ y → f x -→v f y)
          → ∀ {x y} → (∃[ k ] x >- k -→ y) → f x -→v* f y
map-c→v* f cong (zero , -→Z) = -→v*-refl
map-c→v* f cong (suc k , (s -→S rest)) =
  -→vtrans-→v* (cong s) (map-c→v* f cong (k , rest))

map-v→c* : ∀ {m} (f : Value m → Computation n)
          → (∀ {x y} → x -→v y → f x -→ f y)
          → ∀ {x y} → (∃[ k ] x >v- k -→v y) → f x -→* f y
map-v→c* f cong (zero , -→vZ) = -→*-refl
map-v→c* f cong (suc k , (s -→vS rest)) =
  -→trans-→* (cong s) (map-v→c* f cong (k , rest))

map-c→c* : ∀ {m} (f : Computation m → Computation n)
          → (∀ {x y} → x -→ y → f x -→ f y)
          → ∀ {x y} → (∃[ k ] x >- k -→ y) → f x -→* f y
map-c→c* f cong (zero , -→Z) = -→*-refl
map-c→c* f cong (suc k , (s -→S rest)) =
  -→trans-→* (cong s) (map-c→c* f cong (k , rest))

ξ-ƛ* : ∀ {c c' : Computation (suc n)}
  → c -→* c'
  → ƛ c -→v* ƛ c'
ξ-ƛ* = map-c→v* ƛ_ ξ-ƛ

ξ-hand₁* : ∀ {cᵣ cᵣ' : Computation (suc n)} {cₒₚ : Computation (2+ n)} {op}
  → cᵣ -→* cᵣ'
  → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ -→v* #handler⟨ cᵣ' ⨟ op , cₒₚ ⟩
ξ-hand₁* {cₒₚ = cₒₚ} {op} = map-c→v* (λ cᵣ → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩) ξ-hand₁

ξ-hand₂* : ∀ {cᵣ : Computation (suc n)} {cₒₚ cₒₚ' : Computation (2+ n)} {op}
  → cₒₚ -→* cₒₚ'
  → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ -→v* #handler⟨ cᵣ ⨟ op , cₒₚ' ⟩
ξ-hand₂* {cᵣ = cᵣ} {op = op} = map-c→v* (λ cₒₚ → #handler⟨ cᵣ ⨟ op , cₒₚ ⟩) ξ-hand₂

ξ-ret* : ∀ {v v' : Value n}
  → v -→v* v'
  → #ret v -→* #ret v'
ξ-ret* = map-v→c* (λ v → #ret v) ξ-ret

ξ-app₁* : ∀ {v₁ v₁' v₂ : Value n}
  → v₁ -→v* v₁'
  → v₁ ∙ v₂ -→* v₁' ∙ v₂
ξ-app₁* {v₂ = v₂} = map-v→c* (_∙ v₂) ξ-app₁

ξ-app₂* : ∀ {v₁ v₂ v₂' : Value n}
  → v₂ -→v* v₂'
  → v₁ ∙ v₂ -→* v₁ ∙ v₂'
ξ-app₂* {v₁ = v₁} = map-v→c* (v₁ ∙_) ξ-app₂

ξ-let* : ∀ {C C' : Computation n} {D : Computation (suc n)}
  → C -→* C'
  → (#let C #in D) -→* (#let C' #in D)
ξ-let* {D = D} = map-c→c* (#let_#in D) ξ-let

ξ-in* : ∀ {C : Computation n} {D D' : Computation (suc n)}
  → D -→* D'
  → (#let C #in D) -→* (#let C #in D')
ξ-in* {C = C} = map-c→c* (#let C #in_) ξ-in

ξ-with₁* : ∀ {h h' : Value n} {c : Computation n}
  → h -→v* h'
  → (#with h #handle c) -→* (#with h' #handle c)
ξ-with₁* {c = c} = map-v→c* (#with_#handle c) ξ-with₁

ξ-with₂* : ∀ {c c' : Computation n} {h : Value n}
  → c -→* c'
  → (#with h #handle c) -→* (#with h #handle c')
ξ-with₂* {h = h} = map-c→c* (#with h #handle_) ξ-with₂

ξ-op₁* : ∀ {v v' : Value n} {k : Computation (suc n)} {op}
  → v -→v* v'
  → op ⟨ v ⨟ k ⟩ -→* op ⟨ v' ⨟ k ⟩
ξ-op₁* {k = k} {op} = map-v→c* (λ v → op ⟨ v ⨟ k ⟩) ξ-op₁

ξ-op₂* : ∀ {v : Value n} {k k' : Computation (suc n)} {op}
  → k -→* k'
  → op ⟨ v ⨟ k ⟩ -→* op ⟨ v ⨟ k' ⟩
ξ-op₂* {v = v} {op = op} = map-c→c* (λ k → op ⟨ v ⨟ k ⟩) ξ-op₂

-- helpers for lifting substitution multi-steps through holes

subst-cons : ∀ {m n} → Value n → Subst m n → Subst (suc m) n
subst-cons v θ F.zero = v
subst-cons v θ (F.suc x) = θ x

subst-cons-step : ∀ {m n} {v : Value n} {θ τ : Subst m n}
  → θ -→s τ
  → subst-cons v θ -→s subst-cons v τ
subst-cons-step {v = v} {θ} {τ} (ξ-σ x s rest) =
  ξ-σ (F.suc x) s (λ y neq → helper y neq)
  where
    helper : ∀ y → y ≢ F.suc x → subst-cons v θ y ≡ subst-cons v τ y
    helper F.zero neq = refl
    helper (F.suc y) neq = rest y (λ eq → neq (cong F.suc eq))

pointwise-≡ : ∀ {m n} {σ σ' : Subst m n} {x : Fin m}
  → σ x ≡ σ' x
  → (∀ y → y ≢ x → σ y ≡ σ' y)
  → ∀ y → σ y ≡ σ' y
pointwise-≡ {x = x} eq rest y with y F≟ x
... | yes refl = eq
... | no neq = rest y neq

pointwise-≡→≡ : ∀ {m n} {σ σ' : Subst m n} {x : Fin m}
  → σ x ≡ σ' x
  → (∀ y → y ≢ x → σ y ≡ σ' y)
  → σ ≡ σ'
pointwise-≡→≡ eq rest = extensionality (pointwise-≡ eq rest)

chain-zero-id : ∀ {V W : Value n} {k}
  → V >v- k -→v W
  → k ≡ zero
  → V ≡ W
chain-zero-id -→vZ refl = refl
chain-zero-id (_ -→vS _) ()

subst-cons-rest-zero : ∀ {m n} {σ : Subst (suc m) n} {v' : Value n}
  → ∀ y → y ≢ F.zero → σ y ≡ subst-cons v' (λ x → σ (F.suc x)) y
subst-cons-rest-zero F.zero neq = ⊥-elim (neq refl)
subst-cons-rest-zero (F.suc y) neq = refl

subst-cons-rest-zero-cong : ∀ {m n} {σ σ' : Subst (suc m) n} {v' : Value n}
  → (∀ y → y ≢ F.zero → σ y ≡ σ' y)
  → ∀ y → y ≢ F.zero → subst-cons v' (λ x → σ (F.suc x)) y ≡ σ' y
subst-cons-rest-zero-cong rest F.zero neq = ⊥-elim (neq refl)
subst-cons-rest-zero-cong rest (F.suc y) neq = rest (F.suc y) (λ ())

hole-v-zero-step : ∀ {m n} {i} {σ σ' : Subst (suc m) n}
  → σ F.zero -→v* σ' F.zero
  → (∀ y → y ≢ F.zero → σ y ≡ σ' y)
  → ⁇ i σ -→v* ⁇ i σ'
hole-v-zero-step {i = i} {σ = σ} {σ' = σ'} (k , chain) rest
  with k | chain
... | zero | q =
  subst (λ τ → ⁇ i σ -→v* ⁇ i τ) (pointwise-≡→≡ (chain-zero-id q refl) rest) -→v*-refl
... | suc k' | (_-→vS_ {W = V} s chain') =
  let τ = subst-cons V (λ x → σ (F.suc x))
  in -→vtrans-→v*
       (ξ-hole-v (ξ-σ {σ = σ} {σ' = τ} F.zero s subst-cons-rest-zero))
       (hole-v-zero-step {i = i} {σ = τ} {σ' = σ'}
         (k' , chain')
         (subst-cons-rest-zero-cong rest))

hole-c-zero-step : ∀ {m n} {i} {σ σ' : Subst (suc m) n}
  → σ F.zero -→v* σ' F.zero
  → (∀ y → y ≢ F.zero → σ y ≡ σ' y)
  → ⦃⁇⦄ i σ -→* ⦃⁇⦄ i σ'
hole-c-zero-step {i = i} {σ = σ} {σ' = σ'} (k , chain) rest
  with k | chain
... | zero | q =
  subst (λ τ → ⦃⁇⦄ i σ -→* ⦃⁇⦄ i τ) (pointwise-≡→≡ (chain-zero-id q refl) rest) -→*-refl
... | suc k' | (_-→vS_ {W = V} s chain') =
  let τ = subst-cons V (λ x → σ (F.suc x))
  in -→trans-→*
       (ξ-hole-c (ξ-σ {σ = σ} {σ' = τ} F.zero s subst-cons-rest-zero))
       (hole-c-zero-step {i = i} {σ = τ} {σ' = σ'}
         (k' , chain')
         (subst-cons-rest-zero-cong rest))

subst-cons-hole-v : ∀ {m n} {i} {v : Value n} {θ θ' : Subst m n}
  → ⁇ i θ -→v* ⁇ i θ'
  → ⁇ i (subst-cons v θ) -→v* ⁇ i (subst-cons v θ')
subst-cons-hole-v (zero , -→vZ) = -→v*-refl
subst-cons-hole-v {v = v} (suc k , (ξ-hole-v t -→vS rest)) =
  -→vtrans-→v*
    (ξ-hole-v (subst-cons-step {v = v} t))
    (subst-cons-hole-v {v = v} (k , rest))

hole-v-multistep : ∀ {m n} {i} {σ σ' : Subst m n}
  → σ -→s* σ'
  → ⁇ i σ -→v* ⁇ i σ'
hole-v-multistep {m = zero} {i = i} {σ = σ} {σ' = σ'} s =
  subst (λ τ → ⁇ i σ -→v* ⁇ i τ) (extensionality (λ ())) -→v*-refl
hole-v-multistep {m = suc m} {i = i} {σ = σ} {σ' = σ'} s =
  let v' = σ' F.zero
      θ' = λ x → σ' (F.suc x)
      consθ'≡σ' : subst-cons v' θ' ≡ σ'
      consθ'≡σ' = extensionality (λ { F.zero → refl
                                    ; (F.suc x) → refl })
  in subst (λ τ → ⁇ i σ -→v* ⁇ i τ) consθ'≡σ'
       (trans-→v*
         (hole-v-zero-step (s F.zero) subst-cons-rest-zero)
         (subst-cons-hole-v {v = v'} (hole-v-multistep {m = m} (λ x → s (F.suc x)))))

subst-cons-hole-c : ∀ {m n} {i} {v : Value n} {θ θ' : Subst m n}
  → ⦃⁇⦄ i θ -→* ⦃⁇⦄ i θ'
  → ⦃⁇⦄ i (subst-cons v θ) -→* ⦃⁇⦄ i (subst-cons v θ')
subst-cons-hole-c (zero , -→Z) = -→*-refl
subst-cons-hole-c {v = v} (suc k , (ξ-hole-c t -→S rest)) =
  -→trans-→*
    (ξ-hole-c (subst-cons-step {v = v} t))
    (subst-cons-hole-c {v = v} (k , rest))

hole-c-multistep : ∀ {m n} {i} {σ σ' : Subst m n}
  → σ -→s* σ'
  → ⦃⁇⦄ i σ -→* ⦃⁇⦄ i σ'
hole-c-multistep {m = zero} {i = i} {σ = σ} {σ' = σ'} s =
  subst (λ τ → ⦃⁇⦄ i σ -→* ⦃⁇⦄ i τ) (extensionality (λ ())) -→*-refl
hole-c-multistep {m = suc m} {i = i} {σ = σ} {σ' = σ'} s =
  let v' = σ' F.zero
      θ' = λ x → σ' (F.suc x)
      consθ'≡σ' : subst-cons v' θ' ≡ σ'
      consθ'≡σ' = extensionality (λ { F.zero → refl
                                    ; (F.suc x) → refl })
  in subst (λ τ → ⦃⁇⦄ i σ -→* ⦃⁇⦄ i τ) consθ'≡σ'
       (trans-→*
         (hole-c-zero-step (s F.zero) subst-cons-rest-zero)
         (subst-cons-hole-c {v = v'} (hole-c-multistep {m = m} (λ x → s (F.suc x)))))

-- lifting a pointwise substitution multi-step through exts / exts²

exts-preserves-→s* : ∀ {m n} {σ σ' : Subst m n}
  → σ -→s* σ'
  → exts σ -→s* exts σ'
exts-preserves-→s* s F.zero = -→v*-refl
exts-preserves-→s* s (F.suc x) = liftV-preserves-→v* (s x)

exts²-preserves-→s* : ∀ {m n} {σ σ' : Subst m n}
  → σ -→s* σ'
  → exts (exts σ) -→s* exts (exts σ')
exts²-preserves-→s* s F.zero = -→v*-refl
exts²-preserves-→s* s (F.suc F.zero) = -→v*-refl
exts²-preserves-→s* s (F.suc (F.suc x)) =
  liftV-preserves-→v* (liftV-preserves-→v* (s x))

-- substitution preserves multi-step reduction

mutual
  substV-preserves-→v* : ∀ {m n} {σ σ' : Subst m n} (v : Value m)
    → σ -→s* σ'
    → substV σ v -→v* substV σ' v
  substV-preserves-→v* (‵ x) s = s x
  substV-preserves-→v* (⁇ i σᵢ) s =
    hole-v-multistep (λ t → substV-preserves-→v* (σᵢ t) s)
  substV-preserves-→v* (ƛ c) s =
    ξ-ƛ* (substC-preserves-→* c (exts-preserves-→s* s))
  substV-preserves-→v* #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ s =
    trans-→v*
      (ξ-hand₁* (substC-preserves-→* cᵣ (exts-preserves-→s* s)))
      (ξ-hand₂* (substC-preserves-→* cₒₚ (exts²-preserves-→s* s)))

  substC-preserves-→* : ∀ {m n} {σ σ' : Subst m n} (c : Computation m)
    → σ -→s* σ'
    → substC σ c -→* substC σ' c
  substC-preserves-→* (#ret v) s = ξ-ret* (substV-preserves-→v* v s)
  substC-preserves-→* (⦃⁇⦄ i σᵢ) s =
    hole-c-multistep (λ t → substV-preserves-→v* (σᵢ t) s)
  substC-preserves-→* (v₁ ∙ v₂) s =
    trans-→*
      (ξ-app₁* (substV-preserves-→v* v₁ s))
      (ξ-app₂* (substV-preserves-→v* v₂ s))
  substC-preserves-→* (#let C #in D) s =
    trans-→*
      (ξ-let* (substC-preserves-→* C s))
      (ξ-in* (substC-preserves-→* D (exts-preserves-→s* s)))
  substC-preserves-→* (#with h #handle c) s =
    trans-→*
      (ξ-with₁* (substV-preserves-→v* h s))
      (ξ-with₂* (substC-preserves-→* c s))
  substC-preserves-→* (op ⟨ v ⨟ k ⟩) s =
    trans-→*
      (ξ-op₁* (substV-preserves-→v* v s))
      (ξ-op₂* (substC-preserves-→* k (exts-preserves-→s* s)))

module HandlerExample where
  Ω :  ∀ n → Computation n
  Ω n = (ƛ (# 0 ∙ # 0)) ∙ (ƛ (# 0 ∙ # 0))

  _ : ∀ n → Ω n -→ Ω n
  _ = λ n → β

  s : Subst 0 0
  s ()

  err = 1
  h : Value 0
  h = #handler⟨ #ret (# 0) ⨟ err , #ret (# 0) ⟩   -- err(x, k) -> ret k

  d : Computation 0
  d = err ⟨ ƛ #ret (# 0) ⨟ #ret (# 0) ⟩

  ex : Computation 0
  ex = #with h #handle (#let d #in Ω 1)
 
  _ : ex -→ ex
  _ = ξ-with₂ (ξ-in β)
  _ : ex -→* #ret (ƛ (#with #handler⟨ #ret (# 0) ⨟ err , #ret (# 0) ⟩ #handle (#let #ret (# 0) #in Ω 2)))
  _ = form-→* (ξ-with₂ op-let -→S β-op-eq -→S -→Z)
