{-# OPTIONS --safe #-}

open import Axiom.Extensionality.Propositional as Ext
open import Agda.Primitive using (lzero)
module Filling (extensionality : Ext.Extensionality lzero lzero) where

open import Syntax
open import Subst extensionality
open import Semantics extensionality
open import Scope extensionality
open import Confluence extensionality using (confluence)

open import Data.Nat
open import Data.Fin as F using (Fin; cast; _↑ʳ_; toℕ; fromℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_; refl; _≢_; cong; cong₂; sym; trans)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Function.Base using (_∘_)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax; _,_)

private
  variable
    n : ℕ
    m : ℕ
    n' : ℕ


subst-lookup-typed : ∀ {Δv Δc m n} {σ : Subst m n}
  → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m
  → ∀ (t : Fin m)
  → Δv ⨟ Δc ⨟ n ⊢v σ t
subst-lookup-typed (sub p) t = p {t}

contV-typed : ∀ {Δv Δc n cᵣ op cₒₚ k}
  → Δv ⨟ Δc ⨟ n ⊢v #handler⟨ cᵣ ⨟ op , cₒₚ ⟩
  → Δv ⨟ Δc ⨟ suc n ⊢c k
  → Δv ⨟ Δc ⨟ n ⊢v ƛ #with #handler⟨ liftC-ret cᵣ ⨟ op , liftC-op cₒₚ ⟩ #handle k
contV-typed (hand p1 p2) x₁ = abs (#with (hand (rename-comp-typed (ext F.suc) p1) (rename-comp-typed (ext (ext F.suc)) p2)) x₁)

-- step preserves type (mutual with value/substitution preservation)
-→v-preserve : ∀ {Δv Δc n} {v v' : Value n}
  → v -→v v'
  → Δv ⨟ Δc ⨟ n ⊢v v
  ----------------
  → Δv ⨟ Δc ⨟ n ⊢v v'

-→s-preserve : ∀ {Δv Δc m n} {σ σ' : Subst m n}
  → σ -→s σ'
  → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m
  ----------------
  → Δv ⨟ Δc ⨟ n ⊢ σ' ⦂ m

-→-preserve : ∀ {Δv Δc n} {c c' : Computation n}
  → c -→ c'
  → Δv ⨟ Δc ⨟ n ⊢c c
  ----------------
  → Δv ⨟ Δc ⨟ n ⊢c c'
-→v-preserve (ξ-ƛ s) (abs x) = abs (-→-preserve s x)
-→v-preserve (ξ-hand₁ s) (hand x x₁) = hand (-→-preserve s x) x₁
-→v-preserve (ξ-hand₂ s) (hand x x₁) = hand x (-→-preserve s x₁)
-→v-preserve (ξ-hole-v s) (hole x (sub p)) = hole x (-→s-preserve s (sub p))

σ'-ok : ∀ {Δv Δc m n} {σ σ' : Subst m n} 
  → (x : Fin m)
  → (s : σ x -→v σ' x)
  → (rest : ∀ (y : Fin m) → y ≢ x → σ y ≡ σ' y)
  → (p : ∀ {t : Fin m} → Δv ⨟ Δc ⨟ n ⊢v σ t)
  → ∀ (t : Fin m) → Δv ⨟ Δc ⨟ n ⊢v σ' t
σ'-ok x s rest p t with t F.≟ x
... | yes refl = -→v-preserve s p
... | no k rewrite sym (rest t k) = p

-→s-preserve {Δv} {Δc} {m} {n} (ξ-σ {σ = σ} {σ'} x s rest) (sub p) = sub λ {t} → σ'-ok x s rest p t

-→-preserve {Δv} {Δc} {n} {c} {c'} β (app (abs x) x₁) = subst-comp x x₁
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-let x) (bind x₁ x₂) = bind (-→-preserve x x₁) x₂
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-in x) (bind x₁ x₂) = bind x₁ (-→-preserve x x₂)
-→-preserve {Δv} {Δc} {n} {c} {c'} β-let (bind (ret x) x₂) = subst-comp x₂ x
-→-preserve {Δv} {Δc} {n} {c} {c'} op-let (bind (opcall pv pk) pc) = opcall pv (bind pk (rename-comp-typed (ext F.suc) pc))
-→-preserve {Δv} {Δc} {n} {c} {c'} β-ret (#with (hand x x₂) (ret x₁)) = subst-comp x x₁
-→-preserve {Δv} {Δc} {n} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op ⟨ v ⨟ k ⟩} {c'}
  β-op-eq (#with ph@(hand p1 p2) (opcall pv pk)) 
  = subst-comp-gen p2 (subst-subst-gen (exts-typed (subst-zero-typed pv)) (subst-zero-typed (contV-typed ph pk)))

-→-preserve {Δv} {Δc} {n} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op' ⟨ v ⨟ k ⟩} {c'}
  (β-op-neq op≢op') (#with (hand p1 p2) (opcall pv pk)) =
  opcall pv (#with (hand (rename-comp-typed (ext F.suc) p1) (rename-comp-typed (ext (ext F.suc)) p2)) pk)
-→-preserve {Δv} {Δc} {n} {#with h #handle c} {c'} (ξ-with₁ s) (#with pv pc) = #with (-→v-preserve s pv) pc
-→-preserve {Δv} {Δc} {n} {#with h #handle c} {c'} (ξ-with₂ s) (#with pv pc) = #with pv (-→-preserve s pc)
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-ret s) (ret x) = ret (-→v-preserve s x)
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-hole-c s) (hole-c x (sub p)) = hole-c x (-→s-preserve s (sub p))
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-app₁ s) (app x x₂) = app (-→v-preserve s x) x₂
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-app₂ s) (app x x₂) = app x (-→v-preserve s x₂)
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-op₁ s) (opcall x x₂) = opcall (-→v-preserve s x) x₂
-→-preserve {Δv} {Δc} {n} {c} {c'} (ξ-op₂ s) (opcall x x₂) = opcall x (-→-preserve s x₂)

-→*-preserve : ∀ {Δv Δc n} {c c' : Computation n}
  → Δv ⨟ Δc ⨟ n ⊢c c
  → c -→* c'
  ----------------
  → Δv ⨟ Δc ⨟ n ⊢c c'
-→*-preserve x (fst , -→Z) = x
-→*-preserve x (suc n , (s -→S snd)) = -→*-preserve (-→-preserve s x) (n , snd)

module Pure where

  -- hole filling is defined only for well-typed(scoped) terms 
  -- pure hole filling
  -- 1. the type for each hole u is constant
  -- 2. holes can be filled in different contexts (under a binder) m ≠ n
  -- 3. Δv u ≡ just m unsures in the hole case, m always equals to n (witnessed by the typing rules) 
  hole-filling-v : ∀ {Δv Δc n m} → (v : Value n) → Δv ⨟ Δc ⨟ n ⊢v v → (u : ℕ) → Δv u ≡ just m → (v' : Value m) → Value n
  hole-filling-c : ∀ {Δv Δc n m} → (c : Computation n) → Δv ⨟ Δc ⨟ n ⊢c c → (u : ℕ) → Δv u ≡ just m → (v' : Value m) → Computation n
  hole-filling-subst : ∀ {Δv Δc m n m'} → (σ : Subst m n) → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m → (u : ℕ) → Δv u ≡ just m' → (v' : Value m') → Subst m n
  -- a helper function for hole case
  hole-filling-hole : ∀ {Δv Δc n} (i : ℕ) (nσ : ℕ) (σ : Subst nσ n)
                  → (x : Δv i ≡ just nσ)
                  → (p : ∀ {t} → Δv ⨟ Δc ⨟ n ⊢v σ t)
                  → (u : ℕ)
                  → (m : ℕ)
                  → Δv u ≡ just m
                  → (v' : Value m)
                  → Dec (i ≡ u)
                  → Value n

  hole-filling-v {m = m} (⁇ {m'} i σ) (hole x (sub p)) u x₁ v' = hole-filling-hole i m' σ x p u m x₁ v' (i ≟ u)
  hole-filling-v (‵ x₂) x u x₁ v' = ‵ x₂
  hole-filling-v (ƛ t) (abs x) u x₁ v' = ƛ hole-filling-c t x u x₁ v'
  hole-filling-v #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ (hand x₁ x₂) u x v' = 
                 #handler⟨ hole-filling-c cᵣ x₁ u x v' ⨟ op , hole-filling-c cₒₚ x₂ u x v' ⟩

  hole-filling-c (#ret v) (ret x) u x₁ v' = #ret (hole-filling-v v x u x₁ v')
  hole-filling-c (v ∙ t₁) (app x x₂) u x₁ v' = hole-filling-v v x u x₁ v' ∙ hole-filling-v t₁ x₂ u x₁ v'
  hole-filling-c (#let t₁ #in t₂) (bind x x₂) u x₁ v' = #let hole-filling-c t₁ x u x₁ v' #in hole-filling-c t₂ x₂ u x₁ v'
  hole-filling-c (⦃⁇⦄ i σ) (hole-c x₁ (sub p)) u x v' = ⦃⁇⦄ i (hole-filling-subst σ (sub p) u x v')
  hole-filling-c (#with h #handle c) (#with x₁ x₂) u x v' = 
                  #with hole-filling-v h x₁ u x v' #handle hole-filling-c c x₂  u x v'
  hole-filling-c (op ⟨ v ⨟ k ⟩) (opcall x₁ x₂) u x v' = op ⟨ hole-filling-v v x₁ u x v' ⨟  hole-filling-c k x₂ u x v' ⟩

  hole-filling-subst σ (sub p) u x₁ v' t = hole-filling-v (σ t) p u x₁ v'
  hole-filling-hole {Δv = Δv} {n = n} i nσ σ x p u m x₁ v' (yes eq) = substV σ' v'
    where
      m≡nσ : m ≡ nσ
      m≡nσ = just≡ (trans (sym x₁) (trans (cong Δv (sym eq)) x))

      σ' : Subst m n
      σ' = hole-filling-subst σ (sub p) u x₁ v' ∘ cast m≡nσ
  hole-filling-hole {n = n} i nσ σ x p u m x₁ v' (no _) = ⁇ i (hole-filling-subst σ (sub p) u x₁ v')

  -- filling lemmas for value, computation and substitution
  filling-value : ∀ {n' n Δv Δc u v v'} 
                → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢v v)
                → Δv ⨟ Δc ⨟ n' ⊢v v'
                ---------------------------------------------------
                → Δv ⨟ Δc ⨟ n ⊢v hole-filling-v v p1 u (⟨↦⟩≡ Δv u n') v'
  filling-comp : ∀ {n' n Δv Δc u c v'} 
                → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢c c)
                → Δv ⨟ Δc ⨟ n' ⊢v v'
                ---------------------------------------------------
                → Δv ⨟ Δc ⨟ n ⊢c hole-filling-c c p1 u (⟨↦⟩≡ Δv u n') v'

  filling-subst : ∀ {n' n n'' Δv Δc u σ v'}
                → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢ σ ⦂ n'')
                → Δv ⨟ Δc ⨟ n' ⊢v v'
                ---------------------------------------------------
                → Δv ⨟ Δc ⨟ n ⊢ hole-filling-subst σ p1 u (⟨↦⟩≡ Δv u n') v' ⦂ n''

  filling-value {n'} {n} {Δv} {Δc} {u} {v' = d'} (hole {u = u'} {σ = σ} k (sub x₃)) x₁ = go (u' ≟ u)
    where
      go : (w : Dec (u' ≡ u)) → Δv ⨟ Δc ⨟ n ⊢v hole-filling-hole u' _ σ k x₃ u n' (⟨↦⟩≡ Δv u n') d' w
      go (yes refl) = subst-value-gen {v = d'} x₁ (sub (λ {t} → filling-value x₃ x₁))
        where
          n'≡nσ = just≡ (trans (sym (⟨↦⟩≡ Δv u n')) k)
      go (no u'≢u) rewrite ⟨↦⟩≢ Δv u u' n' u'≢u = hole k (sub (λ {t} → filling-value x₃ x₁))
  filling-value var x₁ = var
  filling-value (abs p1) x₁ = abs (filling-comp p1 x₁)
  filling-value {v = #handler⟨ cᵣ ⨟ op , cₒₚ ⟩} (hand p1 p2) x₁ = hand (filling-comp p1 x₁) (filling-comp p2 x₁)

  filling-comp (ret p1) x₁ = ret (filling-value p1 x₁)
  filling-comp (app p1 p2) x₁ = app (filling-value p1 x₁) (filling-value p2 x₁)
  filling-comp (bind p1 p2) x₁ = bind (filling-comp p1 x₁) (filling-comp p2 x₁)
  filling-comp {c = ⦃⁇⦄ i σ} (hole-c x₂ (sub x₃)) x₁ = hole-c x₂ (filling-subst (sub x₃) x₁)
  filling-comp {c = #with h #handle c} (#with x₁ x₂) x₃ = #with (filling-value x₁ x₃) (filling-comp x₂ x₃)
  filling-comp {c = op ⟨ v ⨟ c ⟩} (opcall x₁ x₂) x₃ = opcall (filling-value x₁ x₃) (filling-comp x₂ x₃)

  filling-subst (sub p1) x₁ = sub λ {t} → filling-value p1 x₁

  rename-filling-v : ∀ {Δv Δc n m m' u x₁ v'}
    → (ρ : Renaming m n)
    → (v : Value m)
    → (p : Δv ⨟ Δc ⨟ m ⊢v v)
    → hole-filling-v {Δv = Δv} {Δc = Δc} {m = m'} (renameV ρ v) (rename-value-typed ρ p) u x₁ v'
    ≡ renameV ρ (hole-filling-v v p u x₁ v')

  rename-filling-c : ∀ {Δv Δc n m m' u x₁ v'}
    → (ρ : Renaming m n)
    → (c : Computation m)
    → (p : Δv ⨟ Δc ⨟ m ⊢c c)
    → hole-filling-c {Δv = Δv} {Δc = Δc} {m = m'} (renameC ρ c) (rename-comp-typed ρ p) u x₁ v'
    ≡ renameC ρ (hole-filling-c c p u x₁ v')

  rename-filling-s : ∀ {Δv Δc n k m m' u x₁ v'}
    → (ρ : Renaming n k)
    → (σ : Subst m n)
    → (p : Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m)
    → (t : Fin m)
    → hole-filling-subst {Δv = Δv} {Δc = Δc} {m = m} {m' = m'} (renameV ρ ∘ σ)
        (sub (λ {t} → rename-value-typed ρ (subst-lookup-typed p t))) u x₁ v' t
    ≡ renameV ρ (hole-filling-subst σ p u x₁ v' t)

  -- lemmas for substitution ext
  subst-comm-exts : ∀ {m n n' Δv Δc u v'}
                 → (σ : Subst m n)
                 → (p : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢ σ ⦂ m)
                 → (λ t → hole-filling-v (exts σ t) (subst-lookup-typed (exts-typed p) t) u (⟨↦⟩≡ Δv u n') v')
                 ≡ exts (hole-filling-subst σ p u (⟨↦⟩≡ Δv u n') v')
  subst-comm-exts σ (sub p) = extensionality λ { F.zero → refl ; (F.suc x₁) → rename-filling-v F.suc (σ x₁) p }

  rename-filling-v-suc2 : ∀ {Δv Δc m m' u v'} {x₁ : Δv u ≡ just m'}
    → (v : Value m)
    → (p : Δv ⨟ Δc ⨟ m ⊢v v)
    → hole-filling-v (renameV F.suc (renameV F.suc v))
        (rename-value-typed F.suc (rename-value-typed F.suc p)) u x₁ v'
    ≡ renameV F.suc (renameV F.suc (hole-filling-v v p u x₁ v'))
  rename-filling-v-suc2 {Δv} {Δc} {m} {m'} {u} {v'} {x₁} v p 
    rewrite (sym (rename-filling-v {u = u} {x₁ = x₁} {v' = v'} F.suc v p))
    = rename-filling-v F.suc (renameV F.suc v) (rename-value-typed F.suc p)

  subst-comm-exts2 : ∀ {m n n' Δv Δc u v'} 
                 → (σ : Subst m n)
                 → (p : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢ σ ⦂ m)
                 → (λ t → hole-filling-v (exts (exts σ) t) (subst-lookup-typed (exts-typed (exts-typed p)) t) u (⟨↦⟩≡ Δv u n') v')
                 ≡ exts (exts (hole-filling-subst σ p u (⟨↦⟩≡ Δv u n') v')) 
  subst-comm-exts2 σ (sub x₁) = extensionality λ { F.zero → refl ; (F.suc F.zero) → refl
                                                   ; (F.suc (F.suc x₂)) → rename-filling-v-suc2 (σ x₂) x₁ }

  -- substitution commutativity
  subst-comm-c-gen : ∀ {n' Δv Δc u c v'} {σ : Subst m n}
                 → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ m ⊢c c)
                 → (p2 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢ σ ⦂ m)
                 → Δv ⨟ Δc ⨟ n' ⊢v v' 
                 ----------------------------------------------------------------
                 → hole-filling-c (substC σ c) (subst-comp-gen p1 p2) u (⟨↦⟩≡ Δv u n') v' 
                 ≡ substC (hole-filling-subst σ p2 u (⟨↦⟩≡ Δv u n') v') (hole-filling-c c p1 u (⟨↦⟩≡ Δv u n') v') 
  subst-comm-v-gen : ∀ {n' Δv Δc u v v'} {σ : Subst m n}
                 → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ m ⊢v v)
                 → (p2 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢ σ ⦂ m)
                 → Δv ⨟ Δc ⨟ n' ⊢v v' 
                 ----------------------------------------------------------------
                 → hole-filling-v (substV σ v) (subst-value-gen p1 p2) u (⟨↦⟩≡ Δv u n') v' 
                 ≡ substV (hole-filling-subst σ p2 u (⟨↦⟩≡ Δv u n') v') (hole-filling-v v p1 u (⟨↦⟩≡ Δv u n') v') 
  subst-comm-s-gen : ∀ {m n n' Δv Δc u v'} {σ : Subst m n}
                 → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢ σ ⦂ m)
                 → (p2 : Δv ⨟ Δc ⨟ n' ⊢v v')
                 → ∀ (t : Fin m)
                 → hole-filling-v (σ t) (subst-lookup-typed p1 t) u (⟨↦⟩≡ Δv u n') v'
                 ≡ (hole-filling-subst σ p1 u (⟨↦⟩≡ Δv u n') v') t
  subst-comm-c-gen {c = #ret x₂} (ret x₃) (sub x₄) x₁ = cong #ret (subst-comm-v-gen x₃ (sub x₄) x₁)
  subst-comm-c-gen {c = x₂ ∙ x₃} (app x₄ x₅) (sub x₆) x₁ = cong₂ _∙_ (subst-comm-v-gen x₄ (sub x₆) x₁) (subst-comm-v-gen x₅ (sub x₆) x₁)
  subst-comm-c-gen {m} {n} {n'} {Δv} {Δc} {u} {c = #let c #in c₁} {v'} {σ} (bind p1 p3) (sub x₂) x₁  
    rewrite subst-comm-c-gen {σ = σ} p1 (sub x₂) x₁
    | subst-comm-c-gen {σ = exts σ} p3 (exts-typed (sub x₂)) x₁
    | subst-comm-exts {n' = n'} {v' = v'} σ (sub x₂)
    = refl 
  subst-comm-c-gen {c = ⦃⁇⦄ i σᵢ} (hole-c x₂ (sub x₃)) (sub x₄) x₁ =
    cong (⦃⁇⦄ i) (extensionality λ t → subst-comm-v-gen (x₃ {t}) (sub x₄) x₁)
  subst-comm-c-gen {c = #with h #handle c} (#with p1 p2) (sub x₃) x₁ =
    cong₂ #with_#handle_ (subst-comm-v-gen p1 (sub x₃) x₁) (subst-comm-c-gen p2 (sub x₃) x₁)
  subst-comm-c-gen {m} {n} {n'} {Δv} {Δc} {u} {c = op ⟨ v ⨟ k ⟩} {v'} {σ} (opcall p1 p2) (sub pσ) x₁ 
    rewrite subst-comm-v-gen {σ = σ} p1 (sub pσ) x₁
    | subst-comm-c-gen {σ = exts σ} p2 (exts-typed (sub pσ)) x₁
    | subst-comm-exts {n' = n'} {v' = v'} σ (sub pσ)
    = refl
  subst-comm-v-gen {m} {n} {n'} {Δv} {Δc} {u} {v = ⁇ i σᵢ} {v'} {σ} (hole x₄ (sub {m = m₁} pσᵢ)) (sub pσ) pv' = go (i ≟ u)
    where
      hole-filling-subst-comp :
        ∀ (m≡m₁ : n' ≡ m₁)
          → hole-filling-subst (σ ∘ₛ σᵢ) (sub (λ {t} → subst-value-gen pσᵢ (sub pσ))) u (⟨↦⟩≡ Δv u n') v'
            ∘ cast m≡m₁
          ≡ (λ t → hole-filling-v (σ t) pσ u (⟨↦⟩≡ Δv u n') v')
            ∘ₛ (hole-filling-subst σᵢ (sub pσᵢ) u (⟨↦⟩≡ Δv u n') v' ∘ cast m≡m₁)
      hole-filling-subst-comp m≡m₁ = extensionality λ t → subst-comm-v-gen {σ = σ} (pσᵢ {t = cast m≡m₁ t}) (sub pσ) pv'

      go : (d : Dec (i ≡ u)) → hole-filling-hole i m₁ (σ ∘ₛ σᵢ) x₄
        (λ {t} → subst-value-gen pσᵢ (sub pσ)) u n' (⟨↦⟩≡ Δv u n') v' d
        ≡ substV (λ t → hole-filling-v (σ t) pσ u (⟨↦⟩≡ Δv u n') v') (hole-filling-hole i m₁ σᵢ x₄ pσᵢ u n' (⟨↦⟩≡ Δv u n') v' d)

      -- If i == u, the hole is filled, so we must show substitution composition agrees.
      go (yes k) = trans (cong (λ σ' → substV σ' v') (hole-filling-subst-comp m≡m₁))
                         (sym (substV-comp (λ t → hole-filling-v (σ t) pσ u (⟨↦⟩≡ Δv u n') v') σR v'))
        where
          m≡m₁ : n' ≡ m₁
          m≡m₁ = just≡ (trans (sym (⟨↦⟩≡ Δv u n')) (trans (cong (Δv ⟨ u ↦ n' ⟩) (sym k)) x₄))

          σR : Subst n' m
          σR = hole-filling-subst σᵢ (sub pσᵢ) u (⟨↦⟩≡ Δv u n') v' ∘ cast m≡m₁

      -- If i != u, the hole remains and we recurse pointwise into σᵢ.
      go (no k) = cong (⁇ i) (extensionality λ t → subst-comm-v-gen {σ = σ} (pσᵢ {t}) (sub pσ) pv')

  subst-comm-v-gen {v = ‵ x₂} var (sub x₃) x₁ = refl

  subst-comm-v-gen {m} {n} {n'} {Δv} {Δc} {u} {v = ƛ x₂} {v'} {σ} (abs x₃) p2@(sub p) x₁
    rewrite (subst-comm-c-gen x₃ (exts-typed p2) x₁)
    | subst-comm-exts {n' = n'} {v' = v'} σ (sub p)
    = refl
  subst-comm-v-gen {m} {n} {n'} {Δv} {Δc} {u} {v = #handler⟨ cᵣ ⨟ op , cₒₚ ⟩} {v'} {σ} (hand p1 p2) p3@(sub pσ) x₁
    rewrite subst-comm-c-gen p1 (exts-typed p3) x₁
    | subst-comm-c-gen p2 (exts-typed (exts-typed p3)) x₁
    | subst-comm-exts {n' = n'} {v' = v'} σ (sub pσ)
    | subst-comm-exts2  {n' = n'} {v' = v'} σ (sub pσ)
    = refl
  subst-comm-s-gen (sub x₁) p2 t = refl

  rename-filling-v {Δv = Δv} {Δc = Δc} {m = m₁} {m' = m'} {u = u} {x₁ = x₄} {v' = v'} ρ (⁇ {m0} x x₁) (hole x₂ (sub x₃)) with x ≟ u 
  ... | yes k = trans
                  (cong (λ σ → substV σ v') (extensionality λ t → rename-filling-s ρ x₁ (sub x₃) (cast m'≡m0 t)))
                  (rename-subst-v ρ σR v')
    where
      m'≡m0 : m' ≡ m0
      m'≡m0 = just≡ (trans (sym x₄) (trans (cong Δv (sym k)) x₂))

      σR : Subst m' m₁
      σR = hole-filling-subst x₁ (sub x₃) u x₄ v' ∘ cast m'≡m0
  ... | no k = cong (⁇ x) (extensionality λ x₄ → rename-filling-v ρ (x₁ x₄) x₃)
  rename-filling-v ρ (‵ x) p = refl
  rename-filling-v ρ (ƛ x) (abs x₁) = cong ƛ_ (rename-filling-c (ext ρ) x x₁)
  rename-filling-v ρ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ (hand x x₁) =
    cong₂ (λ cᵣ' cₒₚ' → #handler⟨ cᵣ' ⨟ op , cₒₚ' ⟩)
      (rename-filling-c (ext ρ) cᵣ x)
      (rename-filling-c (ext (ext ρ)) cₒₚ x₁)
  rename-filling-c ρ (#ret x) (ret x₁) = cong #ret (rename-filling-v ρ x x₁)
  rename-filling-c ρ (x ∙ x₁) (app x₂ x₃) = cong₂ _∙_ (rename-filling-v ρ x x₂) (rename-filling-v ρ x₁ x₃)
  rename-filling-c ρ (#let c #in c₁) (bind p p₁) = cong₂ #let_#in_ (rename-filling-c ρ c p) (rename-filling-c (ext ρ) c₁ p₁) 
  rename-filling-c ρ (⦃⁇⦄ i σ) (hole-c x (sub x₁)) =
    cong (⦃⁇⦄ i) (extensionality λ t → rename-filling-s ρ σ (sub x₁) t)
  rename-filling-c ρ (#with h #handle c) (#with x x₁) =
    cong₂ #with_#handle_ (rename-filling-v ρ h x) (rename-filling-c ρ c x₁)
  rename-filling-c ρ (op ⟨ v ⨟ k ⟩) (opcall x x₁) =
    cong₂ (λ v' k' → op ⟨ v' ⨟ k' ⟩) (rename-filling-v ρ v x) (rename-filling-c (ext ρ) k x₁)
  rename-filling-s ρ σ (sub x) t = rename-filling-v ρ (σ t) x

  subst-comm-n-c : ∀ {n n' Δv Δc u c v v'} 
         → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ suc n ⊢c c)
         → (p2 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢v v)
         → Δv ⨟ Δc ⨟ n' ⊢v v' 
                 ----------------------------------------------------------------
         → hole-filling-c (c [ v ]c) (subst-comp p1 p2) u (⟨↦⟩≡ Δv u n') v' 
         ≡ (hole-filling-c c p1 u (⟨↦⟩≡ Δv u n') v') [ hole-filling-v v p2 u (⟨↦⟩≡ Δv u n') v' ]c
  subst-comm-n-v : ∀ {n n' Δv Δc u v1 v2 v'} 
         → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ suc n ⊢v v1)
         → (p2 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢v v2)
         → Δv ⨟ Δc ⨟ n' ⊢v v' 
                 ----------------------------------------------------------------
         → hole-filling-v (v1 [ v2 ]v) (subst-value p1 p2) u (⟨↦⟩≡ Δv u n') v' 
         ≡ (hole-filling-v v1 p1 u (⟨↦⟩≡ Δv u n') v') [ hole-filling-v v2 p2 u (⟨↦⟩≡ Δv u n') v' ]v
  subst-comm-n-c {n} {n'} {Δv} {Δc} {u} {c} {v} {v'} p1 p2 x₁ = trans (subst-comm-c-gen p1 (subst-zero-typed p2) x₁) 
                        (cong (λ σ → substC σ (hole-filling-c c p1 u (⟨↦⟩≡ Δv u n') v')) 
                                                                  (extensionality λ { F.zero → refl ; (F.suc x) → refl })) 
  subst-comm-n-v {n} {n'} {Δv} {Δc} {u} {v1} {v2} {v'} p1 p2 x₁ = trans (subst-comm-v-gen p1 (subst-zero-typed p2) x₁) 
                      (cong (λ σ → substV σ (hole-filling-v v1 p1 u (⟨↦⟩≡ Δv u n') v')) 
                                                                    (extensionality λ { F.zero → refl ; (F.suc x) → refl }))

  subst-comm-c : ∀ {n' Δv Δc u c v v'} 
                 → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ 1 ⊢c c)
                 → (p2 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ 0 ⊢v v)
                 → Δv ⨟ Δc ⨟ n' ⊢v v' 
                 ----------------------------------------------------------------
                 → hole-filling-c (c [ v ]c) (subst-comp p1 p2) u (⟨↦⟩≡ Δv u n') v' 
                 ≡ (hole-filling-c c p1 u (⟨↦⟩≡ Δv u n') v') [ hole-filling-v v p2 u (⟨↦⟩≡ Δv u n') v' ]c
  subst-comm-v : ∀ {n' Δv Δc u v1 v2 v'} 
                 → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ 1 ⊢v v1)
                 → (p2 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ 0 ⊢v v2)
                 → Δv ⨟ Δc ⨟ n' ⊢v v' 
                 ----------------------------------------------------------------
                 → hole-filling-v (v1 [ v2 ]v) (subst-value p1 p2) u (⟨↦⟩≡ Δv u n') v' 
                 ≡ (hole-filling-v v1 p1 u (⟨↦⟩≡ Δv u n') v') [ hole-filling-v v2 p2 u (⟨↦⟩≡ Δv u n') v' ]v
  subst-comm-c p1 p2 x₁ = subst-comm-n-c p1 p2 x₁
  subst-comm-v p1 p2 x₁ = subst-comm-n-v p1 p2 x₁

  β-op-eq-case : ∀ {Δv Δc n n' u} {d' : Value n'}
            (cᵣ : Computation (suc n)) (cₒₚ : Computation (2+ n)) (v : Value n) (k : Computation (suc n))
            (op : ℕ)
            (x₁ : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ suc n ⊢c cᵣ) (x₂ : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ 2+ n ⊢c cₒₚ)
            (x₃ : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢v v) (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ suc n ⊢c k)
            (p2 : Δv ⨟ Δc ⨟ n' ⊢v d')
            → (hole-filling-c
                  (cₒₚ [ v ⨟
                  ƛ (#with #handler⟨ liftC-ret cᵣ ⨟ op , liftC-op cₒₚ ⟩ #handle k) ]c)
                  (-→-preserve β-op-eq (#with (hand x₁ x₂) (opcall x₃ p1))) u
                  (⟨↦⟩≡ Δv u n') d')
            ≡ (hole-filling-c cₒₚ x₂ u (⟨↦⟩≡ Δv u n') d'
                [ hole-filling-v v x₃ u (⟨↦⟩≡ Δv u n') d'
                ⨟ ƛ (#with #handler⟨ liftC-ret (hole-filling-c cᵣ x₁ u (⟨↦⟩≡ Δv u n') d')
                ⨟ op , liftC-op (hole-filling-c cₒₚ x₂ u (⟨↦⟩≡ Δv u n') d') ⟩ #handle hole-filling-c k p1 u (⟨↦⟩≡ Δv u n') d') ]c)
  β-op-eq-case {Δv} {Δc} {n} {n'} {u} {d'} cᵣ cₒₚ v k op x₁ x₂ x₃ p1 p2 = trans (subst-comm-c-gen x₂ (subst-subst-gen (exts-typed (subst-zero-typed x₃))
                                                                                                                         (subst-zero-typed (contV-typed (hand x₁ x₂) p1))) p2)
          (cong (λ σ →  substC σ (hole-filling-c cₒₚ x₂ u (⟨↦⟩≡ Δv u n') d'))
          (extensionality λ { F.zero → cong₂ (λ x y → ƛ #with #handler⟨ x ⨟ op , y ⟩ #handle hole-filling-c k p1 u (⟨↦⟩≡ Δv u n') d')
                                                      (rename-filling-c (ext F.suc) cᵣ x₁) (rename-filling-c (ext (ext F.suc)) cₒₚ x₂)
                            ; (F.suc F.zero) → case1 ; (F.suc (F.suc x)) → refl}))
    where
      σ = (subst-zero (ƛ (#with #handler⟨ renameC (ext F.suc) cᵣ ⨟ op , renameC (ext (ext F.suc)) cₒₚ ⟩ #handle k)))
      σ-typed = subst-zero-typed (abs (#with (hand (rename-comp-typed (ext F.suc) x₁) (rename-comp-typed (ext (ext F.suc)) x₂)) p1))
      v' : Value (suc n)
      v' = renameV F.suc v
      σv'-typed = (subst-value-gen (rename-value-typed F.suc x₃) (subst-zero-typed (contV-typed (hand x₁ x₂) p1)))
      u-w = ⟨↦⟩≡ Δv u n'

      case1 : hole-filling-v (substV σ v') σv'-typed u u-w d'
        ≡ (subst-zero
         (ƛ
          (#with
           #handler⟨ liftC-ret (hole-filling-c cᵣ x₁ u u-w d') ⨟ op ,
           liftC-op (hole-filling-c cₒₚ x₂ u u-w d') ⟩
           #handle hole-filling-c k p1 u u-w d'))
         ∘ₛ exts (subst-zero (hole-filling-v v x₃ u u-w d')))
        (F.suc F.zero)
      case1 = trans y (cong₂ substV (extensionality (λ { F.zero → cong₂ (λ x y → ƛ #with #handler⟨ x ⨟ op , y ⟩  #handle hole-filling-c k p1 u u-w d')
                                                                    (rename-filling-c (ext F.suc) cᵣ x₁) (rename-filling-c (ext (ext F.suc)) cₒₚ x₂)
                                                   ; (F.suc x) → refl})) (rename-filling-v F.suc v x₃))
        where
          y : hole-filling-v (substV σ v') σv'-typed u u-w d'
               ≡ substV (hole-filling-subst σ σ-typed u u-w d') (hole-filling-v v' (rename-value-typed F.suc x₃) u u-w d')
          y = subst-comm-v-gen {Δv = Δv} {Δc = Δc} {v' = d'} {σ = σ} (rename-value-typed F.suc x₃) σ-typed p2

  mutual
    -→v--→v*-comm-gen : ∀ {n' Δv Δc u v v' d'}
                  → (s : v -→v v')
                  → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢v v)
                  → (p2 : Δv ⨟ Δc ⨟ n' ⊢v d')
                  → hole-filling-v v p1 u (⟨↦⟩≡ Δv u n') d' -→v* hole-filling-v v' (-→v-preserve s p1) u (⟨↦⟩≡ Δv u n') d'
    -→v--→v*-comm-gen (ξ-ƛ s) (abs p1) p2 =
      ξ-ƛ* (-→--→*-comm-gen s p1 p2)
    -→v--→v*-comm-gen (ξ-hand₁ s) (hand p1 p2) p3 =
      ξ-hand₁* (-→--→*-comm-gen s p1 p3)
    -→v--→v*-comm-gen (ξ-hand₂ s) (hand p1 p2) p3 =
      ξ-hand₂* (-→--→*-comm-gen s p2 p3)
    -→v--→v*-comm-gen {n' = n'} {Δv = Δv} {Δc = Δc} {u = u} {d' = d'}
      (ξ-hole-v {m = m} {i = i} {σ = σ} {σ' = σ'} (ξ-σ x s rest)) (hole h (sub p)) p2 =
      go (i ≟ u) h
      where
        x₁ = ⟨↦⟩≡ Δv u n'
        p' = λ {t} → subst-lookup-typed (-→s-preserve (ξ-σ x s rest) (sub p)) t
        go : (w : Dec (i ≡ u)) (h' : (Δv ⟨ u ↦ n' ⟩) i ≡ just m) →
             hole-filling-hole i m σ h' p u n' x₁ d' w -→v*
             hole-filling-hole i m σ' h' p' u n' x₁ d' w
        go (yes refl) h' =
          substV-preserves-→v* d' (λ y → -→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2 (cast m≡n' y))
          where
            m≡n' : n' ≡ m
            m≡n' = just≡ (trans (sym x₁) h')
        go (no neq) h' =
          hole-v-multistep (-→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2)

    -→s--→s*-comm-gen : ∀ {m n' Δv Δc u σ σ' d'}
                  → (s : σ -→s σ')
                  → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢ σ ⦂ m)
                  → (p2 : Δv ⨟ Δc ⨟ n' ⊢v d')
                  → hole-filling-subst σ p1 u (⟨↦⟩≡ Δv u n') d' -→s* hole-filling-subst σ' (-→s-preserve s p1) u (⟨↦⟩≡ Δv u n') d'
    -→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2 t with t F.≟ x
    ... | yes refl = -→v--→v*-comm-gen s (p {x}) p2
    ... | no neq rewrite sym (rest t neq) = 0 , -→vZ

    -→--→*-comm-gen : ∀ {n' Δv Δc u d₁ d₂ d'}
                  → (s : d₁ -→ d₂)
                  → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢c d₁)
                  → (p2 : Δv ⨟ Δc ⨟ n' ⊢v d')
                  → hole-filling-c d₁ p1 u (⟨↦⟩≡ Δv u n') d' -→* hole-filling-c d₂ (-→-preserve s p1) u (⟨↦⟩≡ Δv u n') d'
    -→--→*-comm-gen β (app (abs p1) p2) p3 rewrite subst-comm-n-c p1 p2 p3 = -→trans-→* β -→*-refl
    -→--→*-comm-gen β-let (bind (ret p1) p2) p3 rewrite subst-comm-n-c p2 p1 p3 = -→trans-→* β-let -→*-refl
    -→--→*-comm-gen {n} {n'} {Δv} {Δc} {u} {#let op ⟨ v ⨟ k ⟩ #in c} {d₂} {d'} op-let (bind (opcall x₁ x₂) x₃) p2
      rewrite rename-filling-c {u = u} {x₁ = (⟨↦⟩≡ Δv u n')} {v' = d'} (ext F.suc) c x₃
      = -→trans-→* op-let -→*-refl
    -→--→*-comm-gen β-ret (#with (hand x₁ x₂) (ret x₃)) p2 rewrite subst-comm-n-c x₁ x₃ p2 = -→trans-→* β-ret -→*-refl
    -→--→*-comm-gen {n} {n'} {Δv} {Δc} {u} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op ⟨ v ⨟ k ⟩} {d₂} {d'} β-op-eq (#with (hand x₁ x₂) (opcall x₃ p1)) p2
      rewrite β-op-eq-case {Δv} {Δc} {n} {n'} {u} {d'} cᵣ cₒₚ v k op x₁ x₂ x₃ p1 p2
      = -→trans-→* β-op-eq -→*-refl
    -→--→*-comm-gen {n} {n'} {Δv} {Δc} {u} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op' ⟨ v ⨟ k ⟩} {d₂} {d'} (β-op-neq x₂) (#with (hand x₁ x₃) (opcall x₄ p1)) p2
      rewrite rename-filling-c {u = u} {x₁ = (⟨↦⟩≡ Δv u n')} {v' = d'} (ext F.suc) cᵣ x₁
            | rename-filling-c {u = u} {x₁ = (⟨↦⟩≡ Δv u n')} {v' = d'} (ext (ext F.suc)) cₒₚ x₃
      = -→trans-→* (β-op-neq x₂) -→*-refl
    -→--→*-comm-gen (ξ-ret s) (ret p1) p2 =
      ξ-ret* (-→v--→v*-comm-gen s p1 p2)
    -→--→*-comm-gen (ξ-hole-c (ξ-σ x s rest)) (hole-c h (sub p)) p2 =
      hole-c-multistep (-→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2)
    -→--→*-comm-gen (ξ-app₁ s) (app p1 p2) p3 = ξ-app₁* (-→v--→v*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-app₂ s) (app p1 p2) p3 = ξ-app₂* (-→v--→v*-comm-gen s p2 p3)
    -→--→*-comm-gen (ξ-let s) (bind p1 p2) p3 = ξ-let* (-→--→*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-in s) (bind p1 p2) p3 = ξ-in* (-→--→*-comm-gen s p2 p3)
    -→--→*-comm-gen (ξ-with₁ s) (#with p1 p2) p3 = ξ-with₁* (-→v--→v*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-with₂ s) (#with p1 p2) p3 = ξ-with₂* (-→--→*-comm-gen s p2 p3)
    -→--→*-comm-gen (ξ-op₁ s) (opcall p1 p2) p3 = ξ-op₁* (-→v--→v*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-op₂ s) (opcall p1 p2) p3 = ξ-op₂* (-→--→*-comm-gen s p2 p3)

  -- the main commutativity theorem
  -→*-comm : ∀ {n n' Δv Δc u d₁ d₂ d'}
           → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢c d₁)
           → (p2 : Δv ⨟ Δc ⨟ n' ⊢v d')
           → (s : d₁ -→* d₂)
           → hole-filling-c d₁ p1 u (⟨↦⟩≡ Δv u n') d' -→* hole-filling-c d₂ (-→*-preserve p1 s) u (⟨↦⟩≡ Δv u n') d'
  -→*-comm p1 p2 (fst , -→Z) = 0 , -→Z
  -→*-comm {n} {n'} {Δv} {Δc} {u} {d₁} {d₂} {d'} p1 p2 (suc n'' , (_-→S_ {M = M} s snd)) 
           = trans-→* (-→--→*-comm-gen s p1 p2) (-→*-comm (-→-preserve s p1) p2 (n'' , snd))

  -- the main fill-and-resume soundness theorem
  resumption : ∀ {n n' Δv Δc u d d₁ d'}
             → (p1 : Δv ⟨ u ↦ n' ⟩ ⨟ Δc ⨟ n ⊢c d)
             → (p2 : Δv ⨟ Δc ⨟ n' ⊢v d')
             → (s : d -→* d₁)
             → ∃[ d₂ ] (hole-filling-c d p1 u (⟨↦⟩≡ Δv u n') d' -→* d₂ × hole-filling-c d₁ (-→*-preserve p1 s) u (⟨↦⟩≡ Δv u n') d' -→* d₂)
  resumption p1 p2 s = confluence -→*-refl (-→*-comm p1 p2 s)
  
module Impure where

  hole-filling-v : ∀ {Δv Δc n m} → (v : Value n) → Δv ⨟ Δc ⨟ n ⊢v v → (u : ℕ) → Δc u ≡ just m → (c' : Computation m) → Value n
  hole-filling-c : ∀ {Δv Δc n m} → (c : Computation n) → Δv ⨟ Δc ⨟ n ⊢c c → (u : ℕ) → Δc u ≡ just m → (c' : Computation m) → Computation n
  hole-filling-subst : ∀ {Δv Δc m n m'} → (σ : Subst m n) → Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m → (u : ℕ) → Δc u ≡ just m' → (c' : Computation m') → Subst m n
  hole-filling-hole : ∀ {Δv Δc n} (i : ℕ) (nσ : ℕ) (σ : Subst nσ n)
                  → (x : Δc i ≡ just nσ)
                  → (p : ∀ {t} → Δv ⨟ Δc ⨟ n ⊢v σ t)
                  → (u : ℕ)
                  → (m : ℕ)
                  → Δc u ≡ just m
                  → (c' : Computation m)
                  → Dec (i ≡ u)
                  → Computation n

  hole-filling-v {m = m} (⁇ {m'} i σ) (hole x (sub p)) u x₁ c' = ⁇ i (hole-filling-subst σ (sub p) u x₁ c')
  hole-filling-v (‵ x₂) x u x₁ c' = ‵ x₂
  hole-filling-v (ƛ t) (abs x) u x₁ c' = ƛ hole-filling-c t x u x₁ c'
  hole-filling-v #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ (hand x₁ x₂) u x c' =
                 #handler⟨ hole-filling-c cᵣ x₁ u x c' ⨟ op , hole-filling-c cₒₚ x₂ u x c' ⟩

  hole-filling-c (#ret v) (ret x) u x₁ c' = #ret (hole-filling-v v x u x₁ c')
  hole-filling-c (v ∙ t₁) (app x x₂) u x₁ c' = hole-filling-v v x u x₁ c' ∙ hole-filling-v t₁ x₂ u x₁ c'
  hole-filling-c (#let t₁ #in t₂) (bind x x₂) u x₁ c' = #let hole-filling-c t₁ x u x₁ c' #in hole-filling-c t₂ x₂ u x₁ c'
  hole-filling-c (⦃⁇⦄ i σ) (hole-c x₁ (sub p)) u x c' = hole-filling-hole i _ σ x₁ p u _ x c' (i ≟ u)
  hole-filling-c (#with h #handle c) (#with x₁ x₂) u x c' =
                  #with hole-filling-v h x₁ u x c' #handle hole-filling-c c x₂  u x c'
  hole-filling-c (op ⟨ v ⨟ k ⟩) (opcall x₁ x₂) u x c' = op ⟨ hole-filling-v v x₁ u x c' ⨟  hole-filling-c k x₂ u x c' ⟩

  hole-filling-subst σ (sub p) u x₁ c' t = hole-filling-v (σ t) p u x₁ c'
  hole-filling-hole {Δc = Δc} {n = n} i nσ σ x p u m x₁ c' (yes eq) = substC σ' c'
    where
      m≡nσ : m ≡ nσ
      m≡nσ = just≡ (trans (sym x₁) (trans (cong Δc (sym eq)) x))

      σ' : Subst m n
      σ' = hole-filling-subst σ (sub p) u x₁ c' ∘ cast m≡nσ
  hole-filling-hole {n = n} i nσ σ x p u m x₁ c' (no _) = ⦃⁇⦄ i (hole-filling-subst σ (sub p) u x₁ c')

  -- impure filling lemmas for value, computation and substitution
  filling-value : ∀ {n' n Δv Δc u v c'}
                → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢v v)
                → Δv ⨟ Δc ⨟ n' ⊢c c'
                ---------------------------------------------------
                → Δv ⨟ Δc ⨟ n ⊢v hole-filling-v v p1 u (⟨↦⟩≡ Δc u n') c'

  filling-comp : ∀ {n' n Δv Δc u c c'}
                → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢c c)
                → Δv ⨟ Δc ⨟ n' ⊢c c'
                ---------------------------------------------------
                → Δv ⨟ Δc ⨟ n ⊢c hole-filling-c c p1 u (⟨↦⟩≡ Δc u n') c'

  filling-subst-lemma : ∀ {n' n n'' Δv Δc u σ c'}
                → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢ σ ⦂ n'')
                → Δv ⨟ Δc ⨟ n' ⊢c c'
                ---------------------------------------------------
                → Δv ⨟ Δc ⨟ n ⊢ hole-filling-subst σ p1 u (⟨↦⟩≡ Δc u n') c' ⦂ n''

  filling-value (hole k (sub x₃)) x₁ = hole k (sub (λ {t} → filling-value x₃ x₁))
  filling-value var x₁ = var
  filling-value (abs p1) x₁ = abs (filling-comp p1 x₁)
  filling-value {v = #handler⟨ cᵣ ⨟ op , cₒₚ ⟩} (hand p1 p2) x₁ = hand (filling-comp p1 x₁) (filling-comp p2 x₁)

  filling-comp (ret p1) x₁ = ret (filling-value p1 x₁)
  filling-comp (app p1 p2) x₁ = app (filling-value p1 x₁) (filling-value p2 x₁)
  filling-comp (bind p1 p2) x₁ = bind (filling-comp p1 x₁) (filling-comp p2 x₁)
  filling-comp {n'} {n} {Δv} {Δc} {u} {c = ⦃⁇⦄ i σ} {c' = d'} (hole-c x₂ (sub x₃)) x₁ = go (i ≟ u)
    where
      go : (w : Dec (i ≡ u)) → Δv ⨟ Δc ⨟ n ⊢c hole-filling-hole i _ σ x₂ x₃ u n' (⟨↦⟩≡ Δc u n') d' w
      go (yes refl) = subst-comp-gen x₁ (sub (λ {t} → filling-value x₃ x₁))
      go (no i≢u) rewrite ⟨↦⟩≢ Δc u i n' i≢u = hole-c x₂ (sub (λ {t} → filling-value x₃ x₁))
  filling-comp {c = #with h #handle c} (#with x₁ x₂) x₃ = #with (filling-value x₁ x₃) (filling-comp x₂ x₃)
  filling-comp {c = op ⟨ v ⨟ c ⟩} (opcall x₁ x₂) x₃ = opcall (filling-value x₁ x₃) (filling-comp x₂ x₃)

  filling-subst-lemma (sub p1) x₁ = sub λ {t} → filling-value p1 x₁

  rename-filling-v : ∀ {Δv Δc n m m' u x₁ c'}
    → (ρ : Renaming m n)
    → (v : Value m)
    → (p : Δv ⨟ Δc ⨟ m ⊢v v)
    → hole-filling-v {Δv = Δv} {Δc = Δc} {m = m'} (renameV ρ v) (rename-value-typed ρ p) u x₁ c'
    ≡ renameV ρ (hole-filling-v v p u x₁ c')

  rename-filling-c : ∀ {Δv Δc n m m' u x₁ c'}
    → (ρ : Renaming m n)
    → (c : Computation m)
    → (p : Δv ⨟ Δc ⨟ m ⊢c c)
    → hole-filling-c {Δv = Δv} {Δc = Δc} {m = m'} (renameC ρ c) (rename-comp-typed ρ p) u x₁ c'
    ≡ renameC ρ (hole-filling-c c p u x₁ c')

  rename-filling-s : ∀ {Δv Δc n k m m' u x₁ c'}
    → (ρ : Renaming n k)
    → (σ : Subst m n)
    → (p : Δv ⨟ Δc ⨟ n ⊢ σ ⦂ m)
    → (t : Fin m)
    → hole-filling-subst {Δv = Δv} {Δc = Δc} {m = m} {m' = m'} (renameV ρ ∘ σ)
        (sub (λ {t} → rename-value-typed ρ (subst-lookup-typed p t))) u x₁ c' t
    ≡ renameV ρ (hole-filling-subst σ p u x₁ c' t)

  rename-filling-v ρ (⁇ x x₁) (hole x₂ (sub x₃)) =
    cong (⁇ x) (extensionality λ t → rename-filling-v ρ (x₁ t) x₃)
  rename-filling-v ρ (‵ x) p = refl
  rename-filling-v ρ (ƛ x) (abs x₁) = cong ƛ_ (rename-filling-c (ext ρ) x x₁)
  rename-filling-v ρ #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ (hand x x₁) =
    cong₂ (λ cᵣ' cₒₚ' → #handler⟨ cᵣ' ⨟ op , cₒₚ' ⟩)
      (rename-filling-c (ext ρ) cᵣ x)
      (rename-filling-c (ext (ext ρ)) cₒₚ x₁)
  rename-filling-c ρ (#ret x) (ret x₁) = cong #ret (rename-filling-v ρ x x₁)
  rename-filling-c ρ (x ∙ x₁) (app x₂ x₃) = cong₂ _∙_ (rename-filling-v ρ x x₂) (rename-filling-v ρ x₁ x₃)
  rename-filling-c ρ (#let c #in c₁) (bind p p₁) = cong₂ #let_#in_ (rename-filling-c ρ c p) (rename-filling-c (ext ρ) c₁ p₁)
  rename-filling-c {Δv = Δv} {Δc = Δc} {u = u} {x₁ = x₂} {c' = c'} ρ (⦃⁇⦄ i σ) (hole-c x (sub x₁)) with i ≟ u
  ... | yes k = trans
                  (cong (λ σ → substC σ c') (extensionality λ t → rename-filling-s ρ σ (sub x₁) (cast m≡nσ t)))
                  (sym (renameC-subst ρ σR c'))
    where
      m≡nσ : _ ≡ _
      m≡nσ = just≡ (trans (sym x₂) (trans (cong Δc (sym k)) x))
      σR : Subst _ _
      σR = hole-filling-subst σ (sub x₁) u x₂ c' ∘ cast m≡nσ
  ... | no k = cong (⦃⁇⦄ i) (extensionality λ t → rename-filling-s ρ σ (sub x₁) t)
  rename-filling-c ρ (#with h #handle c) (#with x x₁) =
    cong₂ #with_#handle_ (rename-filling-v ρ h x) (rename-filling-c ρ c x₁)
  rename-filling-c ρ (op ⟨ v ⨟ k ⟩) (opcall x x₁) =
    cong₂ (λ v' k' → op ⟨ v' ⨟ k' ⟩) (rename-filling-v ρ v x) (rename-filling-c (ext ρ) k x₁)
  rename-filling-s ρ σ (sub x) t = rename-filling-v ρ (σ t) x

  subst-comm-exts : ∀ {m n n' Δv Δc u c'}
                 → (σ : Subst m n)
                 → (p : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢ σ ⦂ m)
                 → (λ t → hole-filling-v (exts σ t) (subst-lookup-typed (exts-typed p) t) u (⟨↦⟩≡ Δc u n') c')
                 ≡ exts (hole-filling-subst σ p u (⟨↦⟩≡ Δc u n') c')
  subst-comm-exts σ (sub p) = extensionality λ { F.zero → refl ; (F.suc x₁) → rename-filling-v F.suc (σ x₁) p }

  rename-filling-v-suc2 : ∀ {Δv Δc m m' u c'} {x₁ : Δc u ≡ just m'}
    → (v : Value m)
    → (p : Δv ⨟ Δc ⨟ m ⊢v v)
    → hole-filling-v (renameV F.suc (renameV F.suc v))
        (rename-value-typed F.suc (rename-value-typed F.suc p)) u x₁ c'
    ≡ renameV F.suc (renameV F.suc (hole-filling-v v p u x₁ c'))
  rename-filling-v-suc2 {Δv} {Δc} {m} {m'} {u} {c'} {x₁} v p
    rewrite (sym (rename-filling-v {u = u} {x₁ = x₁} {c' = c'} F.suc v p))
    = rename-filling-v F.suc (renameV F.suc v) (rename-value-typed F.suc p)

  subst-comm-exts2 : ∀ {m n n' Δv Δc u c'}
                 → (σ : Subst m n)
                 → (p : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢ σ ⦂ m)
                 → (λ t → hole-filling-v (exts (exts σ) t) (subst-lookup-typed (exts-typed (exts-typed p)) t) u (⟨↦⟩≡ Δc u n') c')
                 ≡ exts (exts (hole-filling-subst σ p u (⟨↦⟩≡ Δc u n') c'))
  subst-comm-exts2 σ (sub x₁) = extensionality λ { F.zero → refl ; (F.suc F.zero) → refl
                                                   ; (F.suc (F.suc x₂)) → rename-filling-v-suc2 (σ x₂) x₁ }

  -- substitution commutativity
  subst-comm-c-gen : ∀ {n' Δv Δc u c c'} {σ : Subst m n}
                 → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ m ⊢c c)
                 → (p2 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢ σ ⦂ m)
                 → Δv ⨟ Δc ⨟ n' ⊢c c'
                 ----------------------------------------------------------------
                 → hole-filling-c (substC σ c) (subst-comp-gen p1 p2) u (⟨↦⟩≡ Δc u n') c'
                 ≡ substC (hole-filling-subst σ p2 u (⟨↦⟩≡ Δc u n') c') (hole-filling-c c p1 u (⟨↦⟩≡ Δc u n') c')
  subst-comm-v-gen : ∀ {n' Δv Δc u v c'} {σ : Subst m n}
                 → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ m ⊢v v)
                 → (p2 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢ σ ⦂ m)
                 → Δv ⨟ Δc ⨟ n' ⊢c c'
                 ----------------------------------------------------------------
                 → hole-filling-v (substV σ v) (subst-value-gen p1 p2) u (⟨↦⟩≡ Δc u n') c'
                 ≡ substV (hole-filling-subst σ p2 u (⟨↦⟩≡ Δc u n') c') (hole-filling-v v p1 u (⟨↦⟩≡ Δc u n') c')
  subst-comm-s-gen : ∀ {m n n' Δv Δc u c'} {σ : Subst m n}
                 → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢ σ ⦂ m)
                 → (p2 : Δv ⨟ Δc ⨟ n' ⊢c c')
                 → ∀ (t : Fin m)
                 → hole-filling-v (σ t) (subst-lookup-typed p1 t) u (⟨↦⟩≡ Δc u n') c'
                 ≡ (hole-filling-subst σ p1 u (⟨↦⟩≡ Δc u n') c') t
  subst-comm-c-gen {c = #ret x₂} (ret x₃) (sub x₄) x₁ = cong #ret (subst-comm-v-gen x₃ (sub x₄) x₁)
  subst-comm-c-gen {c = x₂ ∙ x₃} (app x₄ x₅) (sub x₆) x₁ = cong₂ _∙_ (subst-comm-v-gen x₄ (sub x₆) x₁) (subst-comm-v-gen x₅ (sub x₆) x₁)
  subst-comm-c-gen {m} {n} {n'} {Δv} {Δc} {u} {c = #let c #in c₁} {c'} {σ} (bind p1 p3) (sub x₂) x₁
    rewrite subst-comm-c-gen {σ = σ} p1 (sub x₂) x₁
    | subst-comm-c-gen {σ = exts σ} p3 (exts-typed (sub x₂)) x₁
    | subst-comm-exts {n' = n'} {c' = c'} σ (sub x₂)
    = refl
  subst-comm-c-gen {m} {n} {n'} {Δv} {Δc} {u} {c = ⦃⁇⦄ i σᵢ} {c'} {σ} (hole-c x₂ (sub {m = m₁} x₃)) (sub x₄) pc' = go (i ≟ u)
    where
      hole-filling-subst-comp :
        ∀ (m≡m₁ : n' ≡ m₁)
          → hole-filling-subst (σ ∘ₛ σᵢ) (sub (λ {t} → subst-value-gen x₃ (sub x₄))) u (⟨↦⟩≡ Δc u n') c'
            ∘ cast m≡m₁
          ≡ (λ t → hole-filling-v (σ t) x₄ u (⟨↦⟩≡ Δc u n') c')
            ∘ₛ (hole-filling-subst σᵢ (sub x₃) u (⟨↦⟩≡ Δc u n') c' ∘ cast m≡m₁)
      hole-filling-subst-comp m≡m₁ = extensionality λ t → subst-comm-v-gen {σ = σ} (x₃ {t = cast m≡m₁ t}) (sub x₄) pc'

      go : (d : Dec (i ≡ u)) → hole-filling-hole i m₁ (σ ∘ₛ σᵢ) x₂
        (λ {t} → subst-value-gen x₃ (sub x₄)) u n' (⟨↦⟩≡ Δc u n') c' d
        ≡ substC (λ t → hole-filling-v (σ t) x₄ u (⟨↦⟩≡ Δc u n') c') (hole-filling-hole i m₁ σᵢ x₂ x₃ u n' (⟨↦⟩≡ Δc u n') c' d)

      go (yes k) = trans (cong (λ σ' → substC σ' c') (hole-filling-subst-comp m≡m₁))
                         (sym (substC-comp (λ t → hole-filling-v (σ t) x₄ u (⟨↦⟩≡ Δc u n') c') σR c'))
        where
          m≡m₁ : n' ≡ m₁
          m≡m₁ = just≡ (trans (sym (⟨↦⟩≡ Δc u n')) (trans (cong (Δc ⟨ u ↦ n' ⟩) (sym k)) x₂))

          σR : Subst n' m
          σR = hole-filling-subst σᵢ (sub x₃) u (⟨↦⟩≡ Δc u n') c' ∘ cast m≡m₁

      go (no k) = cong (⦃⁇⦄ i) (extensionality λ t → subst-comm-v-gen {σ = σ} (x₃ {t}) (sub x₄) pc')
  subst-comm-c-gen {c = #with h #handle c} (#with p1 p2) (sub x₃) x₁ =
    cong₂ #with_#handle_ (subst-comm-v-gen p1 (sub x₃) x₁) (subst-comm-c-gen p2 (sub x₃) x₁)
  subst-comm-c-gen {m} {n} {n'} {Δv} {Δc} {u} {c = op ⟨ v ⨟ k ⟩} {c'} {σ} (opcall p1 p2) (sub pσ) x₁
    rewrite subst-comm-v-gen {σ = σ} p1 (sub pσ) x₁
    | subst-comm-c-gen {σ = exts σ} p2 (exts-typed (sub pσ)) x₁
    | subst-comm-exts {n' = n'} {c' = c'} σ (sub pσ)
    = refl
  subst-comm-v-gen {m} {n} {n'} {Δv} {Δc} {u} {v = ⁇ i σᵢ} {c'} {σ} (hole x₄ (sub {m = m₁} pσᵢ)) (sub pσ) pc' =
    cong (⁇ i) (extensionality λ t → subst-comm-v-gen {σ = σ} (pσᵢ {t}) (sub pσ) pc')
  subst-comm-v-gen {v = ‵ x₂} var (sub x₃) x₁ = refl

  subst-comm-v-gen {m} {n} {n'} {Δv} {Δc} {u} {v = ƛ x₂} {c'} {σ} (abs x₃) p2@(sub p) x₁
    rewrite (subst-comm-c-gen x₃ (exts-typed p2) x₁)
    | subst-comm-exts {n' = n'} {c' = c'} σ (sub p)
    = refl
  subst-comm-v-gen {m} {n} {n'} {Δv} {Δc} {u} {v = #handler⟨ cᵣ ⨟ op , cₒₚ ⟩} {c'} {σ} (hand p1 p2) p3@(sub pσ) x₁
    rewrite subst-comm-c-gen p1 (exts-typed p3) x₁
    | subst-comm-c-gen p2 (exts-typed (exts-typed p3)) x₁
    | subst-comm-exts {n' = n'} {c' = c'} σ (sub pσ)
    | subst-comm-exts2  {n' = n'} {c' = c'} σ (sub pσ)
    = refl
  subst-comm-s-gen (sub x₁) p2 t = refl

  subst-comm-n-c : ∀ {n n' Δv Δc u c v c'}
         → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ suc n ⊢c c)
         → (p2 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢v v)
         → Δv ⨟ Δc ⨟ n' ⊢c c'
                 ----------------------------------------------------------------
         → hole-filling-c (c [ v ]c) (subst-comp p1 p2) u (⟨↦⟩≡ Δc u n') c'
         ≡ (hole-filling-c c p1 u (⟨↦⟩≡ Δc u n') c') [ hole-filling-v v p2 u (⟨↦⟩≡ Δc u n') c' ]c
  subst-comm-n-v : ∀ {n n' Δv Δc u v1 v2 c'}
         → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ suc n ⊢v v1)
         → (p2 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢v v2)
         → Δv ⨟ Δc ⨟ n' ⊢c c'
                 ----------------------------------------------------------------
         → hole-filling-v (v1 [ v2 ]v) (subst-value p1 p2) u (⟨↦⟩≡ Δc u n') c'
         ≡ (hole-filling-v v1 p1 u (⟨↦⟩≡ Δc u n') c') [ hole-filling-v v2 p2 u (⟨↦⟩≡ Δc u n') c' ]v
  subst-comm-n-c {n} {n'} {Δv} {Δc} {u} {c} {v} {c'} p1 p2 x₁ = trans (subst-comm-c-gen p1 (subst-zero-typed p2) x₁)
                        (cong (λ σ → substC σ (hole-filling-c c p1 u (⟨↦⟩≡ Δc u n') c'))
                                                                  (extensionality λ { F.zero → refl ; (F.suc x) → refl }))
  subst-comm-n-v {n} {n'} {Δv} {Δc} {u} {v1} {v2} {c'} p1 p2 x₁ = trans (subst-comm-v-gen p1 (subst-zero-typed p2) x₁)
                      (cong (λ σ → substV σ (hole-filling-v v1 p1 u (⟨↦⟩≡ Δc u n') c'))
                                                                    (extensionality λ { F.zero → refl ; (F.suc x) → refl }))

  subst-comm-c : ∀ {n' Δv Δc u c v c'}
                 → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ 1 ⊢c c)
                 → (p2 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ 0 ⊢v v)
                 → Δv ⨟ Δc ⨟ n' ⊢c c'
                 ----------------------------------------------------------------
                 → hole-filling-c (c [ v ]c) (subst-comp p1 p2) u (⟨↦⟩≡ Δc u n') c'
                 ≡ (hole-filling-c c p1 u (⟨↦⟩≡ Δc u n') c') [ hole-filling-v v p2 u (⟨↦⟩≡ Δc u n') c' ]c
  subst-comm-v : ∀ {n' Δv Δc u v1 v2 c'}
                 → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ 1 ⊢v v1)
                 → (p2 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ 0 ⊢v v2)
                 → Δv ⨟ Δc ⨟ n' ⊢c c'
                 ----------------------------------------------------------------
                 → hole-filling-v (v1 [ v2 ]v) (subst-value p1 p2) u (⟨↦⟩≡ Δc u n') c'
                 ≡ (hole-filling-v v1 p1 u (⟨↦⟩≡ Δc u n') c') [ hole-filling-v v2 p2 u (⟨↦⟩≡ Δc u n') c' ]v
  subst-comm-c p1 p2 x₁ = subst-comm-n-c p1 p2 x₁
  subst-comm-v p1 p2 x₁ = subst-comm-n-v p1 p2 x₁

  β-op-eq-case : ∀ {Δv Δc n n' u} {c' : Computation n'}
            (cᵣ : Computation (suc n)) (cₒₚ : Computation (2+ n)) (v : Value n) (k : Computation (suc n))
            (op : ℕ)
            (x₁ : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ suc n ⊢c cᵣ) (x₂ : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ 2+ n ⊢c cₒₚ)
            (x₃ : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢v v) (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ suc n ⊢c k)
            (p2 : Δv ⨟ Δc ⨟ n' ⊢c c')
            → (hole-filling-c
                  (cₒₚ [ v ⨟
                  ƛ (#with #handler⟨ liftC-ret cᵣ ⨟ op , liftC-op cₒₚ ⟩ #handle k) ]c)
                  (-→-preserve β-op-eq (#with (hand x₁ x₂) (opcall x₃ p1))) u
                  (⟨↦⟩≡ Δc u n') c')
            ≡ (hole-filling-c cₒₚ x₂ u (⟨↦⟩≡ Δc u n') c'
                [ hole-filling-v v x₃ u (⟨↦⟩≡ Δc u n') c'
                ⨟ ƛ (#with #handler⟨ liftC-ret (hole-filling-c cᵣ x₁ u (⟨↦⟩≡ Δc u n') c')
                ⨟ op , liftC-op (hole-filling-c cₒₚ x₂ u (⟨↦⟩≡ Δc u n') c') ⟩ #handle hole-filling-c k p1 u (⟨↦⟩≡ Δc u n') c') ]c)
  β-op-eq-case {Δv} {Δc} {n} {n'} {u} {c'} cᵣ cₒₚ v k op x₁ x₂ x₃ p1 p2 = trans (subst-comm-c-gen x₂ (subst-subst-gen (exts-typed (subst-zero-typed x₃))
                                                                                                                          (subst-zero-typed (contV-typed (hand x₁ x₂) p1))) p2)
          (cong (λ σ →  substC σ (hole-filling-c cₒₚ x₂ u (⟨↦⟩≡ Δc u n') c'))
          (extensionality λ { F.zero → cong₂ (λ x y → ƛ #with #handler⟨ x ⨟ op , y ⟩ #handle hole-filling-c k p1 u (⟨↦⟩≡ Δc u n') c')
                                                      (rename-filling-c (ext F.suc) cᵣ x₁) (rename-filling-c (ext (ext F.suc)) cₒₚ x₂)
                            ; (F.suc F.zero) → case1 ; (F.suc (F.suc x)) → refl}))
    where
      σ = (subst-zero (ƛ (#with #handler⟨ renameC (ext F.suc) cᵣ ⨟ op , renameC (ext (ext F.suc)) cₒₚ ⟩ #handle k)))
      σ-typed = subst-zero-typed (abs (#with (hand (rename-comp-typed (ext F.suc) x₁) (rename-comp-typed (ext (ext F.suc)) x₂)) p1))
      v' : Value (suc n)
      v' = renameV F.suc v
      σv'-typed = (subst-value-gen (rename-value-typed F.suc x₃) (subst-zero-typed (contV-typed (hand x₁ x₂) p1)))
      u-w = ⟨↦⟩≡ Δc u n'

      case1 : hole-filling-v (substV σ v') σv'-typed u u-w c'
        ≡ (subst-zero
         (ƛ
          (#with
           #handler⟨ liftC-ret (hole-filling-c cᵣ x₁ u u-w c') ⨟ op ,
           liftC-op (hole-filling-c cₒₚ x₂ u u-w c') ⟩
           #handle hole-filling-c k p1 u u-w c'))
         ∘ₛ exts (subst-zero (hole-filling-v v x₃ u u-w c')))
        (F.suc F.zero)
      case1 = trans y (cong₂ substV (extensionality (λ { F.zero → cong₂ (λ x y → ƛ #with #handler⟨ x ⨟ op , y ⟩  #handle hole-filling-c k p1 u u-w c')
                                                                    (rename-filling-c (ext F.suc) cᵣ x₁) (rename-filling-c (ext (ext F.suc)) cₒₚ x₂)
                                                   ; (F.suc x) → refl})) (rename-filling-v F.suc v x₃))
        where
          y : hole-filling-v (substV σ v') σv'-typed u u-w c'
               ≡ substV (hole-filling-subst σ σ-typed u u-w c') (hole-filling-v v' (rename-value-typed F.suc x₃) u u-w c')
          y = subst-comm-v-gen {Δv = Δv} {Δc = Δc} {c' = c'} {σ = σ} (rename-value-typed F.suc x₃) σ-typed p2

  mutual
    -→v--→v*-comm-gen : ∀ {n' Δv Δc u v v' c'}
                  → (s : v -→v v')
                  → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢v v)
                  → (p2 : Δv ⨟ Δc ⨟ n' ⊢c c')
                  → hole-filling-v v p1 u (⟨↦⟩≡ Δc u n') c' -→v* hole-filling-v v' (-→v-preserve s p1) u (⟨↦⟩≡ Δc u n') c'
    -→v--→v*-comm-gen (ξ-ƛ s) (abs p1) p2 =
      ξ-ƛ* (-→--→*-comm-gen s p1 p2)
    -→v--→v*-comm-gen (ξ-hand₁ s) (hand p1 p2) p3 =
      ξ-hand₁* (-→--→*-comm-gen s p1 p3)
    -→v--→v*-comm-gen (ξ-hand₂ s) (hand p1 p2) p3 =
      ξ-hand₂* (-→--→*-comm-gen s p2 p3)
    -→v--→v*-comm-gen {n' = n'} {Δv = Δv} {Δc = Δc} {u = u} {c' = c'}
      (ξ-hole-v {m = m} {i = i} {σ = σ} {σ' = σ'} (ξ-σ x s rest)) (hole h (sub p)) p2 =
      hole-v-multistep (-→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2)

    -→s--→s*-comm-gen : ∀ {m n' Δv Δc u σ σ' c'}
                  → (s : σ -→s σ')
                  → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢ σ ⦂ m)
                  → (p2 : Δv ⨟ Δc ⨟ n' ⊢c c')
                  → hole-filling-subst σ p1 u (⟨↦⟩≡ Δc u n') c' -→s* hole-filling-subst σ' (-→s-preserve s p1) u (⟨↦⟩≡ Δc u n') c'
    -→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2 t with t F.≟ x
    ... | yes refl = -→v--→v*-comm-gen s (p {x}) p2
    ... | no neq rewrite sym (rest t neq) = 0 , -→vZ

    -→--→*-comm-gen : ∀ {n' Δv Δc u d₁ d₂ c'}
                  → (s : d₁ -→ d₂)
                  → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢c d₁)
                  → (p2 : Δv ⨟ Δc ⨟ n' ⊢c c')
                  → hole-filling-c d₁ p1 u (⟨↦⟩≡ Δc u n') c' -→* hole-filling-c d₂ (-→-preserve s p1) u (⟨↦⟩≡ Δc u n') c'
    -→--→*-comm-gen β (app (abs p1) p2) p3 rewrite subst-comm-n-c p1 p2 p3 = -→trans-→* β -→*-refl
    -→--→*-comm-gen β-let (bind (ret p1) p2) p3 rewrite subst-comm-n-c p2 p1 p3 = -→trans-→* β-let -→*-refl
    -→--→*-comm-gen {n} {n'} {Δv} {Δc} {u} {#let op ⟨ v ⨟ k ⟩ #in c} {d₂} {c'} op-let (bind (opcall x₁ x₂) x₃) p2
      rewrite rename-filling-c {u = u} {x₁ = (⟨↦⟩≡ Δc u n')} {c' = c'} (ext F.suc) c x₃
      = -→trans-→* op-let -→*-refl
    -→--→*-comm-gen β-ret (#with (hand x₁ x₂) (ret x₃)) p2 rewrite subst-comm-n-c x₁ x₃ p2 = -→trans-→* β-ret -→*-refl
    -→--→*-comm-gen {n} {n'} {Δv} {Δc} {u} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op ⟨ v ⨟ k ⟩} {d₂} {c'} β-op-eq (#with (hand x₁ x₂) (opcall x₃ p1)) p2
      rewrite β-op-eq-case {Δv} {Δc} {n} {n'} {u} {c'} cᵣ cₒₚ v k op x₁ x₂ x₃ p1 p2
      = -→trans-→* β-op-eq -→*-refl
    -→--→*-comm-gen {n} {n'} {Δv} {Δc} {u} {#with #handler⟨ cᵣ ⨟ op , cₒₚ ⟩ #handle op' ⟨ v ⨟ k ⟩} {d₂} {c'}
                    (β-op-neq x₂) (#with (hand x₁ x₃) (opcall x₄ p1)) p2
      rewrite rename-filling-c {u = u} {x₁ = (⟨↦⟩≡ Δc u n')} {c' = c'} (ext F.suc) cᵣ x₁
            | rename-filling-c {u = u} {x₁ = (⟨↦⟩≡ Δc u n')} {c' = c'} (ext (ext F.suc)) cₒₚ x₃
      = -→trans-→* (β-op-neq x₂) -→*-refl
    -→--→*-comm-gen (ξ-ret s) (ret p1) p2 = ξ-ret* (-→v--→v*-comm-gen s p1 p2)
    -→--→*-comm-gen {n' = n'} {Δv = Δv} {Δc = Δc} {u = u} {c' = c'}
      (ξ-hole-c {m = m} {i = i} {σ = σ} {σ' = σ'} (ξ-σ x s rest)) (hole-c h (sub p)) p2 =
      go (i ≟ u) h
      where
        x₁ = ⟨↦⟩≡ Δc u n'
        p' = λ {t} → subst-lookup-typed (-→s-preserve (ξ-σ x s rest) (sub p)) t
        go : (w : Dec (i ≡ u)) (h' : (Δc ⟨ u ↦ n' ⟩) i ≡ just m) →
             hole-filling-hole i m σ h' p u n' x₁ c' w -→*
             hole-filling-hole i m σ' h' p' u n' x₁ c' w
        go (yes refl) h' =
          substC-preserves-→* c' (λ t → -→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2 (cast m≡nσ t))
          where
            m≡nσ : n' ≡ m
            m≡nσ = just≡ (trans (sym x₁) h')
        go (no neq) h' =
          hole-c-multistep (-→s--→s*-comm-gen (ξ-σ x s rest) (sub p) p2)
    -→--→*-comm-gen (ξ-app₁ s) (app p1 p2) p3 = ξ-app₁* (-→v--→v*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-app₂ s) (app p1 p2) p3 = ξ-app₂* (-→v--→v*-comm-gen s p2 p3)
    -→--→*-comm-gen (ξ-let s) (bind p1 p2) p3 = ξ-let* (-→--→*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-in s) (bind p1 p2) p3 = ξ-in* (-→--→*-comm-gen s p2 p3)
    -→--→*-comm-gen (ξ-with₁ s) (#with p1 p2) p3 = ξ-with₁* (-→v--→v*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-with₂ s) (#with p1 p2) p3 = ξ-with₂* (-→--→*-comm-gen s p2 p3)
    -→--→*-comm-gen (ξ-op₁ s) (opcall p1 p2) p3 = ξ-op₁* (-→v--→v*-comm-gen s p1 p3)
    -→--→*-comm-gen (ξ-op₂ s) (opcall p1 p2) p3 = ξ-op₂* (-→--→*-comm-gen s p2 p3)

  -- the main commutativity theorem
  -→*-comm : ∀ {n n' Δv Δc u d₁ d₂ c'}
           → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢c d₁)
           → (p2 : Δv ⨟ Δc ⨟ n' ⊢c c')
           → (s : d₁ -→* d₂)
           → hole-filling-c d₁ p1 u (⟨↦⟩≡ Δc u n') c' -→* hole-filling-c d₂ (-→*-preserve p1 s) u (⟨↦⟩≡ Δc u n') c'
  -→*-comm p1 p2 (fst , -→Z) = 0 , -→Z
  -→*-comm {n} {n'} {Δv} {Δc} {u} {d₁} {d₂} {c'} p1 p2 (suc n'' , (_-→S_ {M = M} s snd))
           = trans-→* (-→--→*-comm-gen s p1 p2) (-→*-comm (-→-preserve s p1) p2 (n'' , snd))

  -- the main fill-and-resume soundness theorem
  resumption : ∀ {n n' Δv Δc u d d₁ d'}
             → (p1 : Δv ⨟ Δc ⟨ u ↦ n' ⟩ ⨟ n ⊢c d)
             → (p2 : Δv ⨟ Δc ⨟ n' ⊢c d')
             → (s : d -→* d₁)
             → ∃[ d₂ ] (hole-filling-c d p1 u (⟨↦⟩≡ Δc u n') d' -→* d₂ × hole-filling-c d₁ (-→*-preserve p1 s) u (⟨↦⟩≡ Δc u n') d' -→* d₂)
  resumption p1 p2 s = confluence -→*-refl (-→*-comm p1 p2 s)  

module Example where
  open Impure
  Ω :  Computation 1
  Ω = (ƛ (# 0 ∙ # 0)) ∙ (ƛ (# 0 ∙ # 0))

  _ : Ω -→ Ω
  _ = β

  s : Subst 0 0
  s ()

  err = 1
  h : Value 0
  h = #handler⟨ #ret (# 0) ⨟ err , #ret (# 1) ⟩   -- err(x, k) -> ret x

  ex : Computation 0
  ex = #with h #handle (#let (⦃⁇⦄ 1 s) #in Ω)

  ⊢ex : (λ z → nothing) ⨟ (λ z → nothing) ⟨ 1 ↦ 0 ⟩ ⨟ 0 ⊢c ex
  ⊢ex = #with (hand (ret var) (ret var)) 
              (bind (hole-c refl (sub λ { {()} })) 
                    (app (abs (app var var)) (abs (app var var))))
  
  _ : ex -→ ex
  _ = ξ-with₂ (ξ-in β)

  d : Computation 0
  d = err ⟨ ƛ #ret (# 0) ⨟ #ret (# 0) ⟩

  f : Computation 0
  f = hole-filling-c ex ⊢ex 1 refl d

  f' : Computation 0
  f' = #with h #handle (#let d #in Ω)

  _ : f ≡ f'
  _ = refl

  l : ∀ t → ex -→* t → t ≡ ex
  l t (zero , -→Z) = refl
  l t (suc fst , (ξ-with₁ (ξ-hand₁ (ξ-ret ())) -→S snd))
  l t (suc fst , (ξ-with₁ (ξ-hand₂ (ξ-ret ())) -→S snd))
  l t (suc fst , (ξ-with₂ (ξ-let (ξ-hole-c (ξ-σ () x₁ x₂))) -→S snd))
  l t (suc fst , (ξ-with₂ (ξ-in β) -→S snd)) = l t (fst , snd)
  l t (suc fst , (ξ-with₂ (ξ-in (ξ-app₁ (ξ-ƛ (ξ-app₁ ())))) -→S snd))
  l t (suc fst , (ξ-with₂ (ξ-in (ξ-app₁ (ξ-ƛ (ξ-app₂ ())))) -→S snd))
  l t (suc fst , (ξ-with₂ (ξ-in (ξ-app₂ (ξ-ƛ (ξ-app₁ ())))) -→S snd)) 
  l t (suc fst , (ξ-with₂ (ξ-in (ξ-app₂ (ξ-ƛ (ξ-app₂ ())))) -→S snd)) 
      
  _ : f -→* #ret (ƛ #ret (# 0))
  _ = form-→* (ξ-with₂ op-let -→S β-op-eq -→S -→Z)

  -- ex -> ex -> ex -> ...
  -- f  -> f  -> f  -> ...
