

open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order
open import Naturals.Properties
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import UF.Univalence
open import UF.Equiv
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base

module Seq (A : 𝓤 ̇ ) where

Seq : 𝓤 ̇
Seq = ℕ → A

Rel : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
Rel 𝓥 = A → A → 𝓥 ̇

-- Definition of Interleaving
Il : 𝓤₀ ̇
Il = ℕ → ℕ × ℕ

-- each new step, one of the sequences is moved forward.
p1 : (f : Il) → 𝓤₀ ̇
p1 f = ∀ n → let (x , y) = f n
            in (f (succ n) ＝ succ x , y) + (f (succ n) ＝ x , (succ y))

-- We have infinite updates from both sequences.
-- In our case, this is a direct condition due to fairness.
-- that two parallel systems will have a fair amount of time to evolve, compute, communicate
-- This is a natural thing to expect.

p2a : (f : Il) → 𝓤₀ ̇
p2a f = ∀ n → Σ nn ꞉ _ , let (nx , ny) = f nn in n ＝ nx


p2b : (f : Il) → 𝓤₀ ̇
p2b f = ∀ n → Σ nn ꞉ _ , let (nx , ny) = f nn in n ＝ ny 


lem-a : (f : Il) → p1 f → p2a f → p2b f → ∀ n
       → let (na2 , _) = f n
             (na1 , _) = f (succ n)
         in na2 ≤ℕ na1
lem-a f c1 c2a c2b n with c1 n
... | inl x = transport (λ z → f n .pr₁ ≤ℕ z) (ap (λ z → pr₁ z) (x ⁻¹)) (≤-succ (f n .pr₁))
... | inr x = transport (λ z → f n .pr₁ ≤ℕ z) (ap (λ z → pr₁ z) (x ⁻¹)) (≤-refl (f n .pr₁))

lem-a2' : (f : Il) → p1 f → p2a f → p2b f → ∀ n1 n2 k
       → n2 ＝ k +' n1
       → let (na2 , _) = f n2
             (na1 , _) = f n1
         in na1 ≤ℕ na2
lem-a2' f c1 c2a c2b n1 n2 zero eq with eq ∙ zero-left-neutral n1
... | refl = ≤-refl (f n1 .pr₁)
lem-a2' f c1 c2a c2b n1 zero (succ k) eq = 𝟘-elim (positive-not-zero (k +' n1) (succ-left k n1 ⁻¹ ∙ eq ⁻¹))
lem-a2' f c1 c2a c2b n1 (succ n2) (succ k) eq with lem-a2' f c1 c2a c2b n1 n2 k (succ-lc (eq ∙ succ-left k n1))
... | r = ≤-trans ( f n1 .pr₁) (f n2 .pr₁) (f (succ n2) .pr₁) r (lem-a f  c1 c2a c2b n2)

lem-a2 : (f : Il) → p1 f → p2a f → p2b f → ∀ n1 n2
       → n1 ≤ℕ n2
       → let (na2 , _) = f n2
             (na1 , _) = f n1
         in na1 ≤ℕ na2
lem-a2  f c1 c2a c2b n1 n2 rel = let (k , eq) = subtraction n1 n2 rel in lem-a2' f c1 c2a c2b n1 n2 k (eq ⁻¹)


lem-b : (f : Il) → p1 f → p2a f → p2b f → ∀ n
       → let (_ , na2) = f n
             (_ , na1) = f (succ n)
         in na2 ≤ℕ na1
lem-b f c1 c2a c2b n with c1 n
... | inr x = transport (λ z → f n .pr₂ ≤ℕ z) (ap (λ z → pr₂ z) (x ⁻¹)) (≤-succ (f n .pr₂))
... | inl x = transport (λ z → f n .pr₂ ≤ℕ z) (ap (λ z → pr₂ z) (x ⁻¹)) (≤-refl (f n .pr₂))

lem-b2' : (f : Il) → p1 f → p2a f → p2b f → ∀ n1 n2 k
       → n2 ＝ k +' n1
       → let (_ , na2) = f n2
             (_ , na1) = f n1
         in na1 ≤ℕ na2
lem-b2' f c1 c2a c2b n1 n2 zero eq with eq ∙ zero-left-neutral n1
... | refl = ≤-refl (f n1 .pr₂)
lem-b2' f c1 c2a c2b n1 zero (succ k) eq = 𝟘-elim (positive-not-zero (k +' n1) (succ-left k n1 ⁻¹ ∙ eq ⁻¹))
lem-b2' f c1 c2a c2b n1 (succ n2) (succ k) eq with lem-b2' f c1 c2a c2b n1 n2 k (succ-lc (eq ∙ succ-left k n1))
... | r = ≤-trans ( f n1 .pr₂) (f n2 .pr₂) (f (succ n2) .pr₂) r (lem-b f  c1 c2a c2b n2)

lem-b2 : (f : Il) → p1 f → p2a f → p2b f → ∀ n1 n2
       → n1 ≤ℕ n2
       → let (_ , na2) = f n2
             (_ , na1) = f n1
         in na1 ≤ℕ na2
lem-b2  f c1 c2a c2b n1 n2 rel = let (k , eq) = subtraction n1 n2 rel in lem-b2' f c1 c2a c2b n1 n2 k (eq ⁻¹)



lem0a : (f : Il) → p1 f → p2a f → p2b f → ∀ n1 n2
       → let (na1 , _) = f n1
             (na2 , _) = f n2
         in succ na1 ≤ℕ na2 → succ n1 ≤ℕ n2
lem0a f c1 c2a c2b n1 n2 rel with order-split n1 n2
... | inl x = x
... | inr x = 𝟘-elim (bigger-or-equal-not-less (f n2 .pr₁) (f n1 .pr₁) l1 rel) where
 l1 = lem-a2 f c1 c2a c2b n2 n1 x

lem0b : (f : Il) → p1 f → p2a f → p2b f → ∀ n1 n2
       → let (_ , na1) = f n1
             (_ , na2) = f n2
         in succ na1 ≤ℕ na2 → succ n1 ≤ℕ n2
lem0b f c1 c2a c2b n1 n2 rel with order-split n1 n2
... | inl x = x
... | inr x = 𝟘-elim (bigger-or-equal-not-less (f n2 .pr₂) (f n1 .pr₂) l1 rel) where
 l1 = lem-b2 f c1 c2a c2b n2 n1 x


lem1 : (f : Il) → p1 f → p2a f → p2b f → ∀ na nb
      → Σ n ꞉ _ , let (nx , ny) = f n in ((nx ＝ na) × (nb ≤ℕ ny)) + (ny ＝ nb) × (na ≤ℕ nx)
lem1 f c1 c2a c2b na nb with c2a na | c2b nb
... | (fna , eqa) | (fnb , eqb) with order-split fna fnb
... | inl x = let q = lem-a2 f c1 c2a c2b fna fnb (<-coarser-than-≤ fna fnb x)
              in fnb , (inr ((eqb ⁻¹) , transport (λ z → z ≤ℕ f fnb .pr₁) (eqa ⁻¹) q))
... | inr x = let q = lem-b2 f c1 c2a c2b fnb fna x
              in fna , (inl ((eqa ⁻¹) , transport (λ z → z ≤ℕ f fna .pr₂) (eqb ⁻¹) q))

module _ (R : Rel 𝓥) where

 Inf-C : (Sa Sb : Seq) → 𝓥 ̇
 Inf-C Sa Sb = ∀ (f : Il) → p1 f → p2a f → p2b f → ∀ n → Σ nn ꞉ _ , n ≤ℕ nn × let (na , nb) = f nn in R (Sa na) (Sb nb)


 T : (Sa Sb : Seq) → ∀ na → ∀ nb → 𝓥 ̇
 T Sa Sb na nb = (∀ n → na ≤ℕ n → R (Sa n) (Sb nb)) × (∀ n → nb ≤ℕ n → R (Sa na) (Sb n))

-- With this theorem, we remove the interleaving condition.
-- Because we force all interleaving conditions to have an infinite number of
-- R aₙ bₙ 

 seq-cond : (Sa Sb : Seq) → (∀ n → Σ na ꞉ _ , Σ nb ꞉ _ , (n ≤ℕ na) × (n ≤ℕ nb) × T Sa Sb na nb)
      → Inf-C Sa Sb
 seq-cond Sa Sb c f c1 c2a c2b n = r d where
  fna = f n .pr₁
  fnb = f n .pr₂
  l1 = c (succ (max fna fnb))
  na = l1 .pr₁
  nb = l1 .pr₂ .pr₁
  max≤na = l1 .pr₂ .pr₂ .pr₁
  max≤nb = l1 .pr₂ .pr₂ .pr₂ .pr₁
  t = l1 .pr₂ .pr₂ .pr₂ .pr₂
  d = lem1 f c1 c2a c2b na nb
  r : (Σ n ꞉ _ , let (nx , ny) = f n in ((nx ＝ na) × (nb ≤ℕ ny)) + (ny ＝ nb) × (na ≤ℕ nx))
      → _
  r (n' , inl x) = n' , <-coarser-than-≤ n n' (lem0b f c1 c2a c2b n n' l2) , transport (λ z → R (Sa z) (Sb (f n' .pr₂))) (x .pr₁ ⁻¹) (t .pr₂ (f n' .pr₂) (x .pr₂)) where
   l2 : succ (f n .pr₂) ≤ℕ f n' .pr₂
   l2 = ≤-trans (succ (f n .pr₂)) nb (f n' .pr₂) (≤-trans (succ (f n .pr₂)) (succ (max fna fnb)) nb (max-≤-upper-bound' fnb fna) max≤nb) (x .pr₂)
  r (n' , inr x) = n' , <-coarser-than-≤ n n' (lem0a f c1 c2a c2b n n' l3) , transport (λ z → R (Sa (f n' .pr₁)) (Sb z)) (x .pr₁ ⁻¹) (t .pr₁ (f n' .pr₁) (x .pr₂)) where
   l3 : succ (f n .pr₁) ≤ℕ f n' .pr₁
   l3 = ≤-trans (succ (f n .pr₁)) na (f n' .pr₁) (≤-trans (succ (f n .pr₁)) (succ (max fna fnb)) na (max-≤-upper-bound fna fnb) max≤na) (x .pr₂)
