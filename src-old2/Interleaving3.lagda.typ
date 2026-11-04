
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Interleaving
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan renaming (_+_ to _＋_)
open import Naturals.Addition
open import UF.FunExt
open import UF.Base
open import UF.Subsingletons
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties
open import MLTT.Two-Properties


```
*/

```agda

open import PredP
open ΣPred

module Interleaving3 where

Fin : (n : ℕ) → 𝓤₀ ̇
Fin n = Σ x ꞉ ℕ , x ≤ n

irₙ' : (n x : ℕ) → is-prop (x ≤ n)
irₙ' n x = ≤-is-prop-valued x n

irₙ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{n} → (x y : Fin n)
      → (f : Fin n → A) → < x > ＝ < y > → f x ＝ f y
irₙ {n = n} x y f eq = ap f (to-subtype-＝ (irₙ' n) eq)

succₙ : ∀{n} → Fin n → Fin (succ n)
succₙ {n} (r , rl) = succ r , rl

zeroₙ : ∀{n} → Fin n
zeroₙ {n} = 0 , ⋆

last : ∀{n} → Fin n
last {n} = n , ≤-refl n

idₙ : ∀{n} → Fin n → Fin (succ n)
idₙ {n} (r , rl) = r , <-coarser-than-≤ r (succ n) rl

λsuccₙ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{n} → (Fin (succ n) → A) → (Fin n → A)
λsuccₙ f r = f (succₙ r)

λidₙ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{n} → (Fin (succ n) → A) → (Fin n → A)
λidₙ {n = n} f r = f (idₙ r)

_+ᶠ_ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{n k} → (Fin n → A) → (Fin k → A) → Fin (n + (succ k)) → A
_+ᶠ_ {A = A} {n} {k} f1 f2 (zero , rl) = f2 (0 , ⋆)
_+ᶠ_ {A = A} {n} {zero} f1 f2 (succ r , rl) = f1 (r , rl)
_+ᶠ_ {A = A} {n} {succ k} f1 f2 (succ r , rl) = (f1 +ᶠ λsuccₙ f2) (r , rl)

Left-Succₙ : ∀{n} → (Fin (succ n) → ℕ × ℕ) → Fin n → 𝓤₀ ̇
Left-Succₙ f r = let (a , b) = f (idₙ r) in f (succₙ r) ＝ succ a , b 

Right-Succₙ : ∀{n} → (Fin (succ n) → ℕ × ℕ) → Fin n → 𝓤₀ ̇
Right-Succₙ f r = let (a , b) = f (idₙ r) in f (succₙ r) ＝ a , succ b 

Inc-Succₙ' : ∀{n} → (f : Fin (succ n) → ℕ) → 𝓤₀ ̇
Inc-Succₙ' {n} f = (x : Fin n) → f (idₙ x) ≤ f (succₙ x)

Inc-Succₙ : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → 𝓤₀ ̇
Inc-Succₙ f = Inc-Succₙ' (pr₁ ∘ f) × Inc-Succₙ' (pr₂ ∘ f)

Increasingₙ' : ∀{n} → (f : Fin (succ n) → ℕ) → 𝓤₀ ̇
Increasingₙ' f = ∀ x y → < x > ≤ < y > → f x ≤ f y

Increasingₙ : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → 𝓤₀ ̇
Increasingₙ f = Increasingₙ' (pr₁ ∘ f) × Increasingₙ' (pr₂ ∘ f)

Zero-Startₙ : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → 𝓤₀ ̇
Zero-Startₙ f = f zeroₙ ＝ 0 , 0

Cₙ : ∀{n} → (Fin (succ n) → ℕ × ℕ) → 𝓤₀ ̇
Cₙ f = (∀ n → Left-Succₙ f n ＋ Right-Succₙ f n) × Zero-Startₙ f

λidCₙ : ∀{n} → ∀ f → Cₙ {succ n} f → Cₙ (λidₙ f)
λidCₙ {n} f (LR , Z) .pr₁ k = LR (idₙ k)
λidCₙ {n} f c .pr₂ = c .pr₂


BFun : (n : ℕ) → ℕ → ℕ → 𝓤₀ ̇
BFun n l r = Σ f ꞉ (Fin n → ℕ × ℕ) , f (n , ≤-refl n) ＝ (l , r)


Left-Succ : (ℕ → ℕ × ℕ) → ℕ → 𝓤₀ ̇
Left-Succ f n = let (a , b) = f n in (f (succ n) ＝ succ a , b)

Right-Succ : (ℕ → ℕ × ℕ) → ℕ → 𝓤₀ ̇
Right-Succ f n = let (a , b) = f n in (f (succ n) ＝ a , succ b)

Left-Cover : (ℕ → ℕ × ℕ) → 𝓤₀ ̇
Left-Cover f = ∀ n → (Σ k ꞉ ℕ , f k .pr₁ ＝ n)

Right-Cover : (ℕ → ℕ × ℕ) → 𝓤₀ ̇
Right-Cover f = ∀ n → (Σ k ꞉ ℕ , f k .pr₂ ＝ n)

C : (ℕ → ℕ × ℕ) → 𝓤₀ ̇
C f = (∀ n → Left-Succ f n ＋ Right-Succ f n)
      × Left-Cover f × Right-Cover f


Inc-Succ' : (f : ℕ → ℕ) → 𝓤₀ ̇
Inc-Succ' f = ∀ x → f x ≤ f (succ x)

Inc-Succ : (f : ℕ → ℕ × ℕ) → 𝓤₀ ̇
Inc-Succ f = Inc-Succ' (pr₁ ∘ f) × Inc-Succ' (pr₂ ∘ f)

Increasing' : (f : ℕ → ℕ) → 𝓤₀ ̇
Increasing' f = ∀ x y → x ≤ y → f x ≤ f y

Increasing : (f : ℕ → ℕ × ℕ) → 𝓤₀ ̇
Increasing f = Increasing' (pr₁ ∘ f) × Increasing' (pr₂ ∘ f)



Zero-Start : (ℕ → ℕ × ℕ) → 𝓤₀ ̇
Zero-Start f = f 0 ＝ 0 , 0


---------------------------------

inc-succₙ :  ∀{n} → ∀ f → Cₙ {n} f → Inc-Succₙ f
inc-succₙ f (LR , Z) .pr₁ x = l (LR x) where
 l : Left-Succₙ f x ＋ Right-Succₙ f x → _
 l (inl eq) = transport (λ z → pr₁ (f (idₙ x)) ≤ℕ z .pr₁) (eq ⁻¹) (≤-succ (f (idₙ x) .pr₁))
 l (inr eq) = transport (λ z → pr₁ (f (idₙ x)) ≤ℕ z .pr₁) (eq ⁻¹) (≤-refl (f (idₙ x) .pr₁))
inc-succₙ f (LR , _) .pr₂ x = l (LR x) where
 l : Left-Succₙ f x ＋ Right-Succₙ f x → _
 l (inl eq) = transport (λ z → pr₂ (f (idₙ x)) ≤ℕ z .pr₂) (eq ⁻¹) (≤-refl (f (idₙ x) .pr₂))
 l (inr eq) = transport (λ z → pr₂ (f (idₙ x)) ≤ℕ z .pr₂) (eq ⁻¹) (≤-succ (f (idₙ x) .pr₂))

increasingₙ : ∀ {n} → ∀ f → Cₙ {n} f → Increasingₙ f
increasingₙ {n} f c .pr₁ x y rl
 = let (e1 , e2) = subtraction < x > < y > rl
   in l1 x y e1 e2 where
  l1 : ∀ x y k → k + < x > ＝ < y > → let (ax , bx) = f x
                                         (ay , by) = f y
                                      in (ax ≤ ay)
  l1 x y zero eq = transport (λ z → f x .pr₁ ≤ f z .pr₁) (irₙ x y (λ x → x) (zero-left-neutral < x > ⁻¹ ∙ eq) ) (≤-refl (f x .pr₁))
  l1 x y (succ k) eq = l4 where
   k+x≤n = transport (λ z → z ≤ succ n) ((succ-left k < x > ⁻¹ ∙ eq) ⁻¹) (y .pr₂)
   k+x = ((k + < x >) , ≤-trans (k + < x >) (succ (k + < x >)) (succ n) (≤-succ (k + < x >))k+x≤n)
   l2 = l1 x k+x k refl
   l3 = ≤-trans (f x .pr₁) (f k+x .pr₁) _ l2 (inc-succₙ f c .pr₁ (k + < x > , k+x≤n))
   l4 = transport (λ z → f x .pr₁ ≤ℕ f z .pr₁) (irₙ (succₙ (k + x .pr₁ , k+x≤n)) y (λ z → z) ((succ-left k < x > ⁻¹ ∙ eq))) l3
increasingₙ {n} f c .pr₂ x y rl
 = let (e1 , e2) = subtraction < x > < y > rl
   in l1 x y e1 e2 where
  l1 : ∀ x y k → k + < x > ＝ < y > → let (ax , bx) = f x
                                         (ay , by) = f y
                                      in (bx ≤ by)
  l1 x y zero eq = transport (λ z → f x .pr₂ ≤ f z .pr₂) (irₙ x y (λ x → x) (zero-left-neutral < x > ⁻¹ ∙ eq) ) (≤-refl (f x .pr₂))
  l1 x y (succ k) eq = l4 where
   k+x≤n = transport (λ z → z ≤ succ n) ((succ-left k < x > ⁻¹ ∙ eq) ⁻¹) (y .pr₂)
   k+x = ((k + < x >) , ≤-trans (k + < x >) (succ (k + < x >)) (succ n) (≤-succ (k + < x >))k+x≤n)
   l2 = l1 x k+x k refl
   l3 = ≤-trans (f x .pr₂) (f k+x .pr₂) _ l2 (inc-succₙ f c .pr₂ (k + < x > , k+x≤n))
   l4 = transport (λ z → f x .pr₂ ≤ℕ f z .pr₂) (irₙ (succₙ (k + x .pr₁ , k+x≤n)) y (λ z → z) ((succ-left k < x > ⁻¹ ∙ eq))) l3


nextₙ'-l : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → (m : Fin n)
         → ∀ k → < m > + k ＝ n →
          (Σ k ꞉ (Fin n) , (f (idₙ m) .pr₁ ＝ f (idₙ k) .pr₁) × (f (succₙ k) .pr₁ ＝ succ (f (idₙ m) .pr₁))) ＋ (f last .pr₁ ＝ f (idₙ m) .pr₁)
nextₙ'-l {n} f c@(RL , Z) m zero eq = l11 (RL m) where
   l11 : Left-Succₙ f m ＋ Right-Succₙ f m → _
   l11 (inl x) = inl ( m , refl ,  (from-×-＝' x) .pr₁ )
   l11 (inr x) = inr (irₙ {n = succ n} last (succₙ m) (λ z → f z .pr₁) ((ap succ eq) ⁻¹) ∙ (from-×-＝' x) .pr₁)
nextₙ'-l {succ n} f c@(RL , Z) m (succ k) eq = l2 l1 where
 l1 = nextₙ'-l {n} (λidₙ f) (λidCₙ f c) (< m > , cosubtraction < m > n (k , (addition-commutativity k (< m >) ∙ succ-lc eq))) k (succ-lc eq)
 l2 : _ → _
 l2 (inl (k , eq1 , eq2)) = inl (idₙ k , (irₙ (idₙ m) (idₙ (< m > , _)) (λ z → f z .pr₁) refl ∙ eq1) , (eq2 ∙ irₙ (idₙ (< m > , _)) (idₙ m) (λ z → succ (f z .pr₁)) refl))
 l2 (inr x) = l21 (RL last) where
  l21 : Left-Succₙ f last ＋ Right-Succₙ f last → _
  l21 (inl y) = inl (last , l22 , ( ap pr₁ y ∙ (ap succ l22 ⁻¹))) where
   l22 = (irₙ (idₙ m) (idₙ (idₙ ((< m > , _)))) (λ z → f z .pr₁) refl ∙ x ⁻¹)
  l21 (inr y) = inr ((ap pr₁ y) ∙ (x ∙ irₙ (idₙ (idₙ (< m > , _))) (idₙ m) (λ z → f z .pr₁) refl))


nextₙ-l : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → (m : Fin n)
        → (Σ k ꞉ (Fin n) , (f (idₙ m) .pr₁ ＝ f (idₙ k) .pr₁) × (f (succₙ k) .pr₁ ＝ succ (f (idₙ m) .pr₁))) ＋ (f last .pr₁ ＝ f (idₙ m) .pr₁)
nextₙ-l {n} f c@(RL , Z) m
 = nextₙ'-l f c m k eq where
  l = subtraction < m > n (m .pr₂)
  k = l .pr₁
  eq = addition-commutativity (< m >) k ∙ l .pr₂

nextₙ'-r : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → (m : Fin n)
         → ∀ k → < m > + k ＝ n →
          (Σ k ꞉ (Fin n) , (f (idₙ m) .pr₂ ＝ f (idₙ k) .pr₂) × (f (succₙ k) .pr₂ ＝ succ (f (idₙ m) .pr₂))) ＋ (f last .pr₂ ＝ f (idₙ m) .pr₂)
nextₙ'-r {n} f c@(RL , Z) m zero eq = l11 (RL m) where
   l11 : Left-Succₙ f m ＋ Right-Succₙ f m → _
   l11 (inr x) = inl ( m , refl ,  (from-×-＝' x) .pr₂ )
   l11 (inl x) = inr (irₙ {n = succ n} last (succₙ m) (λ z → f z .pr₂) ((ap succ eq) ⁻¹) ∙ (from-×-＝' x) .pr₂)
nextₙ'-r {succ n} f c@(RL , Z) m (succ k) eq = l2 l1 where
 l1 = nextₙ'-r {n} (λidₙ f) (λidCₙ f c) (< m > , cosubtraction < m > n (k , (addition-commutativity k (< m >) ∙ succ-lc eq))) k (succ-lc eq)
 l2 : _ → _
 l2 (inl (k , eq1 , eq2)) = inl (idₙ k , (irₙ (idₙ m) (idₙ (< m > , _)) (λ z → f z .pr₂) refl ∙ eq1) , (eq2 ∙ irₙ (idₙ (< m > , _)) (idₙ m) (λ z → succ (f z .pr₂)) refl))
 l2 (inr x) = l21 (RL last) where
  l21 : Left-Succₙ f last ＋ Right-Succₙ f last → _
  l21 (inr y) = inl (last , l22 , ( ap pr₂ y ∙ (ap succ l22 ⁻¹))) where
   l22 = (irₙ (idₙ m) (idₙ (idₙ ((< m > , _)))) (λ z → f z .pr₂) refl ∙ x ⁻¹)
  l21 (inl y) = inr ((ap pr₂ y) ∙ (x ∙ irₙ (idₙ (idₙ (< m > , _))) (idₙ m) (λ z → f z .pr₂) refl))

nextₙ-r : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → (m : Fin n)
        → (Σ k ꞉ (Fin n) , (f (idₙ m) .pr₂ ＝ f (idₙ k) .pr₂) × (f (succₙ k) .pr₂ ＝ succ (f (idₙ m) .pr₂))) ＋ (f last .pr₂ ＝ f (idₙ m) .pr₂)
nextₙ-r {n} f c@(RL , Z) m
 = nextₙ'-r f c m k eq where
  l = subtraction < m > n (m .pr₂)
  k = l .pr₁
  eq = addition-commutativity (< m >) k ∙ l .pr₂

aa2 : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → (m : Fin n)
     → (k : Fin n) → (f (succₙ k) .pr₂ ＝ succ (f (idₙ m) .pr₂)) → < m > ≤ < k >
aa2 f c@(RL , Z) m k eq with (≤-decidable < m > < k >)
... | inl x = x
... | inr x = let t = not-less-or-equal-is-bigger < m > < k > x
                  v = increasingₙ f c .pr₂ (succₙ k) (idₙ m) t
                  e = transport (λ z → z ≤ f (idₙ m) .pr₂) eq v
              in 𝟘-elim (not-less-than-itself (f (idₙ m) .pr₂) e)

aa1 : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → (m : Fin n)
     → (k : Fin n) → (f (succₙ k) .pr₁ ＝ succ (f (idₙ m) .pr₁)) → < m > ≤ < k >
aa1 f c@(RL , Z) m k eq with (≤-decidable < m > < k >)
... | inl x = x
... | inr x = let t = not-less-or-equal-is-bigger < m > < k > x
                  v = increasingₙ f c .pr₁ (succₙ k) (idₙ m) t
                  e = transport (λ z → z ≤ f (idₙ m) .pr₁) eq v
              in 𝟘-elim (not-less-than-itself (f (idₙ m) .pr₁) e)


ss : ∀ n → pred n ≤ n
ss zero = ⋆
ss (succ n) = ≤-succ n


next-stepₙ : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → Fin n → 𝟚 × Fin n × (Fin n ＋ 𝟙 {𝓤₀})
next-stepₙ {n} f c@(RL , Z) m = l1 (nextₙ-l f c m) (nextₙ-r f c m) where
 l1 :    ((Σ k ꞉ (Fin n) , (f (idₙ m) .pr₁ ＝ f (idₙ k) .pr₁) × (f (succₙ k) .pr₁ ＝ succ (f (idₙ m) .pr₁))) ＋ (f last .pr₁ ＝ f (idₙ m) .pr₁))
       → ((Σ k ꞉ (Fin n) , (f (idₙ m) .pr₂ ＝ f (idₙ k) .pr₂) × (f (succₙ k) .pr₂ ＝ succ (f (idₙ m) .pr₂))) ＋ (f last .pr₂ ＝ f (idₙ m) .pr₂))
       → _
 l1 (inl x) (inl y) = l13 (≤-decidable < x .pr₁ > < y .pr₁ >) where
  l13 : is-decidable _ → _
  l13 (inl _) = ₁ , (pred (l15 .pr₁) , ≤-trans (pred (l15 .pr₁)) (l15 .pr₁) n (ss (l15 .pr₁)) (≤-trans (l15 .pr₁) < y .pr₁ > n (cosubtraction (l15 .pr₁) < y .pr₁ > ((< m > , (addition-commutativity < m > (l15 .pr₁) ∙ l15 .pr₂)))) (y .pr₁ .pr₂))) , inl (y .pr₁) where
   l14 = aa2 f c m (y .pr₁) (y .pr₂ .pr₂)
   l15 = subtraction < m > < y .pr₁ > l14
  l13 (inr _) = ₀ , (pred (l17 .pr₁) , ≤-trans (pred (l17 .pr₁)) (l17 .pr₁) n (ss (l17 .pr₁)) (≤-trans (l17 .pr₁) < x .pr₁ > n (cosubtraction (l17 .pr₁) < x .pr₁ > ((< m > , (addition-commutativity < m > (l17 .pr₁) ∙ l17 .pr₂)))) (x .pr₁ .pr₂))) , inl (x .pr₁) where
   l16 = aa1 f c m (x .pr₁) (x .pr₂ .pr₂)
   l17 = subtraction < m > < x .pr₁ > l16
 l1 (inl x) (inr y) = ₁ , (l12 .pr₁ , cosubtraction (l12 .pr₁) n (< m > , (addition-commutativity < m > (l12 .pr₁) ∙ l12 .pr₂))) , inr ⋆ where
  l12 = subtraction < m > n (m .pr₂)
 l1 (inr x) y = ₀ , (l12 .pr₁ , cosubtraction (l12 .pr₁) n (< m > , (addition-commutativity < m > (l12 .pr₁) ∙ l12 .pr₂))) , inr ⋆ where
  l12 = subtraction < m > n (m .pr₂)


to-step-fₙ : ∀{n} → (f : Fin (succ n) → ℕ × ℕ) → Cₙ f → Σ k ꞉ Fin n , ((Fin < k > → ℕ) × 𝟚)
to-step-fₙ {n} f c@(RL , Z) =  l1 n (≤-refl n) .pr₁  where
 l1 : (x : ℕ) → x ≤ n → (Σ k ꞉ Fin x , ((Fin < k > → ℕ) × 𝟚)) × (Fin n ＋ 𝟙 {𝓤₀})
 l1 zero rl =
  let (two , r , next) = next-stepₙ f c zeroₙ
  in (zeroₙ , (λ z → < r >) , two) , next
 l1 (succ x) rl
  = let ((k , (g , two)) , next) = l1 x (<-coarser-than-≤ x n rl)
    in l2 k g two next where
   l2 : (k : Fin x)  → (Fin < k > → ℕ) → 𝟚 → Fin n ＋ 𝟙 {𝓤₀} → _
   l2 k g two (inl x) =
    let (_ , r , nnext) = next-stepₙ f c x
    in ((succ < k > , k .pr₂) , (transport (λ z → Fin (succ z) → ℕ) (zero-left-neutral (k .pr₁)) ((λ z → < r >) +ᶠ g) , two)) , nnext
   l2 k g two next@(inr _) =  (( (< k > , ≤-trans < k > x (succ x) (k .pr₂) (≤-succ x)) , (g , two)) , next)

-----------------------------------------------------------------------

zero-Start : ∀ f → C f → Zero-Start f
zero-Start f (a , b , c) = to-×-＝ (l2 (l1 .pr₁) (l1 .pr₂)) ((g2 (g1 .pr₁) (g1 .pr₂))) where
 l1 = b 0
 l2 : ∀ k → f k .pr₁ ＝ 0 → f 0 .pr₁ ＝ 0
 l2 zero x = x
 l2 (succ k) x = l2 k (l4 l3) where
  l3 = a k
  l4 : (f (succ k) ＝ succ (f k .pr₁) , f k .pr₂) ＋
      (f (succ k) ＝ f k .pr₁ , succ (f k .pr₂)) → f k .pr₁ ＝ 0
  l4 (inl y) = 𝟘-elim (positive-not-zero (f k .pr₁) ((x ⁻¹ ∙ ap pr₁ y) ⁻¹))
  l4 (inr y) = ap pr₁ y ⁻¹ ∙ x
 g1 = c 0
 g2 : ∀ k → f k .pr₂ ＝ 0 → f 0 .pr₂ ＝ 0
 g2 zero x = x
 g2 (succ k) x = g2 k (g4 g3) where
  g3 = a k
  g4 : (f (succ k) ＝ succ (f k .pr₁) , f k .pr₂) ＋
      (f (succ k) ＝ f k .pr₁ , succ (f k .pr₂)) → f k .pr₂ ＝ 0
  g4 (inr y) = 𝟘-elim (positive-not-zero (f k .pr₂) ((x ⁻¹ ∙ ap pr₂ y) ⁻¹))
  g4 (inl y) = ap pr₂ y ⁻¹ ∙ x

inc-succ :  ∀ f → C f → Inc-Succ f
inc-succ f c@(S , LC , RC) .pr₁ x = l2 (S x) where
 l2 : Left-Succ f x ＋ Right-Succ f x → _
 l2 (inl eq) = transport (λ z → f x .pr₁ ≤ℕ z .pr₁) (eq ⁻¹) (≤-succ (f x .pr₁))
 l2 (inr eq) = transport (λ z → f x .pr₁ ≤ℕ z .pr₁) (eq ⁻¹) (≤-refl (f x .pr₁))
inc-succ f c@(S , LC , RC) .pr₂ x = l2 (S x) where
 l2 : Left-Succ f x ＋ Right-Succ f x → _
 l2 (inl eq) = transport (λ z → f x .pr₂ ≤ℕ z .pr₂) (eq ⁻¹) (≤-refl (f x .pr₂))
 l2 (inr eq) = transport (λ z → f x .pr₂ ≤ℕ z .pr₂) (eq ⁻¹) (≤-succ (f x .pr₂))


increasing : ∀ f → C f → Increasing f
increasing f c@(S , LC , RC) .pr₁ x y rl
 = let (e1 , e2) = (subtraction x y rl)
   in l1 x y e1 e2 where
  l1 : ∀ x y →  ∀ k → k + x ＝ y → let (ax , bx) = f x
                                      (ay , by) = f y
                                   in (ax ≤ ay)
  l1 x y zero eq
   = transport (λ z → (f z .pr₁ ≤ℕ f y .pr₁))
               (eq ⁻¹ ∙ zero-left-neutral x)
               (≤-refl (f y .pr₁))
  l1 x y (succ k) eq = l5 where
   l2 = l1 x (k + x) k refl
   l3 = ≤-trans (f x .pr₁) (f (k + x) .pr₁) (f (succ (k + x)) .pr₁) l2 (inc-succ f c .pr₁ (k + x))
   l5 = transport (λ z → f x .pr₁ ≤ℕ f z .pr₁) (succ-left k x ⁻¹ ∙ eq) l3
increasing f c@(S , LC , RC) .pr₂ x y rl
  = let (e1 , e2) = (subtraction x y rl)
   in l1 x y e1 e2 where
    l1 : ∀ x y →  ∀ k → k + x ＝ y → let (ax , bx) = f x
                                        (ay , by) = f y
                                    in (bx ≤ by)
    l1 x y zero eq
     = transport (λ z → (f z .pr₂ ≤ℕ f y .pr₂))
                 (eq ⁻¹ ∙ zero-left-neutral x)
                 (≤-refl (f y .pr₂))
    l1 x y (succ k) eq = l5 where
     l2 = l1 x (k + x) k refl
     l4 = ≤-trans (f x .pr₂) (f (k + x) .pr₂) (f (succ (k + x)) .pr₂) l2 (inc-succ f c .pr₂ (k + x))
     l5 = transport (λ z → f x .pr₂ ≤ℕ f z .pr₂) (succ-left k x ⁻¹ ∙ eq) l4


const-interval₂ : (f : ℕ → ℕ × ℕ) → Increasing f → ∀ n → ∀ k → f n .pr₂ ＝ f (n + k) .pr₂ → ∀ l → l ≤ k → f n .pr₂ ＝ f (n + l) .pr₂
const-interval₂ f inc n k eq l rl = ≤-anti (f n .pr₂) (f (n + l) .pr₂) (inc .pr₂ n (n + l) (≤-+ n l)) (transport (λ z → f (n + l) .pr₂ ≤ℕ z) (eq ⁻¹) (inc .pr₂ (n + l) (n + k) (≤-n-monotone-left l k n rl)))

const-interval₁ : (f : ℕ → ℕ × ℕ) → Increasing f → ∀ n → ∀ k → f n .pr₁ ＝ f (n + k) .pr₁ → ∀ l → l ≤ k → f n .pr₁ ＝ f (n + l) .pr₁
const-interval₁ f inc n k eq l rl = ≤-anti (f n .pr₁) (f (n + l) .pr₁) (inc .pr₁ n (n + l) (≤-+ n l)) (transport (λ z → f (n + l) .pr₁ ≤ℕ z) (eq ⁻¹) (inc .pr₁ (n + l) (n + k) (≤-n-monotone-left l k n rl)))

private
 dd : ∀ n k → n ≤ k → k ≤ (succ n) → (k ＝ n) ＋ (k ＝ succ n) 
 dd zero zero ⋆ rl2 = inl refl
 dd zero (succ zero) ⋆ rl2 = inr refl
 dd (succ n) (succ k) rl1 rl2 = l2 (dd n k rl1 rl2) where
  l2 : (k ＝ n) ＋ (k ＝ succ n) → _
  l2 (inl x) = inl (ap succ x)
  l2 (inr x) = inr (ap succ x)

step₁ : (f : ℕ → ℕ × ℕ) → Increasing f → ∀ n → ∀ k → succ (f n .pr₁) ＝ f (n + k) .pr₁ → Σ l ꞉ ℕ , (f n .pr₁ ＝ f (n + l) .pr₁) × (succ (f n .pr₁) ＝ f (n + succ l) .pr₁)
step₁ f inc n zero eq = 𝟘-elim (succ-no-fp (f n .pr₁) (eq ⁻¹))
step₁ f inc n (succ k) eq = l2 l1 where
 l1 : (f (n + k) .pr₁ ＝ (f n .pr₁)) ＋ (f (n + k) .pr₁ ＝ succ (f n .pr₁))
 l1 = dd (f n .pr₁) (f (n + k) .pr₁) (inc .pr₁ n (n + k) (≤-+ n k)) (transport (λ z → f (n + k) .pr₁ ≤ℕ z) (eq ⁻¹) (inc .pr₁ (n + k) (succ (n + k)) (≤-succ (n + k))))
 l2 : (f (n + k) .pr₁ ＝ (f n .pr₁)) ＋ (f (n + k) .pr₁ ＝ succ (f n .pr₁)) → _
 l2 (inl x) = k , ((x ⁻¹) , eq)
 l2 (inr x) = step₁ f inc n k (x ⁻¹)

step₂ : (f : ℕ → ℕ × ℕ) → Increasing f → ∀ n → ∀ k → succ (f n .pr₂) ＝ f (n + k) .pr₂ → Σ l ꞉ ℕ , (f n .pr₂ ＝ f (n + l) .pr₂) × (succ (f n .pr₂) ＝ f (n + succ l) .pr₂)
step₂ f inc n zero eq = 𝟘-elim (succ-no-fp (f n .pr₂) (eq ⁻¹))
step₂ f inc n (succ k) eq = l2 l1 where
 l1 : (f (n + k) .pr₂ ＝ (f n .pr₂)) ＋ (f (n + k) .pr₂ ＝ succ (f n .pr₂))
 l1 = dd (f n .pr₂) (f (n + k) .pr₂) (inc .pr₂ n (n + k) (≤-+ n k)) (transport (λ z → f (n + k) .pr₂ ≤ℕ z) (eq ⁻¹) (inc .pr₂ (n + k) (succ (n + k)) (≤-succ (n + k))))
 l2 : (f (n + k) .pr₂ ＝ (f n .pr₂)) ＋ (f (n + k) .pr₂ ＝ succ (f n .pr₂)) → _
 l2 (inl x) = k , ((x ⁻¹) , eq)
 l2 (inr x) = step₂ f inc n k (x ⁻¹)

step-const₁ : (f : ℕ → ℕ × ℕ) → C f → ∀ n → Σ k ꞉ ℕ , (∀ l → l ≤ k → (f (n + l) .pr₁ ＝ f n .pr₁)) × (f (n + succ k) .pr₁ ＝ succ (f n .pr₁))
step-const₁ f c@(S , LC , RC) n = (l2 .pr₁) , (l5 , (l2 .pr₂ .pr₂ ⁻¹)) where
 inc = increasing f c
 l1 = LC (succ (f n .pr₁))
 l4 : n ≤ l1 .pr₁
 l4 = not-less-bigger-or-equal n (l1 .pr₁) λ rl → let a = inc .pr₁ (l1 .pr₁) n (<-coarser-than-≤ (l1 .pr₁) n rl) in let b = transport (λ z → z ≤ℕ f n .pr₁) (l1 .pr₂) a in not-less-than-itself (f n .pr₁) b
 l3 = subtraction n (l1 .pr₁) l4
 l2 = step₁ f inc n (l3 .pr₁) (l1 .pr₂ ⁻¹ ∙ ap (λ z → f z .pr₁) ((addition-commutativity n (l3 .pr₁) ∙ l3 .pr₂) ⁻¹))
 l5 : (l : ℕ) → l ≤ℕ l2 .pr₁ → f (n + l) .pr₁ ＝ f n .pr₁
 l5 l rl = const-interval₁ f inc n (l2 .pr₁) (l2 .pr₂ .pr₁) l rl ⁻¹

step-const₂ : (f : ℕ → ℕ × ℕ) → C f → ∀ n → Σ k ꞉ ℕ , (∀ l → l ≤ k → (f (n + l) .pr₂ ＝ f n .pr₂)) × (f (n + succ k) .pr₂ ＝ succ (f n .pr₂))
step-const₂ f c@(S , LC , RC) n = (l2 .pr₁) , (l5 , (l2 .pr₂ .pr₂ ⁻¹)) where
 inc = increasing f c
 l1 = RC (succ (f n .pr₂))
 l4 : n ≤ l1 .pr₁
 l4 = not-less-bigger-or-equal n (l1 .pr₁) λ rl → let a = inc .pr₂ (l1 .pr₁) n (<-coarser-than-≤ (l1 .pr₁) n rl) in let b = transport (λ z → z ≤ℕ f n .pr₂) (l1 .pr₂) a in not-less-than-itself (f n .pr₂) b
 l3 = subtraction n (l1 .pr₁) l4
 l2 = step₂ f inc n (l3 .pr₁) (l1 .pr₂ ⁻¹ ∙ ap (λ z → f z .pr₂) ((addition-commutativity n (l3 .pr₁) ∙ l3 .pr₂) ⁻¹))
 l5 : (l : ℕ) → l ≤ℕ l2 .pr₁ → f (n + l) .pr₂ ＝ f n .pr₂
 l5 l rl = const-interval₂ f inc n (l2 .pr₁) (l2 .pr₂ .pr₁) l rl ⁻¹

-- TODO It needs debuggging
next-step : (f : ℕ → ℕ × ℕ) → C f → ℕ → 𝟚 × ℕ
next-step f c@(S , LC , RC) n = l3 (≤-decidable (l1 .pr₁) (l2 .pr₁)) where
 l1 = step-const₁ f c n
 l2 = step-const₂ f c n
 l3 : is-decidable ((l1 .pr₁) ≤ (l2 .pr₁)) → _
 l3 (inl x) = ₁ , l2 .pr₁
 l3 (inr x) = ₀ , l1 .pr₁


to-step-f : (f : ℕ → ℕ × ℕ) → C f → ℕ → ℕ × ℕ
to-step-f f c@(S , LC , RC) zero = r , r where
 r = next-step f c 0 .pr₂
to-step-f f c@(S , LC , RC) (succ n)
 = let k = to-step-f f c n .pr₂
       r = next-step f c k .pr₂
   in r , k + r

to-step-2f :  (f : ℕ → ℕ × ℕ) → C f → (ℕ → ℕ) × 𝟚
to-step-2f f c = (λ n → to-step-f f c n .pr₁) , next-step f c 0 .pr₁


----------------------------------------------------------------------------

-- index , index + 1 total elements
index : ∀{n} → (Fin n → ℕ) → ℕ
index {zero} f = f (0 , ⋆)
index {succ n} f = (index {n = n} λ (r , rl) → f ((succ r) , rl)) + succ (f (0 , ⋆))

-- ₁ is left , ₀ is right
succ× : 𝟚 × ℕ × ℕ → ℕ × ℕ
succ× (₀ , a , b) = a , succ b
succ× (₁ , a , b) = succ a , b

n-succ× : (n : ℕ) → 𝟚 → ℕ × ℕ → (Fin n → ℕ × ℕ)
n-succ× n two q (zero , rl) = succ× (two , q)
n-succ× (succ n) two q (succ r , rl) = n-succ× n two (succ× (two , q)) (r , rl)



2ℕ'-fin : ∀{n} → (f : Fin n → ℕ) → 𝟚 → ℕ × ℕ → Fin (index f) → ℕ × ℕ
2ℕ'-fin {zero} f two q = n-succ× (f (0 , ⋆)) two q
2ℕ'-fin {succ n} f two q
 = let r2 = n-succ× (f (0 , _)) two q
       nq = (r2 (f (0 , _) , ≤-refl (f (0 , _))))
       r1 = 2ℕ'-fin (λsuccₙ f) (complement two) nq
   in r1 +ᶠ r2

2ℕ-fin : ∀{n} → (f : Fin n → ℕ) → 𝟚 → Fin (succ (index f)) → ℕ × ℕ
2ℕ-fin f two (zero , rl) = 0 , 0
2ℕ-fin f two (succ z , rl) = 2ℕ'-fin f two (0 , 0) (z , rl)


module test where


 ff : Fin 6 → ℕ × ℕ
 ff (zero , pr₄) = 0 , 0
 ff (succ zero , pr₄) = 0 , 1
 ff (succ (succ zero) , pr₄) = 0 , 2
 ff (succ (succ (succ zero)) , pr₄) = 1 , 2
 ff (succ (succ (succ (succ zero))) , pr₄) = 2 , 2
 ff (succ (succ (succ (succ (succ zero)))) , pr₄) = 3 , 2
 ff (succ (succ (succ (succ (succ (succ zero))))) , pr₄) = 3 , 3
 
 cff : Cₙ ff
 cff .pr₁ (zero , pr₄) = inr refl
 cff .pr₁ (succ zero , pr₄) = inr refl
 cff .pr₁ (succ (succ zero) , pr₄) = inl refl
 cff .pr₁ (succ (succ (succ zero)) , pr₄) = inl refl
 cff .pr₁ (succ (succ (succ (succ zero))) , pr₄) = inl refl
 cff .pr₁ (succ (succ (succ (succ (succ zero)))) , pr₄) = inr refl
 cff .pr₂ = refl
 
 
 ff2 : Fin 6 → ℕ × ℕ
 ff2 (zero , pr₄) = 0 , 0
 ff2 (succ zero , pr₄) = 1 , 0
 ff2 (succ (succ zero) , pr₄) = 1 , 1
 ff2 (succ (succ (succ zero)) , pr₄) = 2 , 1
 ff2 (succ (succ (succ (succ zero))) , pr₄) = 2 , 2
 ff2 (succ (succ (succ (succ (succ zero)))) , pr₄) = 3 , 2
 ff2 (succ (succ (succ (succ (succ (succ zero))))) , pr₄) = 3 , 3
 
 cff2 : Cₙ ff2
 cff2 .pr₁ (zero , _) = inl refl
 cff2 .pr₁ (succ zero , _) = inr refl
 cff2 .pr₁ (succ (succ zero) , _) = inl refl
 cff2 .pr₁ (succ (succ (succ zero)) , _) = inr refl
 cff2 .pr₁ (succ (succ (succ (succ zero))) , _) = inl refl
 cff2 .pr₁ (succ (succ (succ (succ (succ zero)))) , _) = inr refl
 cff2 .pr₂ = refl
 

 l1 = to-step-fₙ ff2 cff2
 l2 = 2ℕ-fin (l1 .pr₂ .pr₁) (l1 .pr₂ .pr₂)
 k0 = l2 (0 , _)
 k1 = l2 (1 , _)
 k2 = l2 (2 , _)
 k3 = l2 (3 , _)
 k4 = l2 (4 , _)
 k5 = l2 (5 , _)
 k6 = l2 (6 , _)

 test : (k0 ＝ (0 , 0)) × (k1 ＝ (1 , 0)) × (k2 ＝ (1 , 1)) × (k3 ＝ (2 , 1)) × (k4 ＝ (2 , 2)) × (k5 ＝ (3 , 2)) × (k6 ＝ (3 , 3))
 test = refl , refl , refl , refl , refl , refl , refl

 l3 = to-step-fₙ ff cff
 l4 = 2ℕ-fin (l3 .pr₂ .pr₁) (l3 .pr₂ .pr₂)
 m0 = l4 (0 , _)
 m1 = l4 (1 , _)
 m2 = l4 (2 , _)
 m3 = l4 (3 , _)
 m4 = l4 (4 , _)
 m5 = l4 (5 , _)
 m6 = l4 (6 , _)

 test2 : (m0 ＝ (0 , 0)) × (m1 ＝ (0 , 1)) × (m2 ＝ (0 , 2)) × (m3 ＝ (1 , 2)) × (m4 ＝ (2 , 2)) × (m5 ＝ (3 , 2)) × (m6 ＝ (3 , 3))
 test2 = refl , refl , refl , refl , refl , refl , refl


------------------------------------------------------------------

λsucc : ∀{𝓦} → {A : 𝓦 ̇ } → (ℕ → A) → (ℕ → A)
λsucc f r = f (succ r)

_+ⁱᶠ_ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{k} → (ℕ → A) → (Fin k → A) → ℕ → A
_+ⁱᶠ_ {A = A} {k} f1 f2 zero = f2 (0 , ⋆)
_+ⁱᶠ_ {A = A} {zero} f1 f2 (succ r) = f1 r
_+ⁱᶠ_ {A = A} {succ k} f1 f2 (succ r) = _+ⁱᶠ_ {k = k} f1 (λsuccₙ f2) r

-- (𝟚 × ℕ × ℕ) (direction of change, last index of f, remaining change)
-- ℕ × ℕ current state of the index of constructed function.
ind-succ× : (f : ℕ → ℕ) → ((𝟚 × ℕ × ℕ) × ℕ × ℕ) → (𝟚 × ℕ × ℕ) × ℕ × ℕ
ind-succ× f ((two , nf , zero) , r) = (complement two , succ nf , f (succ nf)) , succ× (two , r)
ind-succ× f ((two , nf , succ q) , r) = (two , nf , q) , succ× (two , r)

2ℕ-inf' : (f : ℕ → ℕ) → (𝟚 × ℕ × ℕ) × ℕ × ℕ → ℕ → (𝟚 × ℕ × ℕ) × ℕ × ℕ
2ℕ-inf' f e zero = e
2ℕ-inf' f e (succ r) = let w = ind-succ× f e in 2ℕ-inf' f w r 


2ℕ-inf'-+ : (f : ℕ → ℕ) → (e : (𝟚 × ℕ × ℕ) × ℕ × ℕ) → (r1 r2 : ℕ)
 → 2ℕ-inf' f (2ℕ-inf' f e r1) r2 ＝ 2ℕ-inf' f e (r2 + r1)
2ℕ-inf'-+ f e zero r2 = refl
2ℕ-inf'-+ f e (succ r1) r2 = 2ℕ-inf'-+ f (ind-succ× f e) r1 r2


2ℕ-inf-s : (ℕ → ℕ) × 𝟚 → ℕ → (𝟚 × ℕ × ℕ) × ℕ × ℕ
2ℕ-inf-s (f , two) r = 2ℕ-inf' f ((two , 0 , f 0 ) , 0 , 0) r

2ℕ-inf : (ℕ → ℕ) × 𝟚 → ℕ → ℕ × ℕ
2ℕ-inf f r = 2ℕ-inf-s f r .pr₂


module test2 where

----------------------------------------------------------------------------



from-××-＝ : {v b : (𝟚 × ℕ × ℕ) × ℕ × ℕ}
      → let ((i1 , i2 , i3) , i4) = v
            ((j1 , j2 , j3) , j4) = b
        in v ＝ b → (i1 ＝ j1) × (i2 ＝ j2) × (i3 ＝ j3) × (i4 ＝ j4)
from-××-＝ eq = (from-×-＝' (from-×-＝' eq .pr₁) .pr₁) , from-×-＝' (from-×-＝' (from-×-＝' eq .pr₁) .pr₂) .pr₁ , from-×-＝' (from-×-＝' (from-×-＝' eq .pr₁) .pr₂) .pr₂ , from-×-＝' eq .pr₂

to-××-＝ : ∀ {i1 i2 i3 i4 j1 j2 j3 j4}
     → (i1 ＝ j1) × (i2 ＝ j2) × (i3 ＝ j3) × (i4 ＝ j4)
     → _＝_ {X = (𝟚 × ℕ × ℕ) × ℕ × ℕ} ((i1 , i2 , i3) , i4) ((j1 , j2 , j3) , j4)
to-××-＝ eq = to-×-＝ (to-×-＝ (eq .pr₁) (to-×-＝ (eq .pr₂ .pr₁) (eq .pr₂ .pr₂ .pr₁))) (eq .pr₂ .pr₂ .pr₂)


ind-succ×-eq : (f g : (ℕ → ℕ)) → (c : Σ l ꞉ ℕ , (∀ n → f (l + (succ n)) ＝ g (succ n)))
 → ∀ n → ∀ two q a
 → let ((i1 , i2 , i3) , i4) = ind-succ× f ((two , c .pr₁ + n , q) , a)
       ((j1 , j2 , j3) , j4) = ind-succ× g ((two , n , q) , a)
   in (i1 ＝ j1) × (i2 ＝ c .pr₁ + j2) × (i3 ＝ j3) × (i4 ＝ j4)
ind-succ×-eq f g (l , c) n two zero a = refl , refl , c n , refl
ind-succ×-eq f g (l , c) n two (succ q) a =  refl , refl , refl , refl

2ℕ-inf'-l+n=n : (f g : (ℕ → ℕ)) → (c : Σ l ꞉ ℕ , (∀ n → f (l + (succ n)) ＝ g (succ n)))
 → ∀ n → ∀ two q a → ∀ r
 → let l = c .pr₁
       ((i1 , i2 , i3) , i4) = 2ℕ-inf' f ((two , l + n , q) , a) r
       ((j1 , j2 , j3) , j4) = 2ℕ-inf' g ((two , n , q) , a) r
   in ((i1 , i2 , i3) , i4) ＝ ((j1 , l + j2 , j3) , j4)
2ℕ-inf'-l+n=n f g c n two q a zero = refl
2ℕ-inf'-l+n=n f g c n two q a (succ r)
 =   ap (λ z → 2ℕ-inf' f z r) (let eq = ind-succ×-eq f g c n two q a
                                 in to-××-＝ eq)
   ∙ let ((j1 , j2 , j3) , j4) = ind-succ× g (((two , n , q) , a))
     in 2ℕ-inf'-l+n=n f g c j2 j1 j3 j4 r

2ℕ-inf'-f＝f+l : (f : (ℕ → ℕ)) → ∀ l
 → ∀ n → ∀ two q a → ∀ r
 → let ((i1 , i2 , i3) , i4) = 2ℕ-inf' f ((two , l + n , q) , a) r
       ((j1 , j2 , j3) , j4) = 2ℕ-inf' (λ z → f (l + z)) ((two , n , q) , a) r
   in ((i1 , i2 , i3) , i4) ＝ ((j1 , l + j2 , j3) , j4)
2ℕ-inf'-f＝f+l f l n two q a r = 2ℕ-inf'-l+n=n f (λ z → f (l + z)) (l , (λ n₁ → refl)) n two q a r

2ℕ-inf'-l+n=k+n : (f g : (ℕ → ℕ)) → (c : Σ l ꞉ ℕ , Σ k ꞉ ℕ , (∀ n → f (l + (succ n)) ＝ g (k + (succ n))))
 → ∀ n → ∀ two q a → ∀ r
 → let l = c .pr₁
       k = c .pr₂ .pr₁
       ((i1 , i2 , i3) , i4) = 2ℕ-inf' f ((two , l + n , q) , a) r
       ((j1 , j2 , j3) , j4) = 2ℕ-inf' g ((two , k + n , q) , a) r
   in ((i1 , k + i2 , i3) , i4) ＝ ((j1 , l + j2 , j3) , j4)
2ℕ-inf'-l+n=k+n f g (l , k , c) n two q a r
 = let e = from-××-＝ (2ℕ-inf'-f＝f+l g k n two q a r)
--       (j1 j2 j3 j4 = i1 (c .pr₂ .pr₁ + i2) i3 i4
       t = from-××-＝ (2ℕ-inf'-l+n=n f (λ z → g (k + z)) (l , c) n two q a r)
--       t1 t2 t3 t4 = i1 (c .pr₁ + i2) i3 i4
       j1-i1 = e .pr₁
       j2-i2 = e .pr₂ .pr₁
       j3-i3 = e .pr₂ .pr₂ .pr₁
       j4-i4 = e .pr₂ .pr₂ .pr₂
       t1-i1 = t .pr₁
       t2-i2 = t .pr₂ .pr₁
       t3-i3 = t .pr₂ .pr₂ .pr₁
       t4-i4 = t .pr₂ .pr₂ .pr₂
       n = 2ℕ-inf' (λ z → g (k + z)) ((two , n , q) , a) r .pr₁ .pr₂ .pr₁
       l = ap (λ z → k + z) t2-i2 ∙ ((addition-associativity k l n ⁻¹ ∙ ap (λ z → z + n) (addition-commutativity k l) ∙ addition-associativity l k n) ∙ ap (λ z → l + z) (j2-i2 ⁻¹))
   in to-××-＝ ((t1-i1 ∙ j1-i1 ⁻¹) , l , (t3-i3 ∙ j3-i3 ⁻¹) , (t4-i4 ∙ j4-i4 ⁻¹))

-- In general r1 must be equal to r2 , but it does not seem necessary here.
2ℕ-inf-s-+r1,r2 : (f g : (ℕ → ℕ) × 𝟚) →
        (c : Σ r1 ꞉ ℕ , Σ r2 ꞉ ℕ ,
              let ((i1 , i2 , i3) , i4) = 2ℕ-inf-s f r1
                  ((j1 , j2 , j3) , j4) = 2ℕ-inf-s g r2
              in  ((∀ n → (f .pr₁) (i2 + (succ n)) ＝ (g .pr₁) (j2 + succ n))
                    × ((i1 , i3 , i4) ＝ (j1 , j3 , j4))))
       → ∀ r → let r1 = c .pr₁
                   r2 = c .pr₂ .pr₁
                   ((_ , i2 , _) , _) = 2ℕ-inf-s f r1
                   ((_ , j2 , _) , _) = 2ℕ-inf-s g r2
                   ((i1' , i2' , i3') , i4') = 2ℕ-inf-s f (r + r1)
                   ((j1' , j2' , j3') , j4') = 2ℕ-inf-s g (r + r2)
               in ((i1' , j2 + i2' , i3') , i4') ＝ ((j1' , i2 + j2' , j3') , j4')
2ℕ-inf-s-+r1,r2 f g (r1 , r2 , (c , eq)) r
 = let trf = 2ℕ-inf'-+ (f .pr₁) ((f .pr₂ , 0 , f .pr₁ 0) , 0 , 0) r1 r
       trg = 2ℕ-inf'-+ (g .pr₁) ((g .pr₂ , 0 , g .pr₁ 0) , 0 , 0) r2 r
       ((i1 , i2 , i3) , i4) = 2ℕ-inf-s f r1
       ((j1 , j2 , j3) , j4) = 2ℕ-inf-s g r2
       l = from-××-＝ (2ℕ-inf'-l+n=k+n (f .pr₁) (g .pr₁) (i2 , (j2 , c)) 0 i1 i3 i4 r)
       -- TODO Can we clean this?
       l1 = ap (λ z → z .pr₁ .pr₁) trf ⁻¹ ∙ l .pr₁ ∙ ap (λ (z1 , z3 , z4) → 2ℕ-inf' (g .pr₁) ((z1 , 2ℕ-inf' (g .pr₁) ((g .pr₂ , 0 , g .pr₁ 0) , 0 , 0) r2 .pr₁ .pr₂ .pr₁ , z3) , z4) r .pr₁ .pr₁) eq ∙ ap (λ z → z .pr₁ .pr₁) trg
       l3 = ap (λ z → z .pr₁ .pr₂ .pr₂) trf ⁻¹ ∙ l .pr₂ .pr₂ .pr₁ ∙ ap (λ (z1 , z3 , z4) → 2ℕ-inf' (g .pr₁) ((z1 , 2ℕ-inf' (g .pr₁) ((g .pr₂ , 0 , g .pr₁ 0) , 0 , 0) r2 .pr₁ .pr₂ .pr₁ , z3) , z4) r .pr₁ .pr₂ .pr₂) eq ∙ ap (λ z → z .pr₁ .pr₂ .pr₂) trg
       l4 = ap (λ z → z .pr₂) trf ⁻¹ ∙ l .pr₂ .pr₂ .pr₂ ∙ ap (λ (z1 , z3 , z4) → 2ℕ-inf' (g .pr₁) ((z1 , 2ℕ-inf' (g .pr₁) ((g .pr₂ , 0 , g .pr₁ 0) , 0 , 0) r2 .pr₁ .pr₂ .pr₁ , z3) , z4) r .pr₂) eq ∙ ap (λ z → z .pr₂) trg
       l5 = ap (λ z → j2 + z .pr₁ .pr₂ .pr₁) trf ⁻¹ ∙ l .pr₂ .pr₁ ∙ (ap (λ (z1 , z3 , z4) → i2 + 2ℕ-inf' (g .pr₁) ((z1 , 2ℕ-inf' (g .pr₁) ((g .pr₂ , 0 , g .pr₁ 0) , 0 , 0) r2 .pr₁ .pr₂ .pr₁ , z3) , z4) r .pr₁ .pr₂ .pr₁) eq ∙ ap (λ z → i2 + z .pr₁ .pr₂ .pr₁) trg)
   in to-××-＝ (l1 , l5 , l3 , l4)


2ℕ-inf-cond : (f g : (ℕ → ℕ) × 𝟚) →
        (c : Σ r1 ꞉ ℕ , Σ r2 ꞉ ℕ , 
              let ((i1 , i2 , i3) , i4) = 2ℕ-inf-s f r1
                  ((j1 , j2 , j3) , j4) = 2ℕ-inf-s g r2
              in  ((∀ n → (f .pr₁) (i2 + succ n) ＝ (g .pr₁) (j2 + succ n))
                    × ((i1 , i3 , i4) ＝ (j1 , j3 , j4))))
       → ∀ r → let r1 = c .pr₁
                   r2 = c .pr₂ .pr₁
               in 2ℕ-inf f (r + r1) ＝ 2ℕ-inf g (r + r2)
2ℕ-inf-cond f g (r1 , r2 , c) r = ap pr₂ (2ℕ-inf-s-+r1,r2 f g (r1 , r2 , c) r)


-- _∈ₚ_ : (ℕ × ℕ) → ∀{n l r} → BFun n l r → 𝓤₀ ̇
-- x ∈ₚ (f , two , lc , rc) = Σ i ꞉ Fin (succ (index f)) , 2ℕ-fin f two i ＝ x

-- _∈ₚᵢ_ : (ℕ × ℕ) → (ℕ → ℕ) × 𝟚 → 𝓤₀ ̇
-- x ∈ₚᵢ f = Σ i ꞉ ℕ , 2ℕ-inf f i ＝ x
