
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
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties
open import MLTT.Two-Properties


```
*/

```agda

module Interleaving2 where

Fin : (n : ℕ) → 𝓤₀ ̇
Fin n = Σ x ꞉ ℕ , x ≤ n

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

λsuccᶠ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{n} → (Fin (succ n) → A) → (Fin n → A)
λsuccᶠ f (r , rl) = f (succ r , rl)

_+ᶠ_ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{n k} → (Fin n → A) → (Fin k → A) → Fin (n + (succ k)) → A
_+ᶠ_ {A = A} {n} {k} f1 f2 (zero , rl) = f2 (0 , ⋆)
_+ᶠ_ {A = A} {n} {zero} f1 f2 (succ r , rl) = f1 (r , rl)
_+ᶠ_ {A = A} {n} {succ k} f1 f2 (succ r , rl) = (f1 +ᶠ λsuccᶠ f2) (r , rl)

2ℕ'-fin : ∀{n} → (f : Fin n → ℕ) → 𝟚 → ℕ × ℕ → Fin (index f) → ℕ × ℕ
2ℕ'-fin {zero} f two q = n-succ× (f (0 , ⋆)) two q
2ℕ'-fin {succ n} f two q
 = let r2 = n-succ× (f (0 , _)) two q
       nq = (r2 (f (0 , _) , ≤-refl (f (0 , _))))
       r1 = 2ℕ'-fin (λsuccᶠ f) (complement two) nq
   in r1 +ᶠ r2

2ℕ-fin : ∀{n} → (f : Fin n → ℕ) → 𝟚 → Fin (succ (index f)) → ℕ × ℕ
2ℕ-fin f two (zero , rl) = 0 , 0
2ℕ-fin f two (succ z , rl) = 2ℕ'-fin f two (0 , 0) (z , rl)

BFun : (n : ℕ) → ℕ → ℕ → 𝓤₀ ̇
BFun n l r = Σ f ꞉ (Fin n → ℕ) , Σ two ꞉ 𝟚 , let last = 2ℕ-fin f two (succ (index f) , ≤-refl (succ (index f))) in (last .pr₁ ＝ l) × (last .pr₂ ＝ r)


λsucc : ∀{𝓦} → {A : 𝓦 ̇ } → (ℕ → A) → (ℕ → A)
λsucc f r = f (succ r)

_+ⁱᶠ_ : ∀{𝓦} → {A : 𝓦 ̇ } → ∀{k} → (ℕ → A) → (Fin k → A) → ℕ → A
_+ⁱᶠ_ {A = A} {k} f1 f2 zero = f2 (0 , ⋆)
_+ⁱᶠ_ {A = A} {zero} f1 f2 (succ r) = f1 r
_+ⁱᶠ_ {A = A} {succ k} f1 f2 (succ r) = _+ⁱᶠ_ {k = k} f1 (λsuccᶠ f2) r

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


_∈ₚ_ : (ℕ × ℕ) → ∀{n l r} → BFun n l r → 𝓤₀ ̇
x ∈ₚ (f , two , lc , rc) = Σ i ꞉ Fin (succ (index f)) , 2ℕ-fin f two i ＝ x

_∈ₚᵢ_ : (ℕ × ℕ) → (ℕ → ℕ) × 𝟚 → 𝓤₀ ̇
x ∈ₚᵢ f = Σ i ꞉ ℕ , 2ℕ-inf f i ＝ x
