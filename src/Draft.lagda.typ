
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Operators
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan renaming (_+_ to _or_)
open import Naturals.Addition
open import UF.FunExt
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties


```
*/

```agda

open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
open import PredP
open Pred

module Draft (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 where

open import Definitions Msg Secret

open ΣPred
open import PotP Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠


Increasing : (f : ℕ → ℕ) → 𝓤₀ ̇
Increasing f = ∀ x y → succ x ≤ y → succ (f x) ≤ f y

Starts-from-zero : (f : ℕ → ℕ) → 𝓤₀ ̇
Starts-from-zero f = f 0 ＝ 0

Zero-Increasing : (f : ℕ → ℕ) → 𝓤₀ ̇
Zero-Increasing f = Increasing f × Starts-from-zero f

Fin : (n : ℕ) → 𝓤₀ ̇
Fin n = Σ x ꞉ ℕ , x ≤ n

Fin-Increasing : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
Fin-Increasing n f = ∀ (x y : Fin n) → succ < x > ≤ < y > → succ (f x) ≤ f y


Starts-from-fzero : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
Starts-from-fzero n f = f (0 , ⋆) ＝ 0

Zero-Fin-Increasing : (n : ℕ) → (f : Fin n → ℕ) → 𝓤₀ ̇
Zero-Fin-Increasing n f = Fin-Increasing n f × Starts-from-fzero n f

Interleaving : 𝓤₀ ̇
Interleaving = 𝟚 × Σ Zero-Increasing × Σ Zero-Increasing

Fin-Interleaving : 𝓤₀ ̇
Fin-Interleaving = Σ λ n → (Σ (Fin-Increasing n) × Σ (Fin-Increasing (succ n))) or (Σ (Fin-Increasing (succ n)) × Σ (Fin-Increasing n))

-- In some cases we only care for the last value before
-- a communication happens between the two potentialities.

G : Fin-Interleaving → ℕ → ℕ → 𝓤₀ ̇
G (n , inl ((f , _) , g , _)) k l = (f (n , ≤-refl n) ＝ k) × (g (succ n , ≤-refl n) ＝ l)
G (n , inr ((f , _) , g , _)) k l = (f (succ n , ≤-refl n) ＝ k) × (g (n , ≤-refl n) ＝ l)


-- given a function f, we can get a function that is strictly increasing
inc : (ℕ → ℕ) → ℕ → ℕ
inc f zero = 0
inc f (succ x) = (inc f x) + succ (f x)

inc-Inc : (f : ℕ → ℕ) → Increasing (inc f)
inc-Inc f x y eq with subtraction (succ x) y eq
... | k , ee with (addition-commutativity x (succ k)) ∙ succ-left k x ∙ ee
inc-Inc f x y eq | zero , ee | refl = ≤-+ (inc f x) (f x)
inc-Inc f x y eq | succ k , ee | refl = ≤-trans (inc f x) (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (inc-Inc f x (succ (x + k)) (≤-+ x k)) (≤-trans (inc f (x + k) + f (x + k)) (succ (inc f (x + k) + f (x + k))) (succ (inc f (x + k) + f (x + k)) + f (succ (x + k))) (≤-succ (inc f (x + k) + f (x + k))) (≤-+ (succ (inc f (x + k) + f (x + k))) (f (succ (x + k)))))


module _ (fc-pot : Pot) where

 open Functor Fpot
 open CoAlgebra Fpot
 open Final-CoAlgebra Fpot fc-pot
 open import Final-CoAlgebra-Properties fe Fpot fc-pot
 open CoAlgebra₂ Fpot f-co fc
 open Morphism

 open import FCP Msg Secret 𝓥 ⟨ fc ⟩
 open FC
 open Pot {fc-pot}
 open Pot₁ fe {fc-pot}


 data Fin-ex-comm (d : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
  ←m : (n : ℕ) →
        let fd = foc (d at n)
        in (msg : S×Msg) → (bsm : < Mp fd > msg)
           → Fin-ex-comm ((fc ⟶) (fm fd msg bsm)) → Fin-ex-comm d
  →a : (n : ℕ) →
        let fd = foc (d at n)
        in (msg : S×Msg) → (bsa : < Ap fd > msg)
           → Fin-ex-comm ((fc ⟶) (fa fd msg bsa)) → Fin-ex-comm d
  here : Fin-ex-comm d

 record Fin-ex-comm-∞ (d : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
  coinductive
  field
   n : ℕ
   msg : S×Msg
   cond : let fd = foc (d at n) in < Mp fd > msg or < Ap fd > msg
   more : let fd = foc (d at n) in Fin-ex-comm-∞ (case cond of λ { (inl x) → (fc ⟶) (fm fd msg x) ; (inr x) → (fc ⟶) (fa fd msg x)})
   
  
 g : {d : Fn ⟨ fc ⟩} → Fin-ex-comm d → Fn ⟨ fc ⟩

 g {d} (←m n msg bsm x) = (replace d at n) (g x)
 g {d} (→a n msg bsa x) = (replace d at n) (g x)
 g {d} here = d



-- -- Here we are only interested for the rest of the sequence, since we have finite
-- -- communication , thus we omit the finite sequence that has passed before.
--  data Fin-comm (d b : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
--    a←m : (n m : ℕ) →
--          let fd = foc (d at n)
--              fb = foc (b at m)
--          in (msg : S×Msg) → (bsm : < Mp fd > msg) → (bsa : < Ap fb > msg)
--             → Fin-comm ((fc ⟶) (fm fd msg bsm)) (((fc ⟶) (fa fb msg bsa))) → Fin-comm d b
--    m→a : (n m : ℕ) →
--          let fd = foc (d at n)
--              fb = foc (b at m)
--          in (msg : S×Msg) → (bsm : < Mp fb > msg) → (bsa : < Ap fd > msg)
--             → Fin-comm ((fc ⟶) (fa fd msg bsa)) (((fc ⟶) (fm fb msg bsm))) → Fin-comm d b
--    here : Fin-comm d b
 
--  goTo : {a : Fn ⟨ fc ⟩} → Fin-ex-comm a → Fn ⟨ fc ⟩
--  goTo (←m n msg bsm s) = goTo s
--  goTo (→a n msg bsa s) = goTo s
--  goTo {a} here = a




-- -----------------------------------------------------------------------


--  PotSet : ∀ 𝓣 → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ⊔ 𝓣 ⁺ ̇
--  PotSet 𝓣 = Fn ⟨ fc ⟩ → 𝓣 ̇

--  PotSet₂ : ∀ 𝓣 → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ⊔ 𝓣 ⁺ ̇
--  PotSet₂ 𝓣 = Fn ⟨ fc ⟩ → Fn ⟨ fc ⟩ → 𝓣 ̇


-- --  Liveness1 : (PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → 𝓣 ̇) → PotSet₂ 𝓣
-- --  Liveness1 {𝓣 = 𝓣} R a b = (iv : 𝟚 × Σ Increasing × Σ Increasing) → (n : ℕ) → Σ k ꞉ ℕ , n ≤ k × rr iv k where
-- --    rra : (k : ℕ) → (r : 𝟚) → IV r → 𝓣 ̇
-- --    rra k t (x [ y1 , y2 ]) = Σ m ꞉ ℕ , (m ≤ y2) × (y1 ≤ m) × R ((a at x) .pr₂ .pr₁) ((b at m) .pr₂ .pr₁)
-- --    rra k t ([ x2 , x1 ] y) = Σ m ꞉ ℕ , (m ≤ x2) × (x1 ≤ m) × R ((a at m) .pr₂ .pr₁) ((b at y) .pr₂ .pr₁)
-- --    rr : (iv : 𝟚 × Σ Increasing × Σ Increasing) → (k : ℕ) → 𝓣 ̇
-- --    rr (q , f , g) k = rra k (q +₂ (div₂ k .pr₂)) (intV q < f > < g > k)

-- --  Liveness2 : (PSet 𝓥 _ _ → PSet 𝓥 _ _ → 𝓣 ̇) → PotSet₂ (𝓤 ⊔ 𝓥 ⊔ 𝓣)
-- --  Liveness2 R a b = (sa : SS a) → (sb : SS b) → Liveness1 R (goTo sa) (goTo sb) 





-- -- --  data IV : 𝟚 → 𝓤₀ ̇ where
-- -- --   _[_,_] : ℕ → ℕ → ℕ → IV ₀
-- -- --   [_,_]_ : ℕ → ℕ → ℕ → IV ₁

-- -- --  -- we devide by 2 and take the remaining value
-- -- --  div₂ : (y : ℕ) → ℕ × 𝟚
-- -- --  div₂ zero = zero , ₀
-- -- --  div₂ (succ y) = h (div₂ y) where
-- -- --   h : ℕ × 𝟚 → ℕ × 𝟚
-- -- --   h (x , ₀) = x , ₁
-- -- --   h (x , ₁) = succ x , ₀

-- -- --  _+₂_ : 𝟚 → 𝟚 → 𝟚
-- -- --  _+₂_ ₀ y = y
-- -- --  _+₂_ ₁ ₀ = ₁
-- -- --  _+₂_ ₁ ₁ = ₀

-- -- --  intV-h : (q : 𝟚) → (f g : ℕ → ℕ) → (h : ℕ) → (v : ℕ × 𝟚) → IV (q +₂ (v .pr₂))
-- -- --  intV-h ₁ f g h (r , ₀) = [ f r , f (succ r) ] (g r)
-- -- --  intV-h ₁ f g h (r , ₁) = f (succ r) [ g r , g (succ r) ]
-- -- --  intV-h ₀ f g h (r , ₀) = f r  [ g r , g (succ r) ]
-- -- --  intV-h ₀ f g h (r , ₁) = [ f r , f (succ r) ]  g (succ r)

-- -- --  intV : (q : 𝟚) → (ℕ → ℕ) → (ℕ → ℕ) → (h : ℕ) → IV (q +₂ (div₂ h .pr₂))
-- -- --  intV q f g h = intV-h q f g h (div₂ h)

  
-- -- -- --  record CC (a : Fn ⟨ fc ⟩) : {!!} where
-- -- -- --   coinductive
-- -- -- --   field
-- -- -- --    n : ℕ
-- -- -- --    bs : Σ < Mp ((a at n) .pr₂ .pr₂) >
-- -- -- --    nc : CC ((fc ⟶) (fm ((a at n) .pr₂ .pr₂) (bs .pr₁) (bs .pr₂)))

-- -- -- --  F : Functor {!!}
-- -- -- --  F = (λ X → X × (Σ a ꞉ Fn ⟨ fc ⟩ , Σ n ꞉ ℕ , let fca : FC
-- -- -- --                                                  fca = (a at n) .pr₂ .pr₂
-- -- -- --                                              in Σ < Mp fca >)) , {!!} , {!!} , {!!}

-- -- -- -- --  Liveness2 : (&PSet 𝓥 _ → &PSet 𝓥 _ → 𝓣 ̇) → PotSet₂ {!!}
-- -- -- -- --  Liveness2 R a b = ∀ k m → fcm1 × {!!} where
-- -- -- -- --    fca : ∀ k → FC
-- -- -- -- --    fca k = (a at k) .pr₂ .pr₂
-- -- -- -- --    fcb : ∀ m → FC
-- -- -- -- --    fcb m = (b at m) .pr₂ .pr₂

-- -- -- -- --    fcm1 = ∀ k m x → (bs : < Mp (fca k) > x) → Liveness1 R ((fc ⟶) (fm (fca k) x bs)) (b at m) × Liveness2 R ((fc ⟶) (fm (fca k) x bs)) (b at m)
-- -- -- -- --    fcm2 = ∀ k m x → (bs : < Mp (fcb m) > x) → Liveness1 R ((fc ⟶) (fm (fcb m) x bs)) (a at k) × Liveness2 R ((fc ⟶) (fm (fcb m) x bs)) (a at k)

-- -- -- -- --    fca1 = ∀ k m x → (bs : < Ap (fca k) > x) → Liveness1 R ((fc ⟶) (fa (fca k) x bs)) (b at m) × Liveness2 R ((fc ⟶) (fa (fca k) x bs)) (b at m)
-- -- -- -- --    fca2 = ∀ k m x → (bs : < Ap (fcb m) > x) → Liveness1 R ((fc ⟶) (fa (fcb m) x bs)) (a at k) × Liveness2 R ((fc ⟶) (fa (fcb m) x bs)) (a at k)


-- -- -- -- -- -- 
-- -- -- -- -- -- -- Interleaving Pot
-- -- -- -- -- --  ss :  (ℕ → ℕ × ℕ) → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × ℕ × ℕ → Fn (Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩ × ℕ × ℕ)
-- -- -- -- -- --  ss w (a , b , n , zero)
-- -- -- -- -- --   = let wa = w n .pr₁
-- -- -- -- -- --         wb = w n .pr₂
-- -- -- -- -- --         (na , pa , fca) = a at wa
-- -- -- -- -- --         (nb , pb , fcb) = b at wb
-- -- -- -- -- --        --(na , pa , fca) = a at wa
-- -- -- -- -- --        -- (nb , pb , fcb) = b at wb
-- -- -- -- -- --     in   ((fc ⟶) na , (fc ⟶) nb , n , succ zero)
-- -- -- -- -- --        , (pa || pb) , ((Mp fca ∨ Mp fcb)
-- -- -- -- -- --        , λ { x (inl bs) → {!fm!} ;
-- -- -- -- -- --              x (inr bs) → {!!}}) , {!!}
-- -- -- -- -- --  ss w ((na , pa , fca) , (nb , pb , fcb) , n , succ m) = {!!}
-- -- -- -- -- -- 
-- -- -- -- -- ```
