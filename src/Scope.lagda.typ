
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
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
import UF.ImageAndSurjection

open import Lists

module Scope (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) where

open PropositionalTruncation pt
open UF.ImageAndSurjection pt

open import PredP
open Pred
open ΣPred
open import Definitions Msg Secret


_$₂_ : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → {B : 𝓥 ̇ } → (A → B) → A × A → B × B
f $₂ (a , b) = f a , f b

+→𝟚 : ∀{𝓤 𝓥} → {X : 𝓤 ̇ } → {Y : 𝓥 ̇ } → X + Y → 𝟚
+→𝟚 (inl x) = ₀
+→𝟚 (inr x) = ₁

scope-l1 : (x : Secret) → (ls : List Secret) → (A : 𝟚 → 𝓦 ̇ )
          → is-decidable (x ∈ ls) → 𝓦 ̇
scope-l1 x ls A r = A (+→𝟚 r)

scope-l1-prop : (x : Secret) → (ls : List Secret) → (A : 𝟚 → 𝓦 ̇ )
          → is-prop (A ₀)
          → is-prop (A ₁)
          → (z : is-decidable (x ∈ ls)) → is-prop (scope-l1 x ls A z)
scope-l1-prop x ls A d1 d2 (inl _) = d1
scope-l1-prop x ls A d1 d2 (inr _) = d2


module BSet-scope (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where

 Lim : 𝓥 ̇  → 𝟚 → Set 𝓥
 Lim P ₀ = 𝟘
 Lim P ₁ = P

 limitPr : Secret → 𝓥 ̇  → Pred S×Msg 𝓥
 limitPr s P mp@(ls , msg) = scope-l1 s ls (Lim P) (s ∈? ls)

 limit : Secret → BSet 𝓥 → BSet 𝓥
 limit s bs .pr₁ mp = limitPr s (< bs > mp) mp
 limit s bs .pr₂ .pr₁ mp@(ls , msg) = scope-l1-prop s ls (Lim (< bs > mp)) 𝟘-is-prop ((bset-is-prop bs) (ls , msg)) (s ∈? ls)
 limit s bs .pr₂ .pr₂ = λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
   l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈  scrs)) → scope-l1 s ascrs (Lim (< bs > (ascrs , x))) deq → scope-l1 s scrs (Lim (< bs > (scrs , x))) deq2
   l1 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq2))
   l1 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond

   l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Lim (< bs > (scrs , x))) deq → scope-l1 s ascrs (Lim (< bs > (ascrs , x))) deq2
   l2 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq2))
   l2 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond

 limitMPr : Secret → List Secret → 𝓥 ̇  → Pred S×Msg 𝓥
 limitMPr s [] bs mp = limitPr s bs mp
 limitMPr s (l ∷ ls) w mp = let w2 = limitPr s w mp
                                w3 = limitMPr l ls w2 mp
                            in w3

 limitPr-𝟘 : ∀ s mp → limitPr {𝓥} s 𝟘 mp ＝ 𝟘
 limitPr-𝟘 s  mp@(scr , _) with (s ∈? scr)
 ... | inl x = refl
 ... | inr x = refl
 
 limitMPr-𝟘 : ∀ s ls mp → limitMPr {𝓥} s ls 𝟘 mp ＝ 𝟘
 limitMPr-𝟘 s [] mp@(scr , _) = limitPr-𝟘 s mp
 limitMPr-𝟘 s (l ∷ ls) mp = ap (λ z → limitMPr l ls z mp) (limitPr-𝟘 s mp) ∙ limitMPr-𝟘 l ls mp

 limitM : Secret → List Secret → BSet 𝓥 → BSet 𝓥
 limitM s ls bs .pr₁ mp = limitMPr s ls (< bs > mp) mp
 limitM s [] bs .pr₂ = limit s bs .pr₂
 limitM s (l ∷ ls) bs .pr₂ = limitM l ls (limit s bs) .pr₂

 limitM' : List Secret → BSet 𝓥 → BSet 𝓥
 limitM' [] bs = bs
 limitM' (s ∷ ls) bs = limitM s ls bs

-- limitM×' is a restriction, so it fits where bs fits.
 lim-rec : ∀{𝓦} → {A : 𝓦 ̇ } → ∀ s ls {bs mp} → < (limitM {𝓥} s ls bs) > mp → (< bs > mp → A) → A
 lim-rec s [] {bs} {mp@(ws , msg)} c f = l1 (s ∈? ws) c where
  l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
       Lim (< bs > (ws , msg)) (+→𝟚 w) → _
  l1 (inr _) c = f c

 lim-rec {𝓥 = 𝓥} s (l ∷ ls) {bs} {mp@(ws , msg)} c f = l1 (s ∈? ws) c where
  l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
       limitMPr l ls (Lim (< bs > (ws , msg)) (+→𝟚 w)) (ws , msg) → _
  l1 (inl x) c with limitMPr {𝓥} l ls 𝟘 mp | (limitMPr-𝟘 {𝓥} l ls mp)
  l1 (inl x) () | r | refl
  l1 (inr x) c = lim-rec l ls {bs} {mp} c f


 lim-rec' : ∀{𝓦} → {A : 𝓦 ̇ } → ∀ ls bs {mp} → < (limitM' {𝓥} ls bs) > mp → (< bs > mp → A) → A
 lim-rec' [] _ c f = f c
 lim-rec' (x ∷ ls) bs {mp} = lim-rec x ls {bs}


--  module &PSet-scope {𝓥} where

--   open &PSet (𝟚 × ×BSet 𝓥) pt

--   limit&P : Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
--   &⟨ limit&P s ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , limit s bs) (restr &⟨ ps ⟩ x)
--   limit&P s ps .&-is-prop _ = ∃-is-prop
 
--   compl&P : Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
--   &⟨ compl&P s ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , compl s bs) (restr &⟨ ps ⟩ x)
--   compl&P s ps .&-is-prop v = ∃-is-prop
 
--   split&P : Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) × &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
--   split&P s ps =  limit&P s ps , compl&P s ps
 
--   limit&PM : Secret → List Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
--   &⟨ limit&PM s ls ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , limitM× s ls bs) (restr &⟨ ps ⟩ x)
--   limit&PM s ls ps .&-is-prop _ = ∃-is-prop
 
--   compl&PM : Secret → List Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
--   &⟨ compl&PM s ls ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , complM× s ls bs) (restr &⟨ ps ⟩ x)
--   compl&PM s ls ps .&-is-prop v = ∃-is-prop
 
--   split&PM : Secret → List Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) × &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
--   split&PM s ls ps = limit&PM s ls ps , compl&PM s ls ps


-- -- The product here has semantic meaning, the first is the external reducibility type,
-- -- the second is the internal reducibility type.

-- module PSet-scope (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) {𝓥} {𝓦} where

--  open &PSet (𝟚 × ×BSet 𝓥) pt
--  open BSet-scope _∈?_
--  open &PSet-scope {𝓥}

-- -- left is external
-- -- right is internal
--  open PSet pt (&PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) × &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦))
 
 
--  scopeP : Secret → PSet 𝓣 → PSet (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
--  -- Again here we use the _&_operator on inn.
--  -- I think we need to simplify this
--  ∣⟨ scopeP s ps ⟩ v = v ∈image ((λ (ex , inn) → limit&P s ex , (inn &-&ᵖ compl&P s ex)) ∘ restr ∣⟨ ps ⟩)
--  scopeP s ps .∣-is-prop v = ∃-is-prop

--  scopePM : List Secret → PSet (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣) → PSet (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
--  -- Again here we use the _&_operator on inn.
--  -- I think we need to simplify this
--  ∣⟨ scopePM [] ps ⟩ = ∣⟨ ps ⟩
--  ∣⟨ scopePM (s ∷ ls) ps ⟩ v = v ∈image ((λ (ex , inn) → limit&PM s ls ex , (inn &-&ᵖ compl&PM s ls ex)) ∘ restr ∣⟨ ps ⟩)
--  scopePM [] ps .∣-is-prop = ps .∣-is-prop
--  scopePM (s ∷ ls) ps .∣-is-prop v = ∃-is-prop






-- ```
