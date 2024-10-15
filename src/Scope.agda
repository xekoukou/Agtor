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
import PSet
import &PSet

open import Lists
open import Maybe

module Scope (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) where

open PropositionalTruncation pt
open UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret



restr : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → (P : A → 𝓥 ̇ ) → Σ P → A
restr P x =  x .pr₁

_$₂_ : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → {B : 𝓥 ̇ } → (A → B) → A × A → B × B
f $₂ (a , b) = f a , f b

+→𝟚 : ∀{𝓤 𝓥} → {X : 𝓤 ̇ } → {Y : 𝓥 ̇ } → X + Y → 𝟚
+→𝟚 (inl x) = ₀
+→𝟚 (inr x) = ₁

scope-l1 : (x : Secret) → (ls : List Secret) → (A : 𝟚 → 𝓦 ̇ )
          → (z : is-decidable (x ∈ ls)) → 𝓦 ̇
scope-l1 x ls A r = A (+→𝟚 r)

scope-l1-prop : (x : Secret) → (ls : List Secret) → (A : 𝟚 → 𝓦 ̇ )
          → is-prop (A ₀)
          → is-prop (A ₁)
          → (z : is-decidable (x ∈ ls)) → is-prop (scope-l1 x ls A z)
scope-l1-prop x ls A d1 d2 (inl _) = d1
scope-l1-prop x ls A d1 d2 (inr _) = d2


module ∈-dec (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where

 Lim : 𝓥 ̇  → 𝟚 → Set 𝓥
 Lim P ₀ = 𝟘
 Lim P ₁ = P

 limitPr : Secret → 𝓥 ̇  → BPred 𝓥
 limitPr s P mp@(ls , msg) = scope-l1 s ls (Lim P) (s ∈? ls)

 limit' : Secret → BSet 𝓥 → BSet 𝓥
 limit' s bs .pr₁ mp = limitPr s (⟨ bs ⟩ mp) mp
 limit' s bs .pr₂ mp@(ls , msg) = scope-l1-prop s ls (Lim (⟨ bs ⟩ mp)) 𝟘-is-prop ((bset-is-prop bs) (ls , msg)) (s ∈? ls)

 limit : Secret → ×BSet 𝓥 → ×BSet 𝓥
 limit s bs = limit' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
  l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈  scrs)) → scope-l1 s ascrs (Lim (⟨ bs bset ⟩ (ascrs , x))) deq → scope-l1 s scrs (Lim (⟨ bs bset ⟩ (scrs , x))) deq2
  l1 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq2))
  l1 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond

  l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Lim (⟨ bs bset ⟩ (scrs , x))) deq → scope-l1 s ascrs (Lim (⟨ bs bset ⟩ (ascrs , x))) deq2
  l2 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq2))
  l2 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond


 Compl : 𝓥 ̇  → 𝟚 → Set 𝓥
 Compl pred ₀ = pred
 Compl pred ₁ = 𝟘

 complPr : Secret → 𝓥 ̇  → BPred 𝓥
 complPr s P mp@(ls , msg) = scope-l1 s ls (Compl P) (s ∈? ls)
 
 compl' : Secret → BSet 𝓥 → BSet 𝓥
 compl' s bs .pr₁ mp = complPr s (⟨ bs ⟩ mp) mp
 compl' s bs .pr₂ mp@(ls , msg) = scope-l1-prop s ls (Compl (⟨ bs ⟩ mp)) ((bset-is-prop bs) (ls , msg)) 𝟘-is-prop (s ∈? ls)



 compl : Secret → ×BSet 𝓥 → ×BSet 𝓥
 compl s bs = compl' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
  l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈ scrs)) → scope-l1 s ascrs (Compl (⟨ bs bset ⟩ (ascrs , x))) deq → scope-l1 s scrs (Compl (⟨ bs bset ⟩ (scrs , x))) deq2
  l1 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond
  l1 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq))

  l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Compl (⟨ bs bset ⟩ (scrs , x))) deq → scope-l1 s ascrs (Compl (⟨ bs bset ⟩ (ascrs , x))) deq2
  l2 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond
  l2 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq))


 splitPr : Secret → BPred 𝓥 → BPred 𝓥 × BPred 𝓥
 splitPr s bs = (λ mp → limitPr s (bs mp) mp) , λ mp → complPr s (bs mp) mp

 split : Secret → ×BSet 𝓥 → ×BSet 𝓥 × ×BSet 𝓥
 split s bs = limit s bs , compl s bs

 limitMPr : Secret → List Secret → 𝓥 ̇  → BPred 𝓥
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

 limitM' : Secret → List Secret → BSet 𝓥 → BSet 𝓥
 limitM' s ls bs .pr₁ mp = limitMPr s ls (⟨ bs ⟩ mp) mp
 limitM' s [] bs .pr₂ = limit' s bs .pr₂
 limitM' s (l ∷ ls) bs .pr₂ = limitM' l ls (limit' s bs) .pr₂



 limitM× : Secret → List Secret → ×BSet 𝓥 → ×BSet 𝓥
 limitM× s ls bs .pr₁ .pr₁ mp = limitMPr s ls (⟨ bs bset ⟩ mp) mp
 limitM× s ls bs .pr₁ .pr₂ = limitM' s ls (bs bset) .pr₂
 limitM× s [] bs .pr₂ = limit s bs .pr₂
 limitM× s (l ∷ ls) bs .pr₂ = limitM× l ls (limit s bs) .pr₂

 limitM×' : List Secret → ×BSet 𝓥 → ×BSet 𝓥
 limitM×' [] bs = bs
 limitM×' (s ∷ ls) bs = limitM× s ls bs

-- limitM×' is a restriction, so it fits where bs fits.
 lim-rec : {A : 𝓥 ̇ } → ∀ s ls {bs mp} → ⟨ (limitM× {𝓥} s ls bs) bset ⟩ mp → (⟨ bs bset ⟩ mp → A) → A
 lim-rec {𝓥} s [] {bs} {mp@(ws , msg)} c f = l1 (s ∈? ws) c where
  l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
       Lim (bs .pr₁ .pr₁ (ws , msg)) (+→𝟚 w) → _
  l1 (inr _) c = f c

 lim-rec {𝓥} s (l ∷ ls) {bs} {mp@(ws , msg)} c f = l1 (s ∈? ws) c where
  l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
       limitMPr l ls (Lim (bs .pr₁ .pr₁ (ws , msg)) (+→𝟚 w)) (ws , msg) → _
  l1 (inl x) c with limitMPr {𝓥} l ls 𝟘 mp | (limitMPr-𝟘 {𝓥} l ls mp)
  l1 (inl x) () | r | refl
  l1 (inr x) c = lim-rec l ls {bs} {mp} c f


 lim-rec' : {A : 𝓥 ̇ } → ∀ ls bs {mp} → ⟨ (limitM×' {𝓥} ls bs) bset ⟩ mp → (⟨ bs bset ⟩ mp → A) → A
 lim-rec' [] _ c f = f c
 lim-rec' (x ∷ ls) bs {mp} = lim-rec x ls {bs}


 complMPr : Secret → List Secret → BPred 𝓥 → BPred 𝓥
 complMPr s [] bs mp = complPr s (bs mp) mp
 complMPr s (l ∷ ls) w = let (w2 , a) = splitPr s w
                             b = complMPr l ls w2
                         in (λ mp → ∥ a mp + b mp ∥)

 complM' : Secret → List Secret → BSet 𝓥 → BSet 𝓥
 complM' s ls bs .pr₁ = complMPr s ls ⟨ bs ⟩
 complM' s [] bs .pr₂ = compl' s bs .pr₂
 complM' s (l ∷ ls) w .pr₂ = let w2 = limit' s w
                                 b = compl' s w
                                 c = complM' l ls w2
                             in (b || c) .pr₂ 


 complM× : Secret → List Secret → ×BSet 𝓥 → ×BSet 𝓥
 complM× s ls bs .pr₁ .pr₁ = complMPr s ls ⟨ bs bset ⟩
 complM× s ls bs .pr₁ .pr₂ = complM' s ls (bs bset) .pr₂
 complM× s [] w .pr₂ = compl s w .pr₂
 complM× s (l ∷ ls) w .pr₂ = let w2 = limit s w
                                 b = compl s w
                                 c = complM× l ls w2
                             in (b ×|| c) .pr₂


 
 splitM× : Secret → List Secret → ×BSet 𝓥 → ×BSet 𝓥 × ×BSet 𝓥
 splitM× s ls bs = limitM× s ls bs , complM× s ls bs
 


 module &PSet-scope {𝓥} where

  open &PSet (𝟚 × ×BSet 𝓥) pt

  limit&P : Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  &⟨ limit&P s ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , limit s bs) (restr &⟨ ps ⟩ x)
  limit&P s ps .&-is-prop _ = ∃-is-prop
 
  compl&P : Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  &⟨ compl&P s ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , compl s bs) (restr &⟨ ps ⟩ x)
  compl&P s ps .&-is-prop v = ∃-is-prop
 
  split&P : Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) × &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  split&P s ps =  limit&P s ps , compl&P s ps
 
  limit&PM : Secret → List Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  &⟨ limit&PM s ls ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , limitM× s ls bs) (restr &⟨ ps ⟩ x)
  limit&PM s ls ps .&-is-prop _ = ∃-is-prop
 
  compl&PM : Secret → List Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  &⟨ compl&PM s ls ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , complM× s ls bs) (restr &⟨ ps ⟩ x)
  compl&PM s ls ps .&-is-prop v = ∃-is-prop
 
  split&PM : Secret → List Secret → &PSet 𝓦 → &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) × &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  split&PM s ls ps = limit&PM s ls ps , compl&PM s ls ps


-- TODO Here we need to fix this!!!!
-- The product here has semantic meaning, the first is the external reducibility type,
-- the second is the internal reducibility type.

module PSet-scope {𝓥} {𝓦} (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where

 open &PSet (𝟚 × ×BSet 𝓥) pt
 open ∈-dec _∈?_
 open &PSet-scope {𝓥}

-- left is external
-- right is internal
 open PSet pt (&PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) × &PSet (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦))
 
 
 scopeP : Secret → PSet 𝓣 → PSet (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
 -- Again here we use the _&_operator on inn.
 -- I think we need to simplify this
 ∣⟨ scopeP s ps ⟩ v = v ∈image ((λ (ex , inn) → limit&P s ex , (inn &-&ᵖ compl&P s ex)) ∘ restr ∣⟨ ps ⟩)
 scopeP s ps .∣-is-prop v = ∃-is-prop

 scopePM : List Secret → PSet (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣) → PSet (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣)
 -- Again here we use the _&_operator on inn.
 -- I think we need to simplify this
 ∣⟨ scopePM [] ps ⟩ = ∣⟨ ps ⟩
 ∣⟨ scopePM (s ∷ ls) ps ⟩ v = v ∈image ((λ (ex , inn) → limit&PM s ls ex , (inn &-&ᵖ compl&PM s ls ex)) ∘ restr ∣⟨ ps ⟩)
 scopePM [] ps .∣-is-prop = ps .∣-is-prop
 scopePM (s ∷ ls) ps .∣-is-prop v = ∃-is-prop
