{-# OPTIONS --without-K --exact-split #-}

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

module Scope (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (s-is-set : is-set Secret) (dec : (a b : Secret) → is-decidable (a ＝ b)) where

open PropositionalTruncation pt
open UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret s-is-set dec



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

 Lim : 𝓤 ̇  → 𝟚 → Set 𝓤
 Lim P ₀ = 𝟘
 Lim P ₁ = P

 limitPr : Secret → 𝓤 ̇  → BPred
 limitPr s P mp@(ls , msg) = scope-l1 s ls (Lim P) (s ∈? ls)

 limit' : Secret → BSet' → BSet'
 limit' s bs .pr₁ mp = limitPr s (⟨ bs ⟩' mp) mp
 limit' s bs .pr₂ mp@(ls , msg) = scope-l1-prop s ls (Lim (⟨ bs ⟩' mp)) 𝟘-is-prop ((bs is-prop') (ls , msg)) (s ∈? ls)

 limit : Secret → ×BSet → ×BSet
 limit s bs = limit' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
  l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈  scrs)) → scope-l1 s ascrs (Lim (⟨ bs bset ⟩' (ascrs , x))) deq → scope-l1 s scrs (Lim (⟨ bs bset ⟩' (scrs , x))) deq2
  l1 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq2))
  l1 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond

  l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Lim (⟨ bs bset ⟩' (scrs , x))) deq → scope-l1 s ascrs (Lim (⟨ bs bset ⟩' (ascrs , x))) deq2
  l2 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq2))
  l2 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond


 Compl : 𝓤 ̇  → 𝟚 → Set 𝓤
 Compl pred ₀ = pred
 Compl pred ₁ = 𝟘

 complPr : Secret → 𝓤 ̇  → BPred
 complPr s P mp@(ls , msg) = scope-l1 s ls (Compl P) (s ∈? ls)
 
 compl' : Secret → BSet' → BSet'
 compl' s bs .pr₁ mp = complPr s (⟨ bs ⟩' mp) mp
 compl' s bs .pr₂ mp@(ls , msg) = scope-l1-prop s ls (Compl (⟨ bs ⟩' mp)) ((bs is-prop') (ls , msg)) 𝟘-is-prop (s ∈? ls)



 compl : Secret → ×BSet → ×BSet
 compl s bs = compl' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
  l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈ scrs)) → scope-l1 s ascrs (Compl (⟨ bs bset ⟩' (ascrs , x))) deq → scope-l1 s scrs (Compl (⟨ bs bset ⟩' (scrs , x))) deq2
  l1 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond
  l1 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq))

  l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Compl (⟨ bs bset ⟩' (scrs , x))) deq → scope-l1 s ascrs (Compl (⟨ bs bset ⟩' (ascrs , x))) deq2
  l2 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond
  l2 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq))



-- TODO I believe there is a better way here, since most of this is redundant.

 splitPr : Secret → BPred → BPred × BPred
 splitPr s bs = (λ mp → limitPr s (bs mp) mp) , λ mp → complPr s (bs mp) mp

 split : Secret → ×BSet → ×BSet × ×BSet
 split s bs = limit s bs , compl s bs

 limitMPr : Secret → List Secret → 𝓤 ̇  → BPred
 limitMPr s [] bs mp = limitPr s bs mp
 limitMPr s (l ∷ ls) w mp = let w2 = limitPr s w mp
                                w3 = limitMPr l ls w2 mp
                            in w3

 limitPr-𝟘 : ∀ s mp → limitPr s 𝟘 mp ＝ 𝟘
 limitPr-𝟘 s  mp@(scr , _) with (s ∈? scr)
 ... | inl x = refl
 ... | inr x = refl
 
 limitMPr-𝟘 : ∀ s ls mp → limitMPr s ls 𝟘 mp ＝ 𝟘
 limitMPr-𝟘 s [] mp@(scr , _) = limitPr-𝟘 s mp
 limitMPr-𝟘 s (l ∷ ls) mp = ap (λ z → limitMPr l ls z mp) (limitPr-𝟘 s mp) ∙ limitMPr-𝟘 l ls mp

 limitM' : Secret → List Secret → BSet' → BSet'
 limitM' s ls bs .pr₁ mp = limitMPr s ls (⟨ bs ⟩' mp) mp
 limitM' s [] bs .pr₂ = limit' s bs .pr₂
 limitM' s (l ∷ ls) bs .pr₂ = limitM' l ls (limit' s bs) .pr₂


 limitM× : Secret → List Secret → ×BSet → ×BSet
 limitM× s ls bs .pr₁ .pr₁ mp = limitMPr s ls (⟨ bs bset ⟩' mp) mp
 limitM× s ls bs .pr₁ .pr₂ = limitM' s ls (bs bset) .pr₂
 limitM× s [] bs .pr₂ = limit s bs .pr₂
 limitM× s (l ∷ ls) bs .pr₂ = limitM× l ls (limit s bs) .pr₂

 complMPr : Secret → List Secret → BPred → BPred
 complMPr s [] bs mp = complPr s (bs mp) mp
 complMPr s (l ∷ ls) w = let (w2 , a) = splitPr s w
                             b = complMPr l ls w2
                         in (λ mp → ((a mp) × (b mp)) + (¬ ((a mp) × (b mp)) × (a mp + b mp)))

 complM' : Secret → List Secret → BSet' → BSet'
 complM' s ls bs .pr₁ = complMPr s ls ⟨ bs ⟩'
 complM' s [] bs .pr₂ = compl' s bs .pr₂
 complM' s (l ∷ ls) w .pr₂ = let w2 = limit' s w
                                 b = compl' s w
                                 c = complM' l ls w2
                             in (b ||' c) .pr₂ 


 complM× : Secret → List Secret → ×BSet → ×BSet
 complM× s ls bs .pr₁ .pr₁ = complMPr s ls ⟨ bs bset ⟩'
 complM× s ls bs .pr₁ .pr₂ = complM' s ls (bs bset) .pr₂
 complM× s [] w .pr₂ = compl s w .pr₂
 complM× s (l ∷ ls) w .pr₂ = let w2 = limit s w
                                 b = compl s w
                                 c = complM× l ls w2
                             in (b ×|| c) .pr₂


 
 splitM× : Secret → List Secret → ×BSet → ×BSet × ×BSet
 splitM× s ls bs = limitM× s ls bs , complM× s ls bs
 


 module &PSet-scope where

  open &PSet (𝟚 × ×BSet) pt

  limit&P : Secret → &PSet → &PSet
  &⟨ limit&P s ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , limit s bs) (restr &⟨ ps ⟩ x)
  limit&P s ps .&-is-prop _ = ∃-is-prop
 
  compl&P : Secret → &PSet → &PSet
  &⟨ compl&P s ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , compl s bs) (restr &⟨ ps ⟩ x)
  compl&P s ps .&-is-prop v = ∃-is-prop
 
  split&P : Secret → &PSet → &PSet × &PSet
  split&P s ps =  limit&P s ps , compl&P s ps
 
  limit&PM : Secret → List Secret → &PSet → &PSet
  &⟨ limit&PM s ls ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , limitM× s ls bs) (restr &⟨ ps ⟩ x)
  limit&PM s ls ps .&-is-prop _ = ∃-is-prop
 
  compl&PM : Secret → List Secret → &PSet → &PSet
  &⟨ compl&PM s ls ps ⟩ v = v ∈image λ x → (λ (a , bs) → a , complM× s ls bs) (restr &⟨ ps ⟩ x)
  compl&PM s ls ps .&-is-prop v = ∃-is-prop
 
  split&PM : Secret → List Secret → &PSet → &PSet × &PSet
  split&PM s ls ps = limit&PM s ls ps , compl&PM s ls ps


-- TODO Here we need to fix this!!!!
-- The product here has semantic meaning, the first is the external reducibility type,
-- the second is the internal reducibility type.

module PSet-scope (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where

 open &PSet (𝟚 × ×BSet) pt
 open ∈-dec _∈?_
 open &PSet-scope

-- left is external
-- right is internal
 open PSet pt (&PSet × &PSet)
 -- When we add two Q, we need to add both external and internal
 -- Internals cannot communicate with each other and we are interested in
 -- only one of them reducing, thus  _&_ seems an appropriate action.
 -- TODO replace it if not
 -- TODO We do not use it in this context, so maybe place it somewhere else.
      (λ (a1 , a2) (b1 , b2) → (a1 &-&ᵖ b1) , ((a2 &-&ᵖ b2)))
 
 
 scopeP : Secret → PSet → PSet
 -- Again here we use the _&_operator on inn.
 -- I think we need to simplify this
 ∣⟨ scopeP s ps ⟩ v = v ∈image ((λ (ex , inn) → limit&P s ex , (inn &-&ᵖ compl&P s ex)) ∘ restr ∣⟨ ps ⟩)
 scopeP s ps .∣-is-prop v = ∃-is-prop

 scopePM : List Secret → PSet → PSet
 -- Again here we use the _&_operator on inn.
 -- I think we need to simplify this
 ∣⟨ scopePM [] ps ⟩ = ∣⟨ ps ⟩
 ∣⟨ scopePM (s ∷ ls) ps ⟩ v = v ∈image ((λ (ex , inn) → limit&PM s ls ex , (inn &-&ᵖ compl&PM s ls ex)) ∘ restr ∣⟨ ps ⟩)
 scopePM [] ps .∣-is-prop = ps .∣-is-prop
 scopePM (s ∷ ls) ps .∣-is-prop v = ∃-is-prop
