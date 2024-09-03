{-# OPTIONS --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
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
open import Maybe

module Scope (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (s-is-set : is-set Secret) (dec : (a b : Secret) → is-decidable (a ＝ b)) where

open PropositionalTruncation pt
open UF.ImageAndSurjection pt

open import xBSet fe pt Msg Secret s-is-set dec
open import PSet ×BSet fe pt Msg


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

 Lim : BPred → S×Msg → 𝟚 → Set 𝓤
 Lim pred mp ₀ = 𝟘
 Lim pred mp ₁ = pred mp

 Lim' : 𝓤 ̇  → 𝟚 → Set 𝓤
 Lim' P ₀ = 𝟘
 Lim' P ₁ = P

 limitPr : Secret → BPred → BPred
 limitPr s pred mp@(ls , msg) = scope-l1 s ls (Lim pred mp) (s ∈? ls)
 
 limitPr' : Secret → 𝓤 ̇  → BPred
 limitPr' s P mp@(ls , msg) = scope-l1 s ls (Lim' P) (s ∈? ls)

 limit' : Secret → BSet' → BSet'
 limit' s bs .pr₁ = limitPr s ⟨ bs ⟩'
 limit' s bs .pr₂ mp@(ls , msg) = scope-l1-prop s ls (Lim ⟨ bs ⟩' mp) 𝟘-is-prop ((bs is-prop') (ls , msg)) (s ∈? ls)

 limit : Secret → ×BSet → ×BSet
 limit s bs = limit' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
  l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈  scrs)) → scope-l1 s ascrs (Lim ⟨ bs bset ⟩' (ascrs , x)) deq → scope-l1 s scrs (Lim ⟨ bs bset ⟩' (scrs , x)) deq2
  l1 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq2))
  l1 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond

  l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Lim ⟨ bs bset ⟩' (scrs , x)) deq → scope-l1 s ascrs (Lim ⟨ bs bset ⟩' (ascrs , x)) deq2
  l2 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq2))
  l2 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond


 Compl : BPred → S×Msg → 𝟚 → Set 𝓤
 Compl pred mp ₀ = pred mp
 Compl pred mp ₁ = 𝟘

 complPr : Secret → BPred → BPred
 complPr s pred mp@(ls , msg) = scope-l1 s ls (Compl pred mp) (s ∈? ls)
 
 compl' : Secret → BSet' → BSet'
 compl' s bs .pr₁ = complPr s ⟨ bs ⟩'
 compl' s bs .pr₂ mp@(ls , msg) = scope-l1-prop s ls (Compl ⟨ bs ⟩' mp) ((bs is-prop') (ls , msg)) 𝟘-is-prop (s ∈? ls)



 compl : Secret → ×BSet → ×BSet
 compl s bs = compl' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
  l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈ scrs)) → scope-l1 s ascrs (Compl ⟨ bs bset ⟩' (ascrs , x)) deq → scope-l1 s scrs (Compl ⟨ bs bset ⟩' (scrs , x)) deq2
  l1 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond
  l1 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq))

  l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Compl ⟨ bs bset ⟩' (scrs , x)) deq → scope-l1 s ascrs (Compl ⟨ bs bset ⟩' (ascrs , x)) deq2
  l2 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond
  l2 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq))



-- TODO I believe there is a better way here, since most of this is redundant.

 splitPr : Secret → BPred → BPred × BPred
 splitPr s bs = limitPr s bs , complPr s bs

 split : Secret → ×BSet → ×BSet × ×BSet
 split s bs = limit s bs , compl s bs


 limitMPr : Secret → List Secret → BPred → BPred
 limitMPr s [] bs = limitPr s bs
 limitMPr s (l ∷ ls) w = let w2 = limitPr s w
                             w3 = limitMPr l ls w2
                         in w3

 limitMPr' : Secret → List Secret → 𝓤 ̇  → BPred
 limitMPr' s [] bs mp = limitPr' s bs mp
 limitMPr' s (l ∷ ls) bs mp = let w2 = limitPr' s bs mp
                                  w3 = limitMPr' l ls w2 mp
                              in w3

 limitM' : Secret → List Secret → BSet' → BSet'
 limitM' s ls bs .pr₁ = limitMPr s ls ⟨ bs ⟩'
 limitM' s [] bs .pr₂ = limit' s bs .pr₂
 limitM' s (l ∷ ls) bs .pr₂ = limitM' l ls (limit' s bs) .pr₂


 limitM× : Secret → List Secret → ×BSet → ×BSet
 limitM× s ls bs .pr₁ .pr₁ = limitMPr s ls ⟨ bs bset ⟩'
 limitM× s ls bs .pr₁ .pr₂ = limitM' s ls (bs bset) .pr₂
 limitM× s [] bs .pr₂ = limit s bs .pr₂
 limitM× s (l ∷ ls) bs .pr₂ = limitM× l ls (limit s bs) .pr₂

-- This is the same as before but the properties are mixed with the structure.
--  limitM : Secret → List Secret → ×BSet → ×BSet
--  limitM s [] bs = limit s bs
--  limitM s (l ∷ ls) w = let w2 = limit s w
--                            w3 = limitM l ls w2
--                        in w3

 complMPr : Secret → List Secret → BPred → BPred
 complMPr s [] bs = complPr s bs
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



-- This is the previous version , equal to the above.
--  complM : Secret → List Secret → ×BSet → ×BSet
--  complM s [] bs = compl s bs
--  complM s (l ∷ ls) w = let (w2 , b) = split s w
--                            c = complM l ls w2
--                        in (b ×|| c)  

 
 splitM× : Secret → List Secret → ×BSet → ×BSet × ×BSet
 splitM× s ls bs = limitM× s ls bs , complM× s ls bs
 

 restr : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → (P : A → 𝓥 ̇ ) → Σ P → A
 restr P x =  x .pr₁

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
 
 
 limitP : Secret → PSet → PSet
 ∣⟨ limitP s ps ⟩ v = v ∈image limit&P s
 limitP s ps .∣-is-prop v = ∃-is-prop

 complP : Secret → PSet → PSet
 ∣⟨ complP s ps ⟩ v = v ∈image compl&P s
 complP s ps .∣-is-prop v = ∃-is-prop

 splitP : Secret → PSet → PSet × PSet
 splitP s ps = (limitP s ps) , (complP s ps)

 limitPM : Secret → List Secret → PSet → PSet
 ∣⟨ limitPM s ls ps ⟩ v = v ∈image limit&PM s ls
 limitPM s ls ps .∣-is-prop v = ∃-is-prop

 complPM : Secret → List Secret → PSet → PSet
 ∣⟨ complPM s ls ps ⟩ v = v ∈image compl&PM s ls
 complPM s ls ps .∣-is-prop v = ∃-is-prop

 splitPM : Secret → List Secret → PSet → PSet × PSet
 splitPM s ls ps = (limitPM s ls ps) , (complPM s ls ps)
