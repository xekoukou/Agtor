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

open import Lists
open import Maybe

module Scope (fe : Fun-Ext) (pt : propositional-truncations-exist) (UA : Univalence) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) (s-is-set : is-set Secret) (dec : (a b : Secret) → is-decidable (a ＝ b)) where

open PropositionalTruncation pt

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

 limitP : Secret → BPred → BPred
 limitP s pred mp@(ls , msg) = scope-l1 s ls (Lim pred mp) (s ∈? ls)
 
 limit' : Secret → BSet' → BSet'
 limit' s bs .pr₁ = limitP s ⟨ bs ⟩'
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

 complP : Secret → BPred → BPred
 complP s pred mp@(ls , msg) = scope-l1 s ls (Compl pred mp) (s ∈? ls)
 
 compl' : Secret → BSet' → BSet'
 compl' s bs .pr₁ = complP s ⟨ bs ⟩'
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
 splitPr s bs = limitP s bs , complP s bs

 split : Secret → ×BSet → ×BSet × ×BSet
 split s bs = limit s bs , compl s bs


 splitLMPr : Secret → List Secret → BPred → BPred
 splitLMPr s [] bs = limitP s bs
 splitLMPr s (l ∷ ls) w = let w2 = limitP s w
                              w3 = splitLMPr l ls w2
                           in w3

 splitLM' : Secret → List Secret → BSet' → BSet'
 splitLM' s ls bs .pr₁ = splitLMPr s ls ⟨ bs ⟩'
 splitLM' s [] bs .pr₂ = limit' s bs .pr₂
 splitLM' s (l ∷ ls) bs .pr₂ = splitLM' l ls (limit' s bs) .pr₂


 splitLM× : Secret → List Secret → ×BSet → ×BSet
 splitLM× s ls bs .pr₁ .pr₁ = splitLMPr s ls ⟨ bs bset ⟩'
 splitLM× s ls bs .pr₁ .pr₂ = splitLM' s ls (bs bset) .pr₂
 splitLM× s [] bs .pr₂ = limit s bs .pr₂
 splitLM× s (l ∷ ls) bs .pr₂ = splitLM× l ls (limit s bs) .pr₂

-- This is the same as before but the properties are mixed with the structure.
 splitLM : Secret → List Secret → ×BSet → ×BSet
 splitLM s [] bs = limit s bs
 splitLM s (l ∷ ls) w = let w2 = limit s w
                            w3 = splitLM l ls w2
                        in w3

 splitRMPr : Secret → List Secret → BPred → BPred
 splitRMPr s [] bs = complP s bs
 splitRMPr s (l ∷ ls) w = let (w2 , a) = splitPr s w
                              b = splitRMPr l ls w2
                           in (λ mp → ((a mp) × (b mp)) + (¬ ((a mp) × (b mp)) × (a mp + b mp)))

 splitRM' : Secret → List Secret → BSet' → BSet'
 splitRM' s ls bs .pr₁ = splitRMPr s ls ⟨ bs ⟩'
 splitRM' s [] bs .pr₂ = compl' s bs .pr₂
 splitRM' s (l ∷ ls) w .pr₂ = let w2 = limit' s w
                                  b = compl' s w
                                  c = splitRM' l ls w2
                               in (b ||' c) .pr₂ 


 splitRM× : Secret → List Secret → ×BSet → ×BSet
 splitRM× s ls bs .pr₁ .pr₁ = splitRMPr s ls ⟨ bs bset ⟩'
 splitRM× s ls bs .pr₁ .pr₂ = splitRM' s ls (bs bset) .pr₂
 splitRM× s [] w .pr₂ = compl s w .pr₂
 splitRM× s (l ∷ ls) w .pr₂ = let w2 = limit s w
                                  b = compl s w
                                  c = splitRM× l ls w2
                              in (b ×|| c) .pr₂



-- This is the previous version , equal to the above.
 splitRM : Secret → List Secret → ×BSet → ×BSet
 splitRM s [] bs = compl s bs
 splitRM s (l ∷ ls) w = let (w2 , b) = split s w
                            c = splitRM l ls w2
                        in (b ×|| c)  

 
 splitM : Secret → List Secret → ×BSet → ×BSet × ×BSet
 splitM s ls bs = splitLM s ls bs , splitRM s ls bs
 



 limit&P : Secret → &PSet → &PSet
 &⟨ limit&P s ps ⟩ v = ∥ Σ o ꞉ 𝟚 × ×BSet , &⟨ ps ⟩ o × (o .pr₁ , limit s (o .pr₂) ＝ v) ∥
 limit&P s ps .&-is-prop _ = ∥∥-is-prop

 compl&P : Secret → &PSet → &PSet
 &⟨ compl&P s ps ⟩ = {!!}
 compl&P s ps .&-is-prop = {!!}

 split&P : Secret → &PSet → &PSet × &PSet
 &⟨ split&P s ps .pr₁ ⟩ v = ∥ Σ o ꞉ 𝟚 × ×BSet , &⟨ ps ⟩ o × ((o .pr₁ , split s (pr₂ o) .pr₁) ＝ v) ∥
 split&P s ps .pr₁ .&-is-prop o = ∥∥-is-prop
 &⟨ split&P s ps .pr₂ ⟩ v = ∥ Σ o ꞉ 𝟚 × ×BSet , &⟨ ps ⟩ o × ((o .pr₁ , split s (pr₂ o) .pr₂) ＝ v) ∥
 split&P s ps .pr₂ .&-is-prop o = ∥∥-is-prop
 
 split&PM : Secret → List Secret → &PSet → &PSet × &PSet
 &⟨ split&PM s ls ps .pr₁ ⟩ v = ∥ Σ o ꞉ 𝟚 × ×BSet , &⟨ ps ⟩ o × ((o .pr₁ , splitLM s ls (pr₂ o)) ＝ v) ∥
 split&PM s ls ps .pr₁ .&-is-prop o = ∥∥-is-prop
 &⟨ split&PM s ls ps .pr₂ ⟩ v = ∥ Σ o ꞉ 𝟚 × ×BSet , &⟨ ps ⟩ o × ((o .pr₁ , splitRM s ls (pr₂ o)) ＝ v) ∥
 split&PM s ls ps .pr₂ .&-is-prop o = ∥∥-is-prop
 
 
 splitP : Secret → PSet → PSet × PSet
 ∣⟨ splitP s ps .pr₁ ⟩ v = ∥ Σ o ꞉ &PSet , split&P s o .pr₁ ＝ v ∥
 splitP s ps .pr₁ .∣-is-prop o = ∥∥-is-prop
 ∣⟨ splitP s ps .pr₂ ⟩ v = ∥ Σ o ꞉ &PSet , split&P s o .pr₂ ＝ v ∥
 splitP s ps .pr₂ .∣-is-prop o = ∥∥-is-prop
 
 splitPM : Secret → List Secret → PSet → PSet × PSet
 ∣⟨ splitPM s ls ps .pr₁ ⟩ v = ∥ Σ o ꞉ &PSet , split&PM s ls o .pr₁ ＝ v ∥
 splitPM s ls ps .pr₁ .∣-is-prop o = ∥∥-is-prop
 ∣⟨ splitPM s ls ps .pr₂ ⟩ v = ∥ Σ o ꞉ &PSet , split&PM s ls o .pr₂ ＝ v ∥
 splitPM s ls ps .pr₂ .∣-is-prop o = ∥∥-is-prop
 
