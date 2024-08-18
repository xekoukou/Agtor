{-# OPTIONS --safe --without-K --exact-split #-}

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
open import PSet fe pt S×Msg

open list-decidable dec

limitL-l1 : (x : Secret) → (ls : List Secret) → is-decidable (x ∈ ls) → Msg + Secret → (S×Msg → 𝓤 ̇ ) → 𝓤 ̇  → 𝓤 ̇
limitL-l1 x ls (inl x∈ls) msg B A = A
limitL-l1 x ls (inr ¬x∈ls) msg B A = B (ls , msg)

limitL' : Secret → BSet → BSet
⟨ limitL' s bs ⟩ mp@(ls , msg)
 = limitL-l1 s ls (s ∈? ls) msg ⟨ bs ⟩ 𝟘
limitL' s bs .-is-prop mp@(ls , msg) with (s ∈? ls)
... | inl x = 𝟘-is-prop
... | inr x = bs .-is-prop (ls , msg)

limitL : Secret → ×BSet → ×BSet
limitL s bs = limitL' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
 l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈ scrs)) → limitL-l1 s ascrs deq x BSet.⟨ bs bset ⟩ 𝟘 → limitL-l1 s scrs deq2 x BSet.⟨ bs bset ⟩ 𝟘
 l1 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq2))
 l1 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond

 l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → limitL-l1 s scrs deq x BSet.⟨ bs bset ⟩ 𝟘 → limitL-l1 s ascrs deq2 x BSet.⟨ bs bset ⟩ 𝟘
 l2 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq2))
 l2 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond



limitR-l1 : (x : Secret) → (ls : List Secret) → is-decidable (x ∈ ls) → Msg + Secret → (S×Msg → 𝓤 ̇ ) → 𝓤 ̇  → 𝓤 ̇
limitR-l1 x ls (inl x∈ls) msg B A = B (ls , msg)
limitR-l1 x ls (inr ¬x∈ls) msg B A = A

limitR' : Secret → BSet → BSet
⟨ limitR' s bs ⟩ mp@(ls , msg)
 = limitR-l1 s ls (s ∈? ls) msg ⟨ bs ⟩ 𝟘
limitR' s bs .-is-prop mp@(ls , msg) with (s ∈? ls)
... | inl x = bs .-is-prop (ls , msg)
... | inr x = 𝟘-is-prop

limitR : Secret → ×BSet → ×BSet
limitR s bs = limitR' s (bs bset) , λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
 l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈ scrs)) → limitR-l1 s ascrs deq x BSet.⟨ bs bset ⟩ 𝟘 → limitR-l1 s scrs deq2 x BSet.⟨ bs bset ⟩ 𝟘
 l1 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond
 l1 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq))

 l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → limitR-l1 s scrs deq x BSet.⟨ bs bset ⟩ 𝟘 → limitR-l1 s ascrs deq2 x BSet.⟨ bs bset ⟩ 𝟘
 l2 ascrs scrs x a⊃s a⊂s (inl eq1) (inl eq2) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond
 l2 ascrs scrs x a⊃s a⊂s (inl eq) (inr neq) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq))




split : Secret → ×BSet → ×BSet × ×BSet
split s bs = limitL s bs , limitR s bs
