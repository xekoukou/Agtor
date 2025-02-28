{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc


module FCP (A : 𝓤 ̇ ) 𝓥 C (B : 𝓦 ̇) where

open import PredP A

FC : 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺ ̇
FC = (Σ Mp ꞉ ΣPred 𝓥 C , let private module Mp = ΣPred Mp in (∀ x → Mp.type x → B)) × (Σ Ap ꞉ ΣPred 𝓥 C , let private module Ap = ΣPred Ap in (∀ x → Ap.type x → B))

module FC (fc : FC) where
 Mp : _
 Mp = fc .pr₁ .pr₁

 module Mp = ΣPred Mp

 fm : ∀ x → Mp.type x → B
 fm = fc .pr₁ .pr₂

 Ap : _
 Ap = fc .pr₂ .pr₁

 module Ap = ΣPred Ap

 fa : ∀ x → Ap.type x → B
 fa = fc .pr₂ .pr₂
