{-# OPTIONS --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan hiding (rec)
open import MLTT.List
open import MLTT.Maybe
open import MLTT.Bool as B
open import MLTT.Vector
open import UF.Subsingletons
open import Naturals.Order
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Notation.General
open import UF.Sets
open import UF.Base
open import UF.Embeddings
open import MLTT.Two renaming (₀ to 𝕞 ; ₁ to 𝕒)
import UF.ImageAndSurjection
open import Quotient.Type

open import Free
open import Common

module Sheaf (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓥 ̇) where

open PropositionalTruncation pt
open UF.ImageAndSurjection pt
open import BSet fe pt Msg

open BSet

module _ where
 open icomm-sgroup
 
 -- This will be used to project to OSet
 bool-icring : icring {𝓤 = 𝓤}
 icring.E bool-icring = ^ Bool
 pr₁ (pr₁ (icring.str bool-icring)) (a ̂ ) (b ̂ ) = (B._||_ a b ) ̂ 
 pr₂ (pr₁ (icring.str bool-icring)) = false ̂
 pr₂ (icring.str bool-icring) (a ̂ ) (b ̂ ) = (B._||_ a b ) ̂
 pr₁ (pr₁ (pr₁ (icring.ax bool-icring))) (true ̂) (x ̂) (x₁ ̂) = refl
 pr₁ (pr₁ (pr₁ (icring.ax bool-icring))) (false ̂) (x ̂) (x₁ ̂) = refl
 pr₁ (pr₂ (pr₁ (pr₁ (icring.ax bool-icring)))) (true ̂) = refl
 pr₁ (pr₂ (pr₁ (pr₁ (icring.ax bool-icring)))) (false ̂) = refl
 pr₂ (pr₂ (pr₁ (pr₁ (icring.ax bool-icring)))) (true ̂) = refl
 pr₂ (pr₂ (pr₁ (pr₁ (icring.ax bool-icring)))) (false ̂) = refl
 pr₁ (pr₂ (pr₁ (icring.ax bool-icring))) (true ̂) (true ̂) = refl
 pr₁ (pr₂ (pr₁ (icring.ax bool-icring))) (true ̂) (false ̂) = refl
 pr₁ (pr₂ (pr₁ (icring.ax bool-icring))) (false ̂) (true ̂) = refl
 pr₁ (pr₂ (pr₁ (icring.ax bool-icring))) (false ̂) (false ̂) = refl
 pr₂ (pr₂ (pr₁ (icring.ax bool-icring))) (true ̂) = refl
 pr₂ (pr₂ (pr₁ (icring.ax bool-icring))) (false ̂) = refl
 pr₁ (pr₁ (pr₂ (icring.ax bool-icring))) (true ̂) (x ̂) (x₁ ̂) = refl
 pr₁ (pr₁ (pr₂ (icring.ax bool-icring))) (false ̂) (x ̂) (x₁ ̂) = refl
 pr₂ (pr₁ (pr₂ (icring.ax bool-icring))) (true ̂) (true ̂) = refl
 pr₂ (pr₁ (pr₂ (icring.ax bool-icring))) (true ̂) (false ̂) = refl
 pr₂ (pr₁ (pr₂ (icring.ax bool-icring))) (false ̂) (true ̂) = refl
 pr₂ (pr₁ (pr₂ (icring.ax bool-icring))) (false ̂) (false ̂) = refl
 pr₂ (pr₂ (icring.ax bool-icring)) (true ̂) (x₁ ̂) (x₂ ̂) = refl
 pr₂ (pr₂ (icring.ax bool-icring)) (false ̂) (x₁ ̂) (x₂ ̂) = refl

 boolComm : icommonoid {𝓤 = 𝓤}
 boolComm = icring-is-icommonoid bool-icring

OSet : ∀ 𝓤 → (𝓤 ⁺) ⊔ (𝓥 ⁺) ̇
OSet 𝓤 = free-icring {𝓤 = 𝓤} (𝟚 × BSet)

module OSet {𝓤} (r : OSet 𝓤) = free-icring r

module _ {𝓤} where

 private
  module cB = icring {𝓤 = 𝓤} bool-icring

 `o : (msg : 𝟚 × Msg) → 𝟚 × BSet → cB.E
 `o (𝕞 , msg) (𝕞 , bset) = dec→bool (bset . -is-decidable msg)
 `o (𝕞 , pr₄) (𝕒 , pr₆) = false ̂
 `o (𝕒 , pr₄) (𝕞 , pr₆) = false ̂
 `o (𝕒 , msg) (𝕒 , bset) = dec→bool (bset . -is-decidable msg)

module fO→B {𝓤} (o : OSet 𝓤) (msg : 𝟚 × Msg) where

 private
  module O = OSet o

 !fO→B : ∃! (O.free-ringΔ bool-icring (`o msg))
 !fO→B = O.univ bool-icring (`o msg)

 fO→B = pr₁ (pr₁ !fO→B)

module _ (d : icommonoid {𝓤 = 𝓤}) where

 open icommonoid d

 dFun : ^ {𝓤 = 𝓤} Bool → 𝓤 ̇
 dFun (true ̂) = E
 dFun (false ̂) = 𝟙


 mgroup : icommonoid {𝓤 = 𝓤}
 icommonoid.E mgroup = Σ dFun
 pr₁ (icommonoid.str mgroup) ((true ̂) , a) ((true ̂) , b) = true ̂  , (a * b)
 pr₁ (icommonoid.str mgroup) a@((true ̂) , _) ((false ̂) , pr₆) = a
 pr₁ (icommonoid.str mgroup) ((false ̂) , pr₄) b = b
 pr₂ (icommonoid.str mgroup) = (false ̂) , ⋆
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((true ̂) , pr₄) ((true ̂) , pr₅) ((true ̂) , pr₇) = ap (λ x → true ̂  , x) (*-assoc _ _ _)
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((true ̂) , pr₄) ((true ̂) , pr₅) ((false ̂) , pr₇) = refl
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((true ̂) , pr₄) ((false ̂) , pr₅) ((true ̂) , pr₇) = refl
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((true ̂) , pr₄) ((false ̂) , pr₅) ((false ̂) , pr₇) = refl
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((false ̂) , pr₄) ((true ̂) , pr₅) ((true ̂) , pr₇) = refl
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((false ̂) , pr₄) ((true ̂) , pr₅) ((false ̂) , pr₇) = refl
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((false ̂) , pr₄) ((false ̂) , pr₅) ((true ̂) , pr₇) = refl
 pr₁ (pr₁ (icommonoid.ax mgroup)) ((false ̂) , pr₄) ((false ̂) , pr₅) ((false ̂) , pr₇) = refl
 pr₁ (pr₂ (pr₁ (icommonoid.ax mgroup))) ((true ̂) , pr₄) = refl
 pr₁ (pr₂ (pr₁ (icommonoid.ax mgroup))) ((false ̂) , pr₄) = refl
 pr₂ (pr₂ (pr₁ (icommonoid.ax mgroup))) ((true ̂) , pr₄) = refl
 pr₂ (pr₂ (pr₁ (icommonoid.ax mgroup))) ((false ̂) , pr₄) = refl
 pr₁ (pr₂ (icommonoid.ax mgroup)) (true ̂  , a) (true ̂  , b) = ap (λ x → true ̂  , x) (*-comm _ _)
 pr₁ (pr₂ (icommonoid.ax mgroup)) ((true ̂) , a) ((false ̂) , b) = refl
 pr₁ (pr₂ (icommonoid.ax mgroup)) ((false ̂) , a) ((true ̂) , b) = refl
 pr₁ (pr₂ (icommonoid.ax mgroup)) ((false ̂) , a) ((false ̂) , b) = refl
 pr₂ (pr₂ (icommonoid.ax mgroup)) ((true ̂) , pr₄) = ap (λ x → (true ̂) , x) (*-idem _)
 pr₂ (pr₂ (icommonoid.ax mgroup)) ((false ̂) , pr₄) = refl

record ParticleT (D : 𝓦 ̇ ) : 𝓥 ⁺ ⊔ 𝓦 ̇  where
 field
  dom : 𝟚 × BSet
  fun : (mp : 𝟚 × Msg) → { `o {𝓤 = 𝓦} mp dom ＝ true ̂ } → D

module _ (d : icommonoid {𝓤 = 𝓤}) where

 Sheaf : 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
 Sheaf = free-icommonoid {𝓤 = 𝓤} (ParticleT (icommonoid.E d))

 module Sheaf (s : Sheaf) = free-icommonoid s

module BPred (d : icommonoid {𝓤 = 𝓤}) (s : Sheaf d) (msg : 𝟚 × Msg) where

 private
  module Sh = Sheaf d s
  module D = icommonoid d
  module cB = icommonoid {𝓤 = 𝓤} boolComm

 open BSet
 open ParticleT

 `b_ : ParticleT D.E → cB.E
 `b p = `o msg (dom p)


 !fS→B : ∃! (Sh.freeΔ (icommonoid-is-monoid boolComm) `b_)
 !fS→B = Sh.univ (icommonoid-is-monoid boolComm) `b_

 fS→B = pr₁ (pr₁ !fS→B)


 tt : ParticleT D.E → 𝟚 × BSet
 tt p = dom p

 module _ (o : OSet 𝓤) where
  open fO→B o msg
  private
   module O = OSet o

  !fS→O : ∃! (Sh.freeΔ (icommonoid-is-monoid (icring-is-icommonoid O.r)) (O.`_ ∘ tt))
  !fS→O = Sh.univ (icommonoid-is-monoid (icring-is-icommonoid O.r)) (O.`_ ∘ tt)

  fS→O = pr₁ (pr₁ !fS→O)

  fw1 : `o msg ∘ tt ＝ `b_
  fw1 = refl

  fw2 : fO→B ∘ fS→O ∘ Sh.`_ ＝ `b_
  fw2 =  ap (fO→B ∘_) ((pr₂ (pr₂ (pr₁ !fS→O)))) ∙ (ap (_∘ tt) (pr₂ (pr₂ (pr₂ (pr₁ !fO→B)))))

  private
   module Q = monoid-homomorphism (icommonoid-is-monoid (icring-is-icommonoid O.r)) (icommonoid-is-monoid boolComm)
   module W = monoid-homomorphism (icommonoid-is-monoid Sh.r) (icommonoid-is-monoid (icring-is-icommonoid O.r))
   module T = monoid-homomorphism (icommonoid-is-monoid Sh.r) (icommonoid-is-monoid boolComm)

  open monoid-homomorphism-trans (icommonoid-is-monoid Sh.r) (icommonoid-is-monoid (icring-is-icommonoid O.r)) (icommonoid-is-monoid boolComm)
  
  fw3 : (fO→B ∘ fS→O) T.is-hom
  fw3 = trans-hom fO→B (pr₁ (pr₂ (pr₁ !fO→B))) fS→O ((pr₁ (pr₂ (pr₁ !fS→O))))
  
  fw : fO→B ∘ fS→O ＝ fS→B
  fw = ap pr₁ (pr₂ !fS→B (_ , (fw3 , fw2))) ⁻¹

-----------------------
-- TODO
-----------------------

module _ (d : icommonoid {𝓤 = 𝓤}) (s : Sheaf d) (msg : 𝟚 × Msg) where

 open BPred d s msg
 private
  module S = Sheaf d s
  module D = icommonoid d
  module cB = icommonoid {𝓤 = 𝓤} boolComm
  module M = icommonoid {𝓤 = 𝓤} (mgroup d)

 open BSet
 open ParticleT

------------------------------------------
 `md_ : ParticleT D.E → M.E
 `md p with `o {𝓤 = 𝓤} msg (dom p) | fun p msg 
 ... | true ̂  | f = true ̂  , f {refl}
 ... | false ̂  | f = false ̂  , ⋆
------------------------------------------

 !fS→M : ∃! (S.freeΔ (icommonoid-is-monoid (mgroup d)) `md_)
 !fS→M = S.univ (icommonoid-is-monoid (mgroup d)) `md_

 fS→M = pr₁ (pr₁ !fS→M)

 ee : pr₁ ∘ `md_ ∼ `b_
 ee p with `o {𝓤 = 𝓤} msg (dom p) | fun p msg 
 ... | true ̂ | q = refl
 ... | false ̂ | q = refl

 ee2 : pr₁ ∘ `md_ ＝ `b_
 ee2 = dfunext fe ee

 module _ where
  open monoid-homomorphism (icommonoid-is-monoid (mgroup d)) (icommonoid-is-monoid boolComm)

  pr-is-hom : pr₁ is-hom
  (pr₁ pr-is-hom) ((true ̂) , _) ((true ̂) , _) = refl
  (pr₁ pr-is-hom) ((true ̂) , _) ((false ̂) , _) = refl
  (pr₁ pr-is-hom) ((false ̂) , _) ((x ̂) , _) = refl
  (pr₂ pr-is-hom) = refl
  
 module _ where
  open monoid-homomorphism (icommonoid-is-monoid S.r) (icommonoid-is-monoid boolComm)

  qq : (pr₁ ∘ fS→M) is-hom
  pr₁ qq a b = ap pr₁ (pr₁ (pr₁ (pr₂ (pr₁ !fS→M))) a b) ∙ pr₁ pr-is-hom _ _
  pr₂ qq = ap pr₁ (pr₂ (pr₁ (pr₂ (pr₁ !fS→M)))) ∙ pr₂ pr-is-hom

  aa : pr₁ ∘ fS→M ∘ S.`_ ＝ `b_
  aa = ap (pr₁ ∘_) (pr₂ (pr₂ (pr₁ !fS→M))) ∙ ee2

 rr : pr₁ ∘ fS→M ＝ fS→B
 rr = ap pr₁ (pr₂ !fS→B (_ , (qq , aa))) ⁻¹

------------------------------
 f : (e : S.E) → fS→B e ＝ true ̂  → D.E
 f e eq = transport (dFun d) (happly rr e ∙ eq) (pr₂ (fS→M e))
-------------------------------
