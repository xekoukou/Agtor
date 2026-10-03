#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Potentiality Realization


#hide[
```agda
{-# OPTIONS --polarity --without-K --exact-split --cubical --guardedness #-}

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Base
open import UF.FunExt
import Cubical.Foundations.Prelude as Cube
```
]


```agda
open import PredP
open import Common-Rel

open Pred

module PotP-Rel (Msg : 𝓤 ̇ ) (Secret : 𝓤 ̇  ) 𝓥 𝓦 𝓣 where

open import Definitions Msg Secret

open import FCP Msg Secret 𝓥

open ΣPred
open import FunctorP
open import Final-CoAlgebraP
open import CoAlgebraP


open import PotP Msg Secret 𝓥 𝓦 𝓣
open Pot

open Functor Fpot

record PotR : 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇  where
 constructor ptRc
 coinductive
 field
  nextR : PotR
  psetR : PSet 𝓥 𝓦 𝓣
  focR : FC {B = PotR}
  
open PotR

open FC {B = PotR} renaming (Mp to Mpr ; fm to fmr ; Ap to Apr ; fa to far)


record PotEq (a b : PotR) : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇  where
 coinductive
 field
  nextEq : PotEq (nextR a) (nextR b)
  psetEq : psetR a ＝ psetR b
  focEq : (Σ eq ꞉ (Mpr (focR a) ＝ Mpr (focR b)) , (∀ x p → PotEq (fmr (focR a) x p) (fmr (focR b) x (transport (λ z → < z > x) eq p)))) × (Σ eq ꞉ (Apr (focR a) ＝ Apr (focR b)) , (∀ x p → PotEq (far (focR a) x p) (far (focR b) x (transport (λ z → < z > x) eq p))))

open PotEq




poteq-refl : ∀{a} → PotEq a a
poteq-refl .nextEq = poteq-refl
poteq-refl .psetEq = refl
poteq-refl {a} .focEq = (refl , (λ x p → poteq-refl)) , refl , λ x p → poteq-refl

{-# TERMINATING #-}
potEq→eq : ∀ a b → PotEq a b → a Cube.≡ b
potEq→eq a b peq i .nextR = potEq→eq _ _ (peq .nextEq) i
potEq→eq a b peq i .psetR = eqToPath (peq .psetEq) i
potEq→eq a b peq i .focR .pr₁ .pr₁ = eqToPath (peq .focEq .pr₁ .pr₁) i
potEq→eq a b peq i .focR .pr₁ .pr₂ m bs = gg where
  eq = eqToPath (peq .focEq .pr₁ .pr₁)
  bsa = Cube.transport (λ j → < eq ((Cube.~ j) Cube.∧ i) > m) bs
  fg = Cube.cong (λ z → fmr (focR b) m z) (substPath≡transport' ((λ z → < z > m)) bsa (peq .focEq .pr₁ .pr₁))
  g = potEq→eq _ _ (peq .focEq .pr₁ .pr₂ m bsa) Cube.∙ Cube.sym fg
  gg : PotR
  gg = Cube.hcomp ( λ{ j (i = Cube.i0) -> focR a .pr₁ .pr₂ m (Cube.transp (λ j → < eq ((Cube.~ j) Cube.∧ i) > m) j bs)
                     ; j (i = Cube.i1) -> focR b .pr₁ .pr₂ m (Cube.transp (λ k → eq (Cube._∨_ k j) .pr₁ m)
                j (Cube.transp (λ k → < eq (Cube._∨_ (Cube.~ k) j ) > m) j bs))}) (g i)
potEq→eq a b peq i .focR .pr₂ .pr₁ = eqToPath (peq .focEq .pr₂ .pr₁) i
potEq→eq a b peq i .focR .pr₂ .pr₂ m bs = gg where
  eq = eqToPath (peq .focEq .pr₂ .pr₁)
  bsa = Cube.transport (λ j → < eq ((Cube.~ j) Cube.∧ i) > m) bs
  fg = Cube.cong (λ z → far (focR b) m z) (substPath≡transport' ((λ z → < z > m)) bsa (peq .focEq .pr₂ .pr₁))
  g = potEq→eq _ _ (peq .focEq .pr₂ .pr₂ m bsa) Cube.∙ Cube.sym fg
  gg : PotR
  gg = Cube.hcomp ( λ{ j (i = Cube.i0) -> focR a .pr₂ .pr₂ m (Cube.transp (λ j → < eq ((Cube.~ j) Cube.∧ i) > m) j bs)
                     ; j (i = Cube.i1) -> focR b .pr₂ .pr₂ m (Cube.transp (λ k → eq (Cube._∨_ k j) .pr₁ m)
                j (Cube.transp (λ k → < eq (Cube._∨_ (Cube.~ k) j ) > m) j bs))}) (g i)


cr : CoAlgebra Fpot
cr = PotR , λ x → (nextR x) , ((psetR x) , (x .focR))

inv : PotR × PSet 𝓥 𝓦 𝓣 × FC {B = PotR} → PotR
inv (a , b , c) .nextR = a
inv (a , b , c) .psetR = b
inv (a , b , c) .focR = c

module _ where
 open CoAlgebra Fpot
 open CoAlgebra₂ Fpot
 open Morphism

 inv-f-iso : (cr ⟶) ∘ inv ＝ (λ x → x)
 inv-f-iso = dfunextCube λ x → refl

 f-inv-iso : inv ∘ (cr ⟶) ＝ (λ x → x)
 f-inv-iso = dfunextCube λ x → pathToEq (potEq→eq _ _ (r x)) where
   r : ∀ x → PotEq _ _
   r x .nextEq = poteq-refl
   r x .psetEq = refl
   r x .focEq = (refl , (λ m p → poteq-refl)) , (refl , (λ m p → poteq-refl))

 fc-rel : Final-CoAlgebra Fpot
 fc-rel .pr₁ = cr
 fc-rel .pr₂ = l1 where
  l1 : _
  l1 co = (d ∘ (co ⟶) , refl) , q where
   d : Fn < co > → PotR
   d (nx , p , foc) .nextR = d ((co ⟶) nx)
   d (nx , p , foc) .psetR = p
   d (nx , p , ((eqm , fm) , (eqa , fa))) .focR = (eqm , λ m bs → d ((co ⟶) (fm m bs))) , (eqa , λ m bs → d ((co ⟶) (fa m bs)))

   q : (c : co-morphism co cr) → _
   q (t , eq) = ap (λ z → λ x → z ((co ⟶) x)) e ∙ ap (inv ∘_) eq ∙ ap (_∘ t) f-inv-iso where
    e : d ＝ inv ∘ Fm t
    e = dfunextCube (λ x → (pathToEq ((potEq→eq (d x) ((inv ∘ Fm t) x)) (s x)))) where
     s : (x : Fn < co >) → PotEq (d x) (inv ((Fm t) x))
     s (ix , p , ex) .nextEq = df
       where
        h : (w : PotR) → (inv (Fm t ((co ⟶) ix))) ＝ w → PotEq (d ((co ⟶) ix)) w
        h w refl =   s ((co ⟶) ix)
        df : PotEq (d ((co ⟶) ix)) (t ix)
        df = h (t ix) (ap (λ z → z ix) ((ap (inv ∘_) eq ∙ ap (_∘ t) f-inv-iso)))
     s (ix , p , ex) .psetEq = refl
     s (ix , p , ex) .focEq .pr₁ .pr₁ = refl
     s (ix , p , (ex1 , ex2)) .focEq .pr₁ .pr₂ x v = df where
      h : (w : PotR) → (inv (Fm t ((co ⟶) (pr₂ ex1 x v)))) ＝ w → PotEq (d ((co ⟶) (ex1 .pr₂ x v))) w
      h w refl = s ((co ⟶) (ex1 .pr₂ x v))
      df : PotEq (d ((co ⟶) (ex1 .pr₂ x v))) (t (ex1 .pr₂ x v)) 
      df = h (t (ex1 .pr₂ x v)) (ap (λ z → z ((pr₂ ex1 x v))) ((ap (inv ∘_) eq ∙ ap (_∘ t) f-inv-iso)))
     s (ix , p , (ex1 , ex2)) .focEq .pr₂ .pr₁ = refl
     s (ix , p , (ex1 , ex2)) .focEq .pr₂ .pr₂ x v = df where
      h : (w : PotR) → (inv (Fm t ((co ⟶) (pr₂ ex2 x v)))) ＝ w → PotEq (d ((co ⟶) (ex2 .pr₂ x v))) w
      h w refl = s ((co ⟶) (ex2 .pr₂ x v))
      df : PotEq (d ((co ⟶) (ex2 .pr₂ x v))) (t (ex2 .pr₂ x v)) 
      df = h (t (ex2 .pr₂ x v)) (ap (λ z → z ((pr₂ ex2 x v))) ((ap (inv ∘_) eq ∙ ap (_∘ t) f-inv-iso)))


```
