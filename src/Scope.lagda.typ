#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Scope


Every system needs to have local variables /channels that only its members can interact with. At the same time, the channel can be passed to an external system, thus the scope of the
channel changes, it encompasses this external system as well. In $pi$-calculus, this is
expressed by the structural rule:

$(nu x)(P | Q) equiv (nu x) P | Q$  when $x$ is not a free variable in $Q$.

Let us now have an example where we show how we handle scope in our system. Consider these systems:

$A colon.eq (nu x) (tilde(y)⟨x⟩.0|x(k).tilde(k)⟨q⟩.0|d(q).A) $

$B colon.eq y(e).tilde(e)⟨z⟩.tilde(d)⟨k⟩.0|z(q).B $


We have discussed that our systems are described by sets of potentialities. Here though,
we have the simplest systems. Let us describe system A:

#diagram(
    node((0,2.1), $...$, name: <C>),
    node((0,2.8), $tilde(y)|d$, name: <B>),
    node((0,3.5), $tilde(y)|d$, name: <A>),
    edge(<A>, <B>, "-|>"),
    edge(<B>, <C>, "-|>"),
    node((rel: (1.4, -0.2), to: <A>), name: <Fa>),
    edge(<A>, <Fa>, "-|>" ,),
    node((rel: (-0.5, -0.2), to: <Fa>), $tilde(y)|d$ , name: <Fa1> ),
    node((rel: (0, -0.7), to: <Fa1>), $tilde(y)|d$ , name: <Fa2> ),
    node((rel: (0, -1.4), to: <Fa1>), $...$ , name: <Fa3> ),
    edge(<Fa1>, <Fa2>, "-|>" ,),
    edge(<Fa2>, <Fa3>, "-|>" ,),

    node((rel: (0.5, -0.2), to: <Fa>), $x|d$ , name: <Fb1> ),
    node((rel: (0, -0.7), to: <Fb1>), $x|d$ , name: <Fb2> ),
    node((rel: (0, -1.4), to: <Fb1>), $...$ , name: <Fb3> ),
    edge(<Fb1>, <Fb2>, "-|>" ,),
    edge(<Fb2>, <Fb3>, "-|>" ,),
    node(enclose: (<A>, <B>, <C> , <Fa> , <Fa1> , <Fb1> , <Fb3>),
         stroke: teal, fill: teal.lighten(90%),
         snap: -1, // prioritise other nodes when auto-snapping
         name: <g1>) ,
    node((rel: (1.4, -0.2), to: <Fb1>), name: <Fc>),
    edge(<Fb1>, <Fc>, "-|>" ,),
    
    node((rel: (0.5, -0.2), to: <Fc>), $tilde(k)|d$ , name: <Fc1> ),
    node((rel: (0, -0.7), to: <Fc1>), $tilde(k)|d$ , name: <Fc2> ),
    node((rel: (0, -1.4), to: <Fc1>), $...$ , name: <Fc3> ),
    edge(<Fc1>, <Fc2>, "-|>" ,),
    edge(<Fc2>, <Fc3>, "-|>" ,),

    node((rel: (-0.5, -0.2), to: <Fc>), $x|y|d$ , name: <Fd1> ),
    node((rel: (0, -0.7), to: <Fd1>), $x|y|d$ , name: <Fd2> ),
    node((rel: (0, -1.4), to: <Fd1>), $...$ , name: <Fd3> ),
    edge(<Fd1>, <Fd2>, "-|>" ,),
    edge(<Fd2>, <Fd3>, "-|>" ,),

    node((rel: (1.4, -0.2), to: <Fc1>), name: <Fe>),
    edge(<Fc1>, <Fe>, "-|>" ,),
    
    node((rel: (0.5, -0.2), to: <Fe>), $d$ , name: <Fe1> ),
    node((rel: (0, -0.7), to: <Fe1>), $d$ , name: <Fe2> ),
    node((rel: (0, -1.4), to: <Fe1>), $...$ , name: <Fe3> ),
    edge(<Fe1>, <Fe2>, "-|>" ,),
    edge(<Fe2>, <Fe3>, "-|>" ,),

    node((rel: (-0.5, -0.2), to: <Fe>), $tilde(k)|tilde(y)|x|d$ , name: <Fq1> ),
    node((rel: (0, -0.7), to: <Fq1>), $tilde(k)|tilde(y)|x|d$ , name: <Fq2> ),
    node((rel: (0, -1.4), to: <Fq1>), $...$ , name: <Fq3> ),
    edge(<Fq1>, <Fq2>, "-|>" ,),
    edge(<Fq2>, <Fq3>, "-|>" ,),

)

Each horizontal line represents the function of change after system A receives/sends
a msg from a specific channel. For the first case, there are two possibilities,
either it sent a message on channel $tilde(y)$ or it received a message on channel $d$. For this reason, there are two potentialities.

$k$ is a variable, it is the secret to be received by channel $x$.

Keep in mind that the type does not track the number of *actors* that are present. It only
cares whether there is at least one actor that accepts/sends a specific channel. It is idempotent. It is for this reason that the second column is not $tilde(y)|tilde(y)|d$

Also, the diagram is incomplete, since we do not describe the functions of change of the
other potentialities.

Now, if you look closer, at the first type, it is $tilde(y)|d$ when channel $x$ is ready to
receive new messages. Of course, this is not possible since $x$ is a local variable. In column 3 though, $x$ is part of the type, the reason for that is that channel $x$ has been transmitted to the outside world.

System B:

#diagram(
    node((0,2.1), $...$, name: <C>),
    node((0,2.8), $y|z$, name: <B>),
    node((0,3.5), $y|z$, name: <A>),
    edge(<A>, <B>, "-|>"),
    edge(<B>, <C>, "-|>"),
    node((rel: (1.4, -0.2), to: <A>), name: <Fa>),
    edge(<A>, <Fa>, "-|>" ,),
    node((rel: (-0.5, -0.2), to: <Fa>), $y|z$ , name: <Fa1> ),
    node((rel: (0, -0.7), to: <Fa1>), $y|z$ , name: <Fa2> ),
    node((rel: (0, -1.4), to: <Fa1>), $...$ , name: <Fa3> ),
    edge(<Fa1>, <Fa2>, "-|>" ,),
    edge(<Fa2>, <Fa3>, "-|>" ,),

    node((rel: (0.5, -0.2), to: <Fa>), $tilde(e)|z$ , name: <Fb1> ),
    node((rel: (0, -0.7), to: <Fb1>), $tilde(e)|z$ , name: <Fb2> ),
    node((rel: (0, -1.4), to: <Fb1>), $...$ , name: <Fb3> ),
    edge(<Fb1>, <Fb2>, "-|>" ,),
    edge(<Fb2>, <Fb3>, "-|>" ,),

    node((rel: (1.4, -0.2), to: <Fb1>), name: <Fc>),
    edge(<Fb1>, <Fc>, "-|>" ,),
    
    node((rel: (0.5, -0.2), to: <Fc>), $tilde(d)|z$ , name: <Fc1> ),
    node((rel: (0, -0.7), to: <Fc1>), $tilde(d)|z$ , name: <Fc2> ),
    node((rel: (0, -1.4), to: <Fc1>), $...$ , name: <Fc3> ),
    edge(<Fc1>, <Fc2>, "-|>" ,),
    edge(<Fc2>, <Fc3>, "-|>" ,),

    node((rel: (-0.5, -0.2), to: <Fc>), $tilde(e)|y|z$ , name: <Fd1> ),
    node((rel: (0, -0.7), to: <Fd1>), $tilde(e)|y|z$ , name: <Fd2> ),
    node((rel: (0, -1.4), to: <Fd1>), $...$ , name: <Fd3> ),
    edge(<Fd1>, <Fd2>, "-|>" ,),
    edge(<Fd2>, <Fd3>, "-|>" ,),

    node((rel: (1.4, -0.2), to: <Fc1>), name: <Fe>),
    edge(<Fc1>, <Fe>, "-|>" ,),
    
    node((rel: (0.5, -0.2), to: <Fe>), $z$ , name: <Fe1> ),
    node((rel: (0, -0.7), to: <Fe1>), $z$ , name: <Fe2> ),
    node((rel: (0, -1.4), to: <Fe1>), $...$ , name: <Fe3> ),
    edge(<Fe1>, <Fe2>, "-|>" ,),
    edge(<Fe2>, <Fe3>, "-|>" ,),

    node((rel: (-0.5, -0.2), to: <Fe>), $tilde(d)|y|z$ , name: <Fq1> ),
    node((rel: (0, -0.7), to: <Fq1>), $tilde(d)|y|z$ , name: <Fq2> ),
    node((rel: (0, -1.4), to: <Fq1>), $...$ , name: <Fq3> ),
    edge(<Fq1>, <Fq2>, "-|>" ,),
    edge(<Fq2>, <Fq3>, "-|>" ,),

)

Both systems A and B are static, meaning that they cannot progress any further without
external help. For this reason each column has a constant type. In general though, systems
progress on their own.

In the next diagram, I will only describe the initial potentialities of the system A&B, when
it is not pertrubed by an external system.

#diagram(
    node((0,0.7), $...$, name: <E>),
    node((0,1.4), $tilde(d)|d$, name: <D>),
    node((0,2.1), $tilde(d)|tilde(z)|d|z$, name: <C>),
    node((0,2.8), stroke: teal, fill: teal.lighten(90%),
                  $d|z$, name: <B>),
    node((0,3.5), $tilde(y)|d|y|z$, name: <A>),
    edge(<A>, <B>, "-|>"),
    edge(<B>, <C>, "-|>"),
    edge(<C>, <D>, "-|>"),
    edge(<D>, <E>, "-|>"),

    node((0.7,0.7), $...$, name: <E2>),
    node((0.7,1.4), $tilde(z)|z$, name: <D2>),
    node((0.7,2.1), $tilde(d)|tilde(z)|d|z$, name: <C2>),
    node((0.7,2.8),
        stroke: teal, fill: teal.lighten(90%),
        $d|z$, name: <B2>),
    node((0.7,3.5), $tilde(y)|d|y|z$, name: <A2>),
    edge(<A2>, <B2>, "-|>"),
    edge(<B2>, <C2>, "-|>"),
    edge(<C2>, <D2>, "-|>"),
    edge(<D2>, <E2>, "-|>"),

)


The interesting thing happens at the second "state" of the potentialities. Here, it should
have been $x|d|tilde(x)|z$. The reason it is not is because channel $x$ has been
sent inside the system, thus we know that noone else has channel $x$, thus it is impossible
that the external world communicate with A&B through channel $x$.

This is how I handle scope at the moment, by limiting the type of the system to remove channels that cannot be accessed by the exterior world.

In this 'library', we do not have channels, by predicates that require the knowledge of a list of secrets. Thus, any predicates that can only be fulfilled from inside the system are removed. This is the functionality of the *limit&* function.

/*
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
```
*/


```agda
restr : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → (P : A → 𝓥 ̇ ) → Σ P → A
restr P x =  x .pr₁

_$₂_ : ∀{𝓤 𝓥} → {A : 𝓤 ̇ } → {B : 𝓥 ̇ } → (A → B) → A × A → B × B
f $₂ (a , b) = f a , f b

+→𝟚 : ∀{𝓤 𝓥} → {X : 𝓤 ̇ } → {Y : 𝓥 ̇ } → X + Y → 𝟚
+→𝟚 (inl x) = ₀
+→𝟚 (inr x) = ₁

scope-l1 : (x : Secret) → (ls : List Secret) → (A : 𝟚 → 𝓦 ̇ )
          → is-decidable (x ∈ ls) → 𝓦 ̇
scope-l1 x ls A r = A (+→𝟚 r)


module BSet-scope (_∈?_ : ∀ s ls → is-decidable (s ∈ ls)) where

 Lim : 𝓥 ̇  → 𝟚 → Set 𝓥
 Lim P ₀ = 𝟘
 Lim P ₁ = P

 limitPr : Secret → 𝓥 ̇  → Pred S×Msg 𝓥
 limitPr s P mp@(ls , msg) = scope-l1 s ls (Lim P) (s ∈? ls)

 limit : Secret → BSet 𝓥 → BSet 𝓥
 limit s bs .pr₁ mp = limitPr s (< bs > mp) mp
 limit s bs .pr₂ = λ ascrs scrs x (a⊂s , a⊃s) → l1 ascrs scrs x a⊂s a⊃s (s ∈? ascrs) (s ∈? scrs) , l2 ascrs scrs x a⊂s a⊃s (s ∈? scrs) (s ∈? ascrs) where
   l1 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ ascrs)) → (deq2 : is-decidable (s ∈  scrs)) → scope-l1 s ascrs (Lim (< bs > (ascrs , x))) deq → scope-l1 s scrs (Lim (< bs > (scrs , x))) deq2
   l1 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s scrs ascrs a⊂s eq2))
   l1 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₁ cond

   l2 : ∀ ascrs scrs x a⊃s a⊂s → (deq : is-decidable (s ∈ scrs)) → (deq2 : is-decidable (s ∈ ascrs)) → scope-l1 s scrs (Lim (< bs > (scrs , x))) deq → scope-l1 s ascrs (Lim (< bs > (ascrs , x))) deq2
   l2 ascrs scrs x a⊃s a⊂s (inr neq) (inl eq2) cond = 𝟘-elim (neq (∈→∈ s ascrs scrs a⊃s eq2))
   l2 ascrs scrs x a⊃s a⊂s (inr neq) (inr x₁) cond = bs .pr₂ ascrs scrs x (a⊃s , a⊂s) .pr₂ cond

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

-- limitM is a restriction, so it fits where bs fits.
 lim-rec : ∀{𝓦} → {A : 𝓦 ̇ } → ∀ s ls {bs mp} → < (limitM {𝓥} s ls bs) > mp → (< bs > mp → A) → A
 lim-rec s [] {bs} {mp@(ws , msg)} c f = l1 (s ∈? ws) c where
  l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
       Lim (< bs > (ws , msg)) (+→𝟚 w) → _
  l1 (inr _) c = f c

 lim-rec {𝓥 = 𝓥} s (l ∷ ls) {bs} {mp@(ws , msg)} c f = l1 (s ∈? ws) c where
  l1 : (w : (s ∈ ws) + (s ∈ ws → 𝟘)) →
       limitMPr l ls (Lim (< bs > (ws , msg)) (+→𝟚 w)) (ws , msg) → _
  l1 (inl x) c with limitMPr {𝓥} l ls 𝟘 mp | (limitMPr-𝟘 {𝓥} l ls mp)
  l1 (inl x) c | r | d = 𝟘-elim (transport (λ x → x) d c)
  l1 (inr x) c = lim-rec l ls {bs} {mp} c f


 lim-rec' : ∀{𝓦} → {A : 𝓦 ̇ } → ∀ ls bs {mp} → < (limitM' {𝓥} ls bs) > mp → (< bs > mp → A) → A
 lim-rec' [] _ c f = f c
 lim-rec' (x ∷ ls) bs {mp} = lim-rec x ls {bs}


 module &PSet-scope {𝓥} where

  limit&P : Secret → &PSet 𝓥 𝓦 → &PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  limit&P s ps .pr₁ v = v ∈image λ x → (λ (a , bs) → a , limit s bs) (restr < ps > x)
  limit&P s ps .pr₂ = cons-is-non-empty

  limit&PM : Secret → List Secret → &PSet 𝓥 𝓦 → &PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
  limit&PM s ls ps .pr₁ v = v ∈image λ x → (λ (a , bs) → a , limitM s ls bs) (restr < ps > x)
  limit&PM s ls ps .pr₂ = cons-is-non-empty
```
