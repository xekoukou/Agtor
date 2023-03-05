module Notes where


{-

Assume that A , B , C are predicates on UMTypes and porbably secrets.

if we have A as the predicate on the type of msgs, then A ᵉ is the predicate of the input of an actor or a system in general.
A is for msgs, A ᵉ is for the consumption of messages.

Given a msg of type A, and an actor B ᵉ , then reduction can only occur if ∀ x ∈ A → x ∈ B

A ∧ B means that both A and B exist. For reduction to continue, we need that either ⊃A ᵉ or ⊃B ᵉ exist at all cases.

for example : (A · B) ∪ ( B · C · A) has type A ∧ B (but not the only one), and (⊃A ᵉ · C) ∪ ((D ∪ E) · ⊃B ᵉ) has type ⊃A ᵉ ∨ ⊃B ᵉ

A ᵉ ∧ B ᵉ requires that A⊃ ∨ B⊃.


C has type A ∧ B if ∀ x ∈ A → x ∈ C  and ∀ x ∈ B → x ∈ C. This means that we do not care about the number of resources that have this type. We only care that there is a resource that has this type.

A has type A ∨ B.

A ∪ B has type A ∨ B since A has type A ∨ B AND B has type A ∨ B

A · B has type C if ∀ x ∈ C → (x ∈ A OR x ∈ B)

A · B has type A
A · B has type A ∨ C


Now, the question is, how do we characterize our existing terms, how do we assign types to them, and if we have multiple types, how do we know that we have taken into account all possible reduction cases. that correspond to δ (derivation)

A has type A.

term A · B has type A ∧ B
term A ∪ B has type A ∨ B


if A and B,  A ᵉ · B has type A ᵉ ∧ B , the env needs A⊃ ∨ ⊃(B - A) ᵉ

(This is probably wrong)

0 ᵉ ∨ a ＝ 0 ᵉ

0 ᵉ ∧ a = a

0 ∧ a = 0

0 ∨ a = a

-----------------------------------------

B ⊏ A means that if B holds , then A holds, if reduction can happen with B, then it can happen with A.
A is less restrictive.

     B ⊃ A , then B ᵉ ⊏ A ᵉ            
     A ⊃ B , then    B ⊏ A 




-}
