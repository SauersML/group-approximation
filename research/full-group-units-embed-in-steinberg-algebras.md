---
rg: 2
id: full-group-units-embed-in-steinberg-algebras
kind: claim
title: The topological full group of an ample groupoid embeds in the unit group of its Steinberg algebra
artifacts:
  - research/artifacts/bh-algebra-envelopes-2026-09-12.md
---

**ESTABLISHED.** Let `G` be an ample groupoid, Hausdorff or not, with compact
unit space `G^(0)`. Let `R` be a nonzero commutative unital ring. Write `[[G]]`
for the group of full compact open bisections, those `U` with
`s(U) = r(U) = G^(0)`, under `UV` and `U^-1`. Then

```text
[[G]] -> A_R(G)^x,     U |-> 1_U,
```

is an injective group homomorphism into the unit group of the Steinberg
algebra.

**Example.** For the Cuntz groupoid, `A_K(G)` is the Leavitt algebra
`L_K(1,2)`, and `[[G]]` is Thompson's `V` acting on the Cantor set. That
identification is cited context and is not used in the proof.

## Role on the Boone--Higman algebra route

`simple-inputs-have-fp-elementary-leavitt-tensor-hosts` asks for an embedding
`S -> B^x` of a group into units, not for `K[S] ⊆ B`. Steinberg algebras supply
unit embeddings of topological full groups directly. By
`full-group-algebra-to-steinberg-algebra-not-injective`, they do so without
containing the group algebra. So on this route the host algebra need not solve
`algebra-boone-higman-conjecture` for group algebras.
