---
rg: 2
id: full-group-algebra-to-steinberg-algebra-not-injective
kind: claim
title: The group algebra of a topological full group does not embed canonically in the Steinberg algebra
distinct_from:
  full-group-units-embed-in-steinberg-algebras: that embeds the group into the units; this shows the linear extension of that embedding to the group algebra has a kernel.
artifacts:
  - research/artifacts/bh-algebra-envelopes-2026-09-12.md
---

**ESTABLISHED.** Let `G` be an ample groupoid with compact unit space and `R` a
nonzero commutative unital ring. Suppose `G^(0) = U ⊔ W` is a clopen partition
such that `U` carries two distinct compact open bisections `alpha != alpha'` with
`s = r = U`, and `W` carries `beta != beta'` with `s = r = W`. Then the
`R`-linear extension

```text
R[ [[G]] ] -> A_R(G),     g |-> 1_g,
```

of `full-group-units-embed-in-steinberg-algebras` is not injective. Its kernel
contains

```text
(alpha ⊔ beta) - (alpha ⊔ beta') - (alpha' ⊔ beta) + (alpha' ⊔ beta') != 0.
```

For the Cuntz groupoid (Thompson's `V` in `L_K(1,2)`) the hypothesis holds with
`U = [0]` and `W = [1]`. On each cylinder, take the identity and the swap of its
two child cylinders.

## Consequence

- **What the algebra route needs.** Algebra hosts on the Boone--Higman route
  deliver groups into units without containing their group algebras. So the
  premise `simple-inputs-have-fp-elementary-leavitt-tensor-hosts` (units only)
  is weaker in kind than `decidable-group-algebras-have-fp-central-simple-hosts`
  (group algebras). `algebra-boone-higman-conjecture` is sufficient for it but
  not necessary.
- **Scope.** This concerns the canonical map. It says nothing about other
  embeddings of `R[V]` into Leavitt-type algebras.
