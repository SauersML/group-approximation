---
rg: 2
id: inverse-finite-algebraic-action-ce-proof
kind: route
title: Dualize the inverse system and apply locality of soficity
target: inverse-finite-algebraic-actions-are-ce
requires: []
---

Put `A_i=K_i-hat`.  Pontryagin duality changes the inverse system into a
filtered direct system of finite `H`-modules and gives

```text
A = K-hat = colimit_i A_i.
```

Write `B_i` for the image of `A_i` in `A`.  Each `B_i` is finite and
`H`-invariant, the family is directed, and `A=union_i B_i`.  This remains
true when the bonding maps have kernels and when none of the inclusions
splits equivariantly.  Consequently

```text
A rtimes H = union_i (B_i rtimes H)                  (IFA1)
```

as a directed union of subgroups.

Every `B_i rtimes H` is sofic for a reason special to this split finite
module extension.  The action homomorphism

```text
H -> Aut(B_i)
```

has finite image.  Its kernel `H_i` has finite index in `H`, hence is sofic,
and `B_i rtimes H_i=B_i times H_i` is sofic.  This direct product has finite
index in `B_i rtimes H`, so finite-extension permanence proves that the
whole stage is sofic.  (No general amenable-kernel permanence is being used.)
Soficity is local, hence is preserved under directed unions: every finite
subset of the group in `(IFA1)` is contained in one of the sofic stages.
Therefore `A rtimes H` is sofic.

Fourier transform gives the trace-preserving isomorphism

```text
L(A rtimes H) = L^infinity(K,Haar) rtimes H.
```

Group von Neumann algebras of sofic groups are Connes embeddable, proving
the claim.
