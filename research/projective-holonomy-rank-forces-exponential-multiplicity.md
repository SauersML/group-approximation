---
rg: 2
id: projective-holonomy-rank-forces-exponential-multiplicity
kind: claim
title: Binary projective holonomy of rank two-r forces a two-to-r multiplicity divisor
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
distinct_from:
  commuting-automorphism-cocycle-forces-multiplicity: that treats one projective square and obtains one fixed-order divisor; this computes an arbitrary binary cocycle rank and its exponential multiplicity cost.
  robust-clifford-capacity-bound: that bounds the ambient dimension of an all-pairs approximate Clifford-group homomorphism; this is an exact packet-isotypic theorem in which the Clifford representation is forced specifically onto the external multiplicity space.
  same-model-supercritical-clifford-trigger: that must activate more Clifford rank than the candidate model can support with uniform HS soundness; this identifies the exact multiplicity inequality such a trigger must force.
---

Let `B` be finite, let `T` be an irreducible `B`-module, and let
`alpha_1,...,alpha_n in Aut(B)` preserve the equivalence class of `T`.  Assume
the automorphisms commute and choose implementers `U_i` on `T` with binary
projective commutators

```text
U_i U_j=(-1)^(Omega_(ij)) U_j U_i,                              (PHR1)
```

where `Omega` is an alternating matrix over `F_2` of rank `2r`.  In any
representation of

```text
<B,t_1,...,t_n |
  t_i b t_i^(-1)=alpha_i(b), [t_i,t_j]=1>
```

whose invariant `T`-isotypic space is `T tensor C^m`, one has

```text
2^r divides m.                                                   (PHR2)
```

Equivalently, the commuting stable-letter holonomy transfers the entire
rank-`2r` Clifford obstruction from the fixed packet factor to the external
multiplicity factor.  Since `m<=d/dim(T)` in a `d`-dimensional model, any
same-model mechanism activating

```text
r>log_2(d/dim(T))                                                (PHR3)
```

is an exact dimension contradiction.

At any fixed `r`, `(PHR2)` is still normalized-HS dilutable: enlarge `m` and
repair fewer than `2^r` residual copies.  Thus self-similarity must make the
activated cocycle rank depend on the current model, or generate extensive
independent holonomy cells.  The theorem identifies adaptive cocycle rank,
not generic Reynolds transport, as the remaining quantitative resource.

