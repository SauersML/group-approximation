---
rg: 2
id: stw74-collapse-matrix-projections-into-the-unit-proof
kind: route
title: Embed every finite matrix corner into a properly infinite unit
target: stw74-all-stabilized-projections-are-properly-infinite
requires:
  - stw74-simple-infinite-projections-are-properly-infinite
---

The unit of `A` is infinite and hence properly infinite by the required
theorem.  For each `n`, choose isometries `s_1,...,s_n in A` with orthogonal
ranges and define

```text
Phi_n:M_n(A) -> A,
Phi_n((a_ij))=sum_(i,j) s_i a_ij s_j*.
```

This is an injective star homomorphism onto the corner `eAe`, where
`e=sum_i s_i s_i*`.  If `P in M_n(A)` is a nonzero projection, then
`Phi_n(P)` is a nonzero projection in `A`, hence properly infinite.  The
witnessing partial isometries lie in

```text
Phi_n(P) A Phi_n(P) = Phi_n(P) (eAe) Phi_n(P),
```

so pulling them back through `Phi_n` proves that `P` itself is properly
infinite.

Finally, every projection in `A tensor K` is Murray--von Neumann equivalent
to a projection in some finite matrix corner: compress it by a sufficiently
large standard finite-rank projection and use the usual norm-less-than-one
perturbation lemma for projections.  Proper infiniteness is invariant under
Murray--von Neumann equivalence.
