---
rg: 2
id: strict-psd-regularization-has-no-uniform-hs-affine-error-bound
kind: claim
title: Strict PSD regularization does not give a dimension-free normalized-HS affine feasibility bound
distinct_from:
  maslov-sector-tracial-generator-ucp-liftability: that asks for an arithmetic ucp lift on the canonical generator system; this gives an elementary sharp obstruction to one generic strict-regularization strategy for constructing such a lift.
  chordal-partial-positive-operator-matrices-lift: chordal completion produces exact positive completions from exactly compatible clique data; this rules out repairing approximate affine compatibility merely by mixing with a Slater point and projecting.
---

There is no dimension-independent constant `C` with the following property:
for every matrix size, every affine subspace `L` containing `I`, and every
positive `H >= I`,

```text
dist_2(H, PSD intersect L) <= C dist_2(H,L).             (CER1)
```

The failure persists when `H` is obtained by mixing an arbitrary positive
matrix with the fixed strict Slater point `I` by any prescribed
`0<t<1`.  In fact there are bounded diagonal examples with

```text
dist_2(H_d,L_d) <= 2/sqrt(d),
dist_2(H_d, PSD intersect L_d) = 1.                     (CER2)
```

Consequently the proposed Maslov strategy "mix a tracial Gram lift with a
strictly positive regular kernel, then project to the affine label space"
needs a new arithmetic uniform cone-angle theorem.  Strict positivity alone
cannot convert normalized-HS label error into simultaneous positive-and-
affine feasibility.

The proof is `strict-psd-regularization-cone-angle-counterexample-proof`.
