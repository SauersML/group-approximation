---
rg: 2
id: centered-gap-is-on-a-tree-or-forces-tree-motion
kind: claim
title: The centered separator gap is on a tree face or its closing-face part forces tree motion
distinct_from:
  global-triangle-separator-survives-mod-augmentation: that proves a centered component survives on some face and gives full-support finite-dimensional witnesses; this separates the tree and closing cases and identifies the exact finite Choi face in the closing case.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that uses a kernel-cycle Gram matrix to obstruct maps canonical on both tree faces; this uses scalar rather than canonical tree restrictions and multiplicative-domain rigidity inside the finite closing face.
  kernel-relator-forces-two-edge-ucp-section-gap: that gives a quantitative norm gap for a closing-face section trying to fix both edge lifts canonically; this proves an exact scalar-edge collapse and records the remaining mixed Choi pattern without claiming a new norm modulus.
---

**ESTABLISHED (finite centered dichotomy).**  Normalize the global separator
`ell`, fix one bounded face splitting `(SQS7)--(SQS9)`, and set

```text
D_epsilon=id-E_epsilon,
c_ij=ell_ij(D_epsilon|_(C^*(P_ij))).                       (CGT1)
```

Then

```text
c_12+c_23+c_13>=delta.                                    (CGT2)
```

Consequently at least one side of the following useful alternative holds:

```text
max(c_12,c_23)>=delta/6,                                  (CGT3)
```

or

```text
c_13>=2delta/3.                                           (CGT4)
```

In `(CGT3)`, the mod-augmentation component is already on a named tree face.
Choi positivization and the deletion argument from
`global-triangle-separator-survives-mod-augmentation` then give
full-ideal-support finite-dimensional packets with a fixed positive **tree**
defect and arbitrarily small prescribed ideal moments.

In `(CGT4)`, the obvious Boca repair cannot keep both tree faces scalar while
using a non-scalar closing map.  More precisely, put

```text
F_scalar={Phi in UCP(S_Delta,A):
          Phi|_(C^*(P_12))=epsilon(.)1_A,
          Phi|_(C^*(P_23))=epsilon(.)1_A}.                 (CGT5)
```

Then

```text
F_scalar={E_epsilon^A}.                                   (CGT6)
```

Thus `(CGT5)` is a singleton face of the finite-domain Choi feasibility
problem.  There is no closing-face degree of freedom left once both tree
faces are held at scalar augmentation.  Any simultaneous correction of the
large centered closing component in `(CGT4)` must make at least one tree-face
restriction non-scalar.

**Quantitative closure of the scalar-tree residual.**
`scalar-tree-perturbations-force-square-root-closing-control` proves that if
both tree restrictions are within `eta<=1` in cb norm of scalar augmentation,
then the closing restriction is within `C_Delta sqrt(eta)` of scalar
augmentation.  Hence fixed closing movement forces tree movement at least
`min{1,(r/C_Delta)^2}`.  What remains is not this finite-face modulus but the
primal/dual bridge: the large signed separator evaluation `(CGT4)` does not by
itself select a ucp repair with a quantitatively large closing movement.
`supporting-choi-component-does-not-force-primal-motion` shows that this
selection cannot be obtained from closest-point Choi duality alone, even in a
three-point scalar state simplex; a triangle-specific transversality estimate
is required.

Proof: `split-the-centered-gap-and-collapse-the-scalar-tree-choi-face`.

DERIVATION
split-the-centered-gap-and-collapse-the-scalar-tree-choi-face
