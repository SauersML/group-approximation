---
rg: 2
id: leavitt-hyperlinearity-eighteen-relator-unitary-test
kind: claim
title: The binary Leavitt unit group is hyperlinear exactly when four unitaries almost satisfy eighteen explicit relators without x being almost trivial
distinct_from:
  atlas-relator-central-sufficiency: that is the atlas criterion over two regular copies of A8 with a 4,648-entry list and a central-extension condition; this is a four-matrix test on eighteen relators, with no central extension, because the presented group is the unit group itself and is simple.
  hyperlinear-radical-presentation-compactness: that is a general compactness equivalence for membership in the hyperlinear radical, for any presentation; this specializes it to one explicit presentation of a simple group, where radical membership collapses to a yes-or-no question about one generator.
  eighteen-relator-system-is-hamming-rigid: that is the permutation analogue, which is proved; this unitary version is open, and deciding it either way decides whether L_(F_2)(1,2)^x is hyperlinear.
---

**ESTABLISHED (2026-09-12, unreviewed)** as an equivalence, through
`leavitt-hyperlinearity-eighteen-relator-unitary-test-proof`. Which side holds is
unknown.

Let `r_1..r_18` be the relators of `thompson-steinberg-presentation-of-leavitt-unit-group`, and
`||Y||_2 = (tr(Y*Y)/d)^(1/2)` the normalized Hilbert--Schmidt norm on `M_d(C)`. The following
are equivalent:
1. `L_(F_2)(1,2)^x` is hyperlinear.
2. There are dimensions `d_k` and unitaries `A_k, B_k, C_k, X_k in U(d_k)` such that
   `max_j ||r_j(A_k,B_k,C_k,X_k) - I||_2 -> 0` and `liminf_k ||X_k - I||_2 > 0`.

Condition 2 may equivalently ask for any one of `A_k, B_k, C_k` to stay away from `I`, or all
four together. Either way the generated limit homomorphism is nontrivial, hence faithful.

So the question whether the first nonsofic group is hyperlinear — an instance of the famous open
problem of whether every group is hyperlinear, when read toward a negative answer — is a
four-matrix optimization over eighteen words of total length 322. Condition 2 requires, in
particular, almost-representations of Thompson's `V` through the eight words (2.4). Probes of `V`
alone already plateau (`research/artifacts/thompson-v-model-probes-2026-09-12.md`), which is where
a numerical attack on condition 2 would meet its first wall.
