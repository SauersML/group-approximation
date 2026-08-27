---
rg: 2
id: atlas-a4-classical-mixture-trace-separator
kind: claim
title: The one-fifth A4 collision gap gives a weighted trace separator for every classical alignment mixture
artifacts:
  - experiments/atlas_triangle_19243_classical_gap.py
  - experiments/atlas-word-19243.json
---

Let `w_1,...,w_30` be the thirty pair-cube words in
`atlas-shortest-a4-triangle-packet`, and let `q=q_19243` be the fixed collision
word.  For either inner or outer automorphism alignment `phi` of
`A8=GL(4,2)`, let `tau_phi` be the normalized regular trace after evaluating
factor one identically and factor two through `phi`.

For any probability distribution `nu` on the finite set of all such
alignments, put

```text
tau_nu = sum_phi nu(phi) tau_phi.
```

Then the following dimension-free weighted defect inequality holds:

```text
sum_(j=1)^30 ||w_j-1||_(2,tau_nu)^2
  + 6 ||q-1||_(2,tau_nu)^2
  >= 12.                                                (A4-MIX-SEP)
```

Equivalently,

```text
sum_(j=1)^30 Re tau_nu(w_j) + 6 Re tau_nu(q) <= 30.    (A4-MIX-HYP)
```

Thus the finite classical audit separates not only individual chart
alignments but their entire convex hull.  In particular a matrix-valued atlas
obstruction does **not** need to round to one global alignment: it is enough to
round the thirty-one relevant trace moments to an arbitrary convex mixture of
inner/outer automorphism alignments.
