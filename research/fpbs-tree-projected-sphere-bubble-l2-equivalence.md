---
rg: 2
id: fpbs-tree-projected-sphere-bubble-l2-equivalence
kind: claim
title: On tree-projected Cayley graphs the L2 gap holds iff some critical fibre-sphere bubble is below one
distinct_from:
  fpbs-hyperbolic-quotient-fibre-estimates-l2-gap: that derives the L2 gap from two uniform estimates over any hyperbolic quotient; this is an exact equivalence on tree-projected generating sets with a single finite-radius critical quantity.
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated with an infinite cyclic
normal subgroup `H` such that `Q = Gamma/H` is free of rank `n >= 2`. Let `S` be
a finite symmetric generating set whose image in `Q` lies in a free basis, its
inverses and `1`. Examples: `{(a,0),(a,1),(b,0),(1,1)}` in `F_2 x Z`, with
arbitrary height decorations. Put
`b_R(p) = sum_{q in S_Q(R)} sigma_p(q)^2`. Then, on `Cay(Gamma,S)`,

```text
p_c < p_{2->2}     if and only if     b_R(p_c) < 1 for some R >= 1.
```

In particular a single finite-radius critical fibre-sphere bubble below one
gives `p_c < p_u`.

Structure of the proof:
* Fibres are cut sets, so `sigma_p(wu) <= sigma_p(w) sigma_p(u)` and
  `b_(R+R') <= b_R b_(R')`.
* Left-continuity in `p` and the tube excursion bound make the bubble below one
  uniform below `p_c`.
* That gives both premises of `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap`.
* The converse is `B^H_(p_c) <= ||T_(p_c)||^2`.

Proof: artifact Theorem 4.3.
