---
rg: 2
id: fpbs-amenable-kernel-l2-gap-forces-fibre-bubble
kind: claim
title: For an amenable kernel the L2 gap forces a finite critical fibre bubble
distinct_from:
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that equivalence's forward half is the same computation for tree-projected generating sets with cyclic kernel; this holds for every amenable normal subgroup and every quotient.
  fpbs-hyperbolic-quotient-uniform-fibre-bubble: that is the open class-wide premise; this shows that on any single Cayley graph with amenable kernel the premise at p_c is forced by p_c < p_2->2, so it cannot fail where the L2 gap holds.
artifacts:
  - research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `S` a finite symmetric
generating set, `H` an amenable normal subgroup, `Q = Gamma/H`, and
`sigma_p(q) = E_p|K_o ∩ q|`. If `p_c < p_{2->2}` on `Cay(Gamma,S)`, then

```text
sum_{q in Q} sigma_(p_c)(q)^2  <=  ||T_(p_c)||_{2->2}^2  <  infinity.
```

So for amenable kernels the L2 gap sits between two critical fibre bubbles. The
polynomially weighted bubble over a quotient with rapid decay is sufficient
(`fpbs-rd-quotient-weighted-bubble-gives-critical-l2`), and the unweighted
bubble is necessary. Proof: artifact Section 2.
