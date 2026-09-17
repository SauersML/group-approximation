---
rg: 2
id: higman-order-three-torsion-ratio-bound
kind: claim
title: Higman tuples whose odd generators have order three obey a dimension-free linear word bound
distinct_from:
  higman-u2-word-energy-bound: that proves coefficient two only in U(2); this holds in every dimension and every tracial von Neumann algebra, but only on the order-three torsion class.
  higman-hs-word-coefficient-exceeds-sixteen: that refutes small coefficients by one tuple; this proves a finite coefficient on the class in which that tuple and every larger numerical maximizer lie.
  hyperlinear-radical-has-linear-word-certificate: that identifies a global linear certificate with radical membership; this proves a restricted certificate on a torsion class, which by itself says nothing about the radical.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that rewrites general microstates as glued BS packets; this is a direct quantitative collapse through the trivial quotient Hig/<<g_1^3,g_3^3>>.
artifacts:
  - research/artifacts/higman-hs-ratio-scaling-scout-2026-09-17.md
  - experiments/higman-hs-microstate-scaling-2026-09-17/check_torsion_bound.py
  - experiments/higman-hs-microstate-scaling-2026-09-17/ratio_search.py
  - experiments/higman-hs-microstate-scaling-2026-09-17/run_orderq.py
---

Let `g_0,...,g_3` be unitaries in a tracial von Neumann algebra (for example
`U(d)` with `||x||_2^2=tr(x^*x)/d`). Put `e(v)=||v-1||_2^2` and
`r_j=g_j g_(j+1) g_j^(-1) g_(j+1)^(-2)`, `j in Z/4`. Then

```text
e(g_0) <= 25397 ( sum_j e(r_j) + e(g_1^3) + e(g_3^3) ),
```

and, when `g_1^3=g_3^3=1` exactly, `e(g_0) <= 17973 sum_j e(r_j)`. More
precisely, with `eps_j=||r_j-1||_2` and `tau_i=||g_i^3-1||_2`,

```text
||g_0-1||_2 <= 72 eps_0 + 4 eps_1 + 2 eps_2 + 113 eps_3 + 80 tau_1 + 32 tau_3.
```

Consequence (what it rules out). The order-three class
`T3={g_1^3=g_3^3=1}` is closed under direct sums, tensor products and
ultraproducts, and its Higman word-ratio supremum is at most 17973 in all
dimensions. Numerically, every best Higman ratio tuple found for
`d<=16` lies in `T3`, including the certified coefficient-38 tuple. The
same holds for the earlier coefficient-16 tuple, whose odd generators have
`e(g^3)<3e-5`. So no amplification of these witnesses can give `C(4)=infinity`.
Any sequence with ratio tending to infinity must have
`e(g_1^3)+e(g_3^3)` much larger than its relator energy. The odd generators
must stay away from order three at a scale far above the defect.

Reduction (not claimed): if for every `d` the supremum `C_d(4)` is approached
inside `T3`, then `C(4)<=17973` and Higman's group is not hyperlinear. The
search also finds local maximizers outside `T3` with ratio up to 24.3
(d=8), below the best `T3` value 38.74.
