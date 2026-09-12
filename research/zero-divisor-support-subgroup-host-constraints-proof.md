---
rg: 2
id: zero-divisor-support-subgroup-host-constraints-proof
kind: route
title: Unique products, Kropholler--Linnell--Moody and von Neumann dimension each forbid the zero divisor
target: zero-divisor-support-subgroup-host-constraints
requires: []
---

(1) `k[H]` is a subring of `k[G]` containing `alpha` and `beta`, and
subgroups of torsion-free groups are torsion-free.

(2) Suppose `H` has unique products. Some product `g h` with `g` in
`supp alpha` and `h` in `supp beta` has a unique expression as such a
product. Its coefficient in `alpha beta` is `alpha_g beta_h != 0`, which is a
contradiction.

(3) Kropholler, Linnell and Moody, *Applications of a new K-theoretic theorem
to soluble group rings*, Proc. AMS 104 (1988), 675--684, prove that `D[H]` is
a domain (indeed Ore) for every torsion-free elementary amenable group `H`
and every division ring `D`.

(4) Let `char k = 0`. The finitely many coefficients generate a countable
field of characteristic zero, which embeds in `C`, so `alpha beta = 0` holds
in `C[H]`.
- Right multiplication `r_beta` on `l^2(H)` commutes with the left regular
  representation and kills `alpha != 0`, so its kernel is a nonzero Hilbert
  `L(H)`-module. By faithfulness of the trace, `dim_{L(H)} ker r_beta > 0`.
- The dimension is `< 1`. Equality would force `ker r_beta = l^2(H)`, and then
  `beta = r_beta(delta_1) = 0`.
- A dimension strictly between 0 and 1 contradicts the Strong Atiyah
  conjecture for the torsion-free group `H`, which predicts integer
  dimensions.

QED
