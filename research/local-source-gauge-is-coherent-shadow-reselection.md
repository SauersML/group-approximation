---
rg: 2
id: local-source-gauge-is-coherent-shadow-reselection
kind: claim
title: Local source gauges are quantitatively equivalent to coherent shadow reselection
distinct_from:
  spherical-short-holonomies-admit-local-gauge: that is the open existence theorem; this is the exact change of variables showing that its gauges are neither weaker nor easier than coherently reselecting all shadow maps.
  hypergraph-near-perfect-schreier-packing: that is one proposed construction of coherent shadow maps; this theorem is method-independent and identifies the object any construction must produce.
  regular-table-local-h1-restates-spherical-gauge: that identifies local H1 triviality with the gauge conclusion; this identifies the same gauge conclusion directly with simultaneous coherent geometric rounding.
---

Let `x_1,...,x_N` lie in a metric space, let each `U_s` act isometrically,
and let `sigma_s` be permutations which `rho_s`-shadow `U_s` outside sets
of density at most `eta_s`:

```text
d(x_(sigma_s(i)),U_s x_i) <= rho_s.
```

For arbitrary permutations `c_s`, put `tau_s=sigma_s c_s`.

1. If `c_s` moves cloud points by at most `lambda_s` outside a set of
   density `theta_s`, then `tau_s` shadows `U_s` at radius
   `rho_s+lambda_s` outside a set of density at most
   `eta_s+theta_s`.
2. Conversely, if `tau_s` shadows `U_s` at radius `rho'_s` outside a
   set of density `eta'_s`, then `c_s=sigma_s^(-1)tau_s` moves cloud
   points by at most `rho_s+rho'_s` outside a set of density at most
   `eta_s+eta'_s`.
3. For every tested product `gh=k`, the gauge equation for `c_g,c_h,c_k`
   holds at an index exactly when
   `tau_g tau_h=tau_k` holds there. Their normalized Hamming defects are
   identical.

Consequently, once the independent shadows `sigma_s` have been chosen,
geometrically local source-gauge trivialization is quantitatively equivalent
to reselecting a simultaneous family of coherent permutation shadows on the
same cloud. In particular the spherical local-gauge route does not bypass the
coupled rounding problem; it is an exact coordinate form of that problem.

This equivalence neither proves nor refutes the existence of the coherent
reselection. It rules out treating the gauge variables themselves as an
independent source of compactness or cohomological freedom.

DERIVATION
[[local-source-gauge-shadow-reselection-proof]]
