---
rg: 2
id: sl3-return-assembly-firewall-proof
kind: route
title: Cartan full-group detection plus property FA
target: sl3-lattice-returns-have-no-canonical-rf-or-free-assembly
requires: []
---

Put `D=L^infinity(G)`.  The left translation action of the countable dense
group `A` is free, so `D subset Q=D rtimes A` is a Cartan inclusion.  Suppose
`alpha_g=Ad(V)` for a unitary `V in Q`.  Since `alpha_g(D)=D`, the Cartan
normalizer/full-group correspondence gives a measurable map `a:G->A` with

```text
xg=a(x)x                                                    (RAFP1)
```

almost everywhere.  Some fibre `a(x)=a_0` has positive Haar measure.  On
that fibre, `xgx^(-1)=a_0`; if nonempty, its solution set is a coset of the
centralizer `C_G(g)`.  Positive Haar measure makes this centralizer open.
An open subgroup of the `p`-adic analytic group `SL_3(Q_p)` has full Lie
algebra.  Thus `Ad(g)` is the identity on `sl_3(Q_p)`, so `g` is central.

If `g,h in Lambda'` and `[alpha_g]=[alpha_h]`, the same argument applied to
their quotient (up to the harmless reversal from the right-action
convention) shows that `gh^(-1)` is central.  The center of `G` is finite,
while `Lambda'` is torsion-free, so `gh^(-1)=e`.  This proves `(RAF1)`.

Finite amplification does not change the conclusion.  If
`alpha_g tensor id_(M_m)` were implemented by a unitary matrix `(V_ij)` in
`M_m(Q)`, then some nonzero entry would satisfy

```text
V_ij x=alpha_g(x)V_ij             (x in Q).              (RAFP2)
```

Its polar part is a unitary implementing `alpha_g`: both support
projections of `V_ij` are scalar because `Q` is a factor.  Hence stable
innerness implies innerness.

Now suppose the exact orbit-block construction descends from `Lambda'` to a
finite quotient `Lambda'/H`.  Replacing a representative `g` by `gh` must
leave its labelled copy of `Q` unchanged up to an allowed inner coordinate
change.  Cancelling `alpha_g` makes `alpha_h` inner (with the order adjusted
to the right-action convention).  A finite-index subgroup of the infinite
lattice is infinite, so it contains `h!=e`, contradicting `(RAF1)`.  The
matrix-amplified version is excluded by `(RAFP2)`.

Finally `G=SL_3(Q_p)` has property (T), and lattices inherit property (T).
Property (T) implies the fixed-point property FA for actions on trees.
Bass--Serre trees of a nontrivial free product, amalgam, or HNN extension
have no global fixed vertex, so no such decomposition of `Lambda'` exists.
This proves the free-assembly firewall.
