---
rg: 2
id: tfd-low-leakage-compressions-flexibly-reduce
kind: claim
title: Low-leakage compressions over property TFD flexibly reduce
distinct_from:
  kazhdan-projection-rounding: that assumes full property T and rounds one projection in a finite tracial algebra; this uses only the uniform finite-dimensional gap, quantifies the rank error, and turns the rounded projection into a flexible exact representation.
  even-weil-fixed-line-compression: that treats one codimension-one arithmetic compression; this applies at arbitrary ambient codimension and to every exact finite-dimensional representation.
  leakage-small-polar-compressions-obey-projective-transfer: that proves one projective trace inequality for SL3 compressions; this produces an actual nearby exact representation in generalized Hilbert--Schmidt distance.
---

Let `Gamma=<S>` have property `(T;FD)` with uniform
finite-dimensional Kazhdan constant `kappa>0`.  Let

```text
pi:Gamma->U(H)
```

be any exact finite-dimensional representation and let `P` be a projection
of rank `d>0`.  With unnormalized Frobenius norm, put

```text
L(P,pi)=sum_(s in S)||(1-P)pi(s)P||_F^2,
ell(P,pi)=L(P,pi)/d.                                    (TLC1)
```

There is a `pi(Gamma)`-invariant projection `Q` and a constant
`C_kappa`, depending only on the fixed Kazhdan pair, such that

```text
||P-Q||_F/sqrt(d) <= C_kappa sqrt(ell(P,pi)),
|rank(Q)-d|/d <= C_kappa^2 ell(P,pi).                  (TLC2)
```

For each `s in S`, let `rho(s)` be any unitary polar completion of
`P pi(s) P` on `PH`.  Then `rho` is at generalized
Hilbert--Schmidt distance

```text
d_2^gen(rho, exact representation) <= C'_kappa sqrt(ell(P,pi))  (TLC3)
```

from an exact representation on a dimension `D>=d`, where

```text
D/d-1 <= C_kappa^2 ell(P,pi).                          (TLC4)
```

If `rank(Q)>=d`, use the exact restriction `pi|_(QH)`.  If
`rank(Q)<d`, add `d-rank(Q)` trivial lines to that restriction.  Thus
`D=max(d,rank(Q))` in both cases.

In particular, let `Gamma=SL_2(Z[1/2])`, which has property `(T;FD)`.
No Toeplitz or Folner construction obtained by polar-compressing genuine
finite-dimensional congruence endpoints can refute the flexible
Dogon--Vigdorovich question if its leakage for the full fixed generator set
is `o(d)`.  This remains true when the compression deletes a positive or
overwhelming fraction of the ambient space.

A compression may be Folner for the amenable `BS(1,4)` core while leaking
macroscopically for the extending involution.  That case is outside
`(TLC1)`.  Therefore an exact-ambient compression counterexample would have
to use at least one of two genuinely different mechanisms:

1. macroscopic leakage for a global generator, followed by cancellation in
   the polar-corrected relators; or
2. an intrinsic approximate tuple which is not a low-leakage compression of
   any exact endpoint.

The theorem does not rule out either mechanism and does not solve flexible
Iwahori exactification.
