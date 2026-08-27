---
rg: 2
id: finite-isotropy-relation-is-central-corner
kind: claim
title: A constant finite-isotropy relation algebra is a central crossed-product corner
distinct_from:
  thom-central-corner-criterion: that selects scalar characters of a finite central subgroup in a group von Neumann algebra; this averages the point-dependent finite stabilizers of a pmp transformation groupoid and selects its trivial-isotropy sector.
  free-actor-extensions-cannot-host-nonce-relation: that proves the stabilizer-forgetting representation is singular for the native non-CE free-group relation; this gives the exact positive normal-corner theorem when stabilizers are finite.
---

Let `Gamma curvearrowright (X,mu)` be an ergodic pmp action whose stabilizers
have the same finite order `m` almost everywhere, let `R` be its orbit
relation, and put `P=L^infinity(X) rtimes Gamma`.  Then

```text
p = (1/m) sum_(g in Gamma) 1_Fix(g) u_g                  (FIC1)
```

converges in `L^2(P)`, is a central projection of trace `1/m`, and there is a
trace-preserving isomorphism

```text
L(R)  ~=  (p P p, m tau_P).                              (FIC2)
```

Under `(FIC2)`, a diagonal function `a` goes to `ap`, and the orbit normalizer
of `g` goes to `pu_g`.  Thus finite isotropy is exactly a positive-trace
trivial-stabilizer sector of the faithful transformation crossed product.

