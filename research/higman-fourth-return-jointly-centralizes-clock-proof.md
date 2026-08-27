---
rg: 2
id: higman-fourth-return-jointly-centralizes-clock-proof
kind: route
title: Commute the fourth power past its own matcher and intersect the two clock commutants
target: higman-fourth-return-jointly-centralizes-clock
requires: []
---

Put `B=K P K^*` and `C=K^4`.  Since `C` commutes with `K`,

```text
[C,B] = K [C,P] K^*.
```

Also

```text
||[C,P]||
 = ||CPC^*-P||
 = r.                                                (1)
```

Consequently `||[C,B]||=r`.  The matcher error is `||D-B||=epsilon`,
so the triangle inequality and unitarity of `C` give

```text
||[C,D]||
 <= ||[C,B]||+||C(D-B)||+||(D-B)C||
 <= r+2epsilon.                                      (2)
```

This proves `(HJC2)`.

It remains to compute the exact joint commutant for the periodic packet.
The eigenvalues of `D` are the `q` distinct `q`-th roots of unity.  Hence a
matrix commuting with `D` is diagonal, say `T=diag(c_x)`.  It also commutes
with the permutation `P` exactly when

```text
c_(2^(-1)x)=c_x                                      (3)
```

for every `x in Z/qZ`.  Multiplication by `2^(-1)` fixes zero.  For each
`1<=m<=n`, the residues of additive order `3^m` form one orbit: their number
is `phi(3^m)=2*3^(m-1)`, and `2` has exactly that order modulo `3^m` by the
lifting-the-exponent calculation already given in
`periodic-higman-bs-clocks-have-three-opnorm-small-seams-proof`.  There are
therefore exactly `n+1` orbits.  Equation `(3)` says precisely that `T` is
constant on each one, proving `(HJC3)`.  Its unitary elements choose one
circle phase independently on each orbit, so they form an `(n+1)`-torus.

No perturbation-to-commutant assertion is used: `(1)--(3)` prove only the
simultaneous almost-centrality and the exact commutant calculation stated in
the claim.
