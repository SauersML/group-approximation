---
rg: 2
id: two-primary-phase-lift-obstruction-proof
kind: route
title: Reduce Clifford phases at the cyclotomic prime above two and use finite von Neumann direct finiteness
target: modular-one-sided-inverse-has-no-clifford-phase-lift
requires: []
artifacts:
  - research/artifacts/two-primary-phase-lift-obstruction-2026-08-21.md
---

## Direct proof

All coefficients of `A` and `B` lie in `O=Z[zeta_(2^m)]`.  The ideal
`p=(1-zeta_(2^m))` is the unique cyclotomic prime above two needed here, and

```text
O/p = F_2,              zeta_(2^m) = 1 mod p.
```

Thus coefficientwise reduction `O[G]->F_2[G]` sends `A` to `a` and `B` to
`b`.

The complex group algebra `C[G]` is directly finite.  Indeed its left regular
representation embeds it faithfully in the finite von Neumann algebra
`L(G)`.  If `AB=1`, finiteness of `L(G)` gives `BA=1`; faithfulness returns
that equality to `C[G]`, hence to `O[G]`.  Reducing it modulo `p` gives
`ba=1`, contrary to the hypothesis.  Therefore no phase lift exists.

For the quantitative statement fix `m,S,T`.  There are only finitely many
pairs `(alpha,beta)`.  None has `AB=1`, so

```text
delta = min_(alpha,beta) ||AB-1||_(2,L(G)) > 0.
```

In any regular-trace hyperlinear approximation of a finite window containing
`S,T,ST`, the Gram matrix of the represented group words converges to the
canonical group-basis Gram matrix.  Hence the normalized Hilbert--Schmidt
norm of each corresponding phase-decorated product converges to its
`L(G)`-norm.  Since the phase menu is finite, the same `delta` excludes
asymptotic `AB=1` uniformly, even when the phase assignment varies with the
matrix dimension.
