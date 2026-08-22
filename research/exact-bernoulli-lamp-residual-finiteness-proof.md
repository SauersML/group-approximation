---
rg: 2
id: exact-bernoulli-lamp-residual-finiteness-proof
kind: route
title: Pass finite character multisets to Bernoulli measure and eliminate every actor fixed set
target: exact-bernoulli-lamp-trace-forces-actor-residual-finiteness
requires: []
---

For `chi in A_hat`, let `E_(n,chi)` be the joint spectral projection of the
commuting involutions `rho_n(A)` and put

```text
mu_n({chi})=rank(E_(n,chi))/d_n.                         (BER1)
```

Only finitely many projections are nonzero.  If the dual action is written
`g chi`, exact semidirect-product covariance gives

```text
rho_n(g) E_(n,chi) rho_n(g)^*=E_(n,g chi).              (BER2)
```

Thus the ranks are constant on each orbit.  More concretely,

```text
Omega_n={(chi,j):E_(n,chi)!=0, 1<=j<=rank(E_(n,chi))}
```

is a finite `H`-set under `g(chi,j)=(g chi,j)`, and its uniform pushforward to
`A_hat` is `mu_n`.  No choice of bases in the character spaces, and no
untwisting of the internal multiplicity cocycle, is needed.

For `a in A`, Fourier inversion on the character decomposition gives

```text
integral chi(a) dmu_n(chi)=tr_(d_n)(rho_n(a)).           (BER3)
```

The right side tends to `0` for `a!=1` and equals `1` for `a=1`.  These are
the Fourier coefficients of Haar measure `mu` on the compact metrizable group
`A_hat`.  Finite linear combinations of the characters are uniformly dense
in `C(A_hat)` by Stone--Weierstrass.  Hence `(BER3)` implies
`mu_n -> mu` weak-*.

Fix `g!=1`.  The set `Fix(g)` is an intersection of coordinate equalities and
is therefore closed.  If `g` has finite order `r>1`, its regular action on `H`
has infinitely many disjoint `r`-cycles.  A Bernoulli coloring is constant on
the first `N` such cycles with probability

```text
(2/2^r)^N -> 0.
```

If `g` has infinite order, one `g`-orbit contains arbitrarily many distinct
coordinates, and the probability that the first `N` have one common color is
`2^(1-N) -> 0`.  Thus `mu(Fix(g))=0` in both cases.  Portmanteau for the closed
set gives `(BEL2)`.

Choose `n` with `mu_n(Fix(g))<1`.  Some `(chi,j) in Omega_n` is moved by `g`,
so the finite permutation action `H -> Sym(Omega_n)` separates `g`.  Repeating
this for every `g!=1` proves that `H` is residually finite.

