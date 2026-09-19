---
rg: 2
id: stw99-xciv-internal-zstable-core-centralization-proof
kind: route
title: Centralize inside the approximating regular core and pay only its norm distance
target: stw99-xciv-zstable-core-radius-controls-block-defect
requires:
  - stw99-xciv-single-prime-block-centrality-is-exact
artifacts:
  - research/artifacts/stw99-xciv-zstable-core-radius-audit-2026-08-30.md
---

Let `A subset R` be separable, unital, and `Z`-stable.  Given finite
approximants `b_a in A` to the elements `a in F` and `epsilon>0`, the local
norm-central absorption criterion inside `A` supplies a unital homomorphism

```text
psi:D->A
```

such that

```text
||[b_a,psi(h)]||<epsilon             (a in F,h in H).
```

Consequently

```text
||[a,psi(h)]||
 <=2||a-b_a||+epsilon.                                (6)
```

Infimize over the approximants, then over `A`, and finally let `epsilon`
decrease to zero.  This proves `(2)`, and `(5)` is its contrapositive.

For the finite-nuclear-dimension class, use the theorem of
Castillejos--Evington--Tikuisis--White--Winter: every separable simple unital
nuclear infinite-dimensional C*-algebra of finite nuclear dimension is
`Z`-stable.  No finite-dimensional subalgebra approximation or ambient
relative-commutant hypothesis is needed.

For the scalar-commutant example, take the unique trace `tau_Z` of `Z`.
Simplicity makes its GNS representation faithful.  Its von Neumann closure
is an injective infinite-dimensional finite factor, because `Z` is nuclear,
simple, and monotracial; hence it is the hyperfinite II1 factor `R`.  After
identifying that closure with `R`, the GNS embedding

```text
pi_tau:Z->R
```

is weakly dense.  The commutant of a weakly dense subalgebra equals the
center of its factor closure, proving `(3)`.  On the other hand `Z` is
`Z`-stable, so applying `(6)` with `A=pi_tau(Z)` and `a=b_a` proves `(4)`.

The centralizing maps in this example lie inside the weakly dense norm core;
they do not converge to an exact noncommutative subalgebra of
`pi_tau(Z)' intersect R`.  All commutator estimates are nevertheless in
operator norm.
