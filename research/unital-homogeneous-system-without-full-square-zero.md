---
rg: 2
id: unital-homogeneous-system-without-full-square-zero
kind: claim
title: A unital tower of matrix bundle algebras with unbounded rank has no stage admitting a nowhere-zero square-zero section
distinct_from:
  full-square-zero-forces-discriminant-power-vanishing: that obstructs one bundle at a time; this asks for one inductive system whose every stage is obstructed while the rank grows without bound.
  discriminant-obstruction-dies-in-multiplicity-towers: that is a proved no-go for one obstruction along diagonal towers; this is the open existence statement that any successful obstruction would have to deliver.
---

**OPEN.**  There are compact Hausdorff spaces `X_j`, complex vector bundles
`E_j` over `X_j` with `rank E_j -> infinity`, and unital `*`-homomorphisms

```text
Gamma(X_j, End E_j) -> Gamma(X_(j+1), End E_(j+1))
```

such that for no `j` does `End E_j` have a continuous section `x` with
`x_t^2=0` and `x_t != 0` for all `t`.

## Attempts

- **Discriminant.**  `full-square-zero-forces-discriminant-power-vanishing`
  obstructs a single stage whenever `Delta(E_j)^(floor(N_j/2)) != 0`.
  Dead for towers of multiplicity form:
  `discriminant-obstruction-dies-in-multiplicity-towers` shows the power
  vanishes at all large stages.  That dead attempt is recorded as route
  `homogeneous-tower-via-discriminant-obstruction`.
- **Sharper stratum classes (not yet tried).**  The gap cover of that proof
  gives more than a repeated root: on the `r`-th gap set the total Chern class
  factors as `c(K)^2 c(L)`.  Classes that vanish on each such factorization
  locus but are not powers of one discriminant could survive diagonal towers.
  A candidate needs an ideal of characteristic classes, stable under
  multiplicity-form pullback, meeting every stratum ideal.
- **Twisted connecting maps (not yet tried).**  Connecting maps whose spectrum
  map `X_(j+1) -> Sym^k(X_j)` does not lift to `X_j^k` are outside the no-go.
  Their bundles are transfers along finite covers, and within-block root pairs
  need not pull back a fixed earlier class.
