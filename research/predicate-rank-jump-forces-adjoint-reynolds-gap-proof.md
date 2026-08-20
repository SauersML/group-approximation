---
rg: 2
id: predicate-rank-jump-forces-adjoint-reynolds-gap-proof
kind: route
title: Compute both commutants from packet branching and apply Cauchy-Schwarz
target: predicate-rank-jump-forces-adjoint-reynolds-gap
requires:
  - predicate-rank-gate-doubles-restriction-multiplicity
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

For each assignment `x`, index the irreducible `B_f` modules above that
central character by `lambda`, and let their multiplicities in `rho` be
`m_(x,lambda)`.  Put `M_x=sum_lambda m_(x,lambda)`.  Distinct `lambda` may
record radical characters of `B_f`, but every such module restricts to the
same unique `A_f` spin module `S_x`, with multiplicity `2^(f(x))`.  Selectors
belong to `A_f`, so the `S_x` for distinct `x` remain inequivalent.  Therefore

```text
dim End_(B_f)(H_-)=sum_(x,lambda) m_(x,lambda)^2,
dim End_(A_f)(H_-)=sum_x (2^(f(x)) M_x)^2.             (ARG2)
```

Every allowed-sector contribution to the second dimension minus the first is
`M_x^2-sum_lambda m_(x,lambda)^2>=0`.  For forbidden `x` it is

```text
4 M_x^2-sum_lambda m_(x,lambda)^2 >= 3 M_x^2.
```

A forbidden `B_f` simple has dimension `2D`, hence, if `h=qd` is the total
forbidden Hilbert dimension,

```text
h=2D sum_(x:f(x)=1) M_x.
```

Cauchy--Schwarz over the `K` forbidden assignments now gives

```text
dim End_(A_f)(H_-)-dim End_(B_f)(H_-)
 >= 3 sum_(x:f(x)=1) M_x^2
 >= 3 h^2/(4D^2K).
```

Finite-group conjugation averages are orthogonal projections onto these two
commutants.  The subgroup inclusion gives `R_BR_A=R_B`, so their rank
difference equals the displayed commutant-dimension difference.  Divide by
`d^2` to obtain `(ARG1)`.

