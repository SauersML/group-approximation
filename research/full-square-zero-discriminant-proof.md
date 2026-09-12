---
rg: 2
id: full-square-zero-discriminant-proof
kind: route
title: Cut the nilpotent at a singular-value gap on each gap set and multiply relative classes
target: full-square-zero-forces-discriminant-power-vanishing
requires:
  - homogeneous-full-square-zero-is-nilpotent-section
---

Let `x` be full and square-zero.  By
`homogeneous-full-square-zero-is-nilpotent-section`, `x_t != 0` for every `t`.
Write `sigma_1(t)>=...>=sigma_N(t)>=0` for the singular values of `x_t` and
put `sigma_(N+1)=0`.  They are continuous in `t` (eigenvalues of `x_t* x_t`
in a local trivialization).

### The gap cover

Put `W_r={t : sigma_r(t) > sigma_(r+1)(t)}` for `r=1,...,s`.  Each `W_r` is
open.  If `rho=rank(x_t)`, then `1<=rho<=s` (range inside kernel) and
`sigma_rho(t)>0=sigma_(rho+1)(t)`, so `t in W_rho`.  The `W_r` cover `X`.

### Constant rank on a gap set

On `W_r` let `h_t(u)` be `0` for `u<=sigma_(r+1)(t)^2`, `1` for
`u>=sigma_r(t)^2`, and linear in between.  It is jointly continuous, so

```text
Q_t = h_t(x_t* x_t)
```

is a continuous field of rank-`r` projections: the spectral projection onto
the top `r` eigenvalues of `x_t* x_t`.  Put `y_t=x_t Q_t`.  The identity
`x h(x*x) = h(xx*) x` gives

```text
y^2 = h(xx*) x x Q = 0,
```

and `y_t` has rank `r` because `sigma_r(t)>0`.  A constant-rank continuous
field has a continuous range projection `P`; since `range y subset ker y` and
`Q` is the orthogonal complement of `ker y`, `PQ=0`.  The map `y` is a
fibrewise isomorphism `QE -> PE`.  Therefore

```text
E|_(W_r) = PE directSum QE directSum (1-P-Q)E ~= K directSum K directSum L,
```

with `rank K=r`.  This is part 1.

### The discriminant

The Chern roots of `K directSum K directSum L` contain each root of `K`
twice, so the universal polynomial `prod_(a<b)(t_a-t_b)^2` vanishes
identically on them.  Hence `Delta(E)|_(W_r)=0` in `H^*(W_r; Z)`.

By the exact sequence of the pair `(X, W_r)`, `Delta(E)` is the image of some
`alpha_r in H^*(X, W_r; Z)`.  Open sets form excisive couples, so the relative
cup product

```text
alpha_1 cup ... cup alpha_s in H^*(X, W_1 union ... union W_s; Z) = H^*(X, X; Z) = 0
```

is defined, and it maps to `Delta(E)^s` in `H^*(X; Z)`.  So `Delta(E)^s=0`.

### The examples

In `H^*((CP^M)^N; Q)=Q[t_1,...,t_N]/(t_a^(M+1))` the monomials with every
exponent at most `M` form a basis.  The polynomial
`prod_(a<b)(t_a-t_b)^(2s)` is nonzero and each `t_a` occurs to degree at most
`2s(N-1)`, so for `M>=2s(N-1)` its class is nonzero.  So `Delta(E)^s != 0`,
and part 2 excludes a full square-zero element.
