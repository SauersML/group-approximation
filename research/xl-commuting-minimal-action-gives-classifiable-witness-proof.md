---
rg: 2
id: xl-commuting-minimal-action-gives-classifiable-witness-proof
kind: route
title: Følner-averaged Reiter witnesses give the quasi-central approximation property on C(X) x Gamma
target: xl-commuting-minimal-action-gives-classifiable-witness
requires: []
---

Notation: `u_gamma` are the canonical unitaries of `A = C(X) x Gamma`, with
`u_gamma f u_gamma^* = f o gamma^-1`.  Since `Gamma` is amenable the full and
reduced crossed products agree.

**0. `alpha` is well defined.**  For `g in G` the map `f -> f o g^-1` is an
automorphism of `C(X)` commuting with every `f -> f o gamma^-1`, so it
extends to an automorphism of the crossed product fixing every `u_gamma`
(universal property).  `g -> alpha_g` is a homomorphism.  Iterating crossed
products gives `A x_alpha G = C(X) x (G x Gamma)`.

**1. `A` is classifiable and stably finite.**
* Simple: the action is free (hence topologically free) and minimal, and
  `Gamma` is amenable (Archbold--Spielberg).
* Nuclear: `C(X)` nuclear and `Gamma` amenable.
* UCT: the transformation groupoid `X x Gamma` is amenable (Tu).
* Finite nuclear dimension: hypothesis 3; references: Guentner--Willett--Yu
  (finite dynamic asymptotic dimension plus finite `dim X`), Szabo--Wu--Zacharias
  for free `Z^d`-actions; for locally finite `Gamma` the dynamic asymptotic
  dimension is `0`, since each finite `K subset Gamma` lies in a finite subgroup.
* `Z`-stable: `A` is simple, separable, unital, nonelementary (`X` infinite)
  with finite nuclear dimension (Winter).
* Traces: `Gamma` amenable gives a `Gamma`-invariant probability measure `mu`,
  and `mu o E` is a trace (`E` the conditional expectation).  A trace on a
  simple unital algebra is faithful, so if `v^*v = 1_n` in `M_n(A)` then
  `tau(1_n - vv^*) = 0` forces `vv^* = 1_n`: `A` is stably finite.
  Freeness gives `T(A) = {mu o E : mu in M_Gamma(X)}`.

**2. Reiter witnesses.**  Topological amenability of `G` on `X` gives, for
every finite `S subset G` and `epsilon > 0`, a continuous map
`m : X -> Prob(G)` with all `m(x)` supported in one finite set `F` and

```text
sup_x || m(g x) - g . m(x) ||_1 < epsilon     (g in S),
```

where `(g.p)(h) = p(g^-1 h)`.

**3. Averaging over `Gamma`.**  Given also a finite `R subset Gamma`, pick a
finite nonempty `E subset Gamma` with `|E gamma Δ E| < epsilon |E|` for
`gamma in R union R^-1` (right Følner set; amenable groups have them).  Define

```text
n(x) = |E|^-1 sum_{s in E} m(s x),        xi(h)(x) = n(x)(h)^{1/2}.
```

`n` is continuous with values in `Prob(F)`, so `xi in C_c(G, C(X))`, supported
in `F`, and `<xi, xi> = sum_h xi(h)^* xi(h) = 1` exactly.

* *Equivariance.*  Because `G` and `Gamma` commute,
  `n(g x) - g.n(x) = |E|^-1 sum_s (m(g s x) - g.m(s x))`, so
  `sup_x ||n(gx) - g.n(x)||_1 < epsilon` for `g in S`.
* *Invariance under `Gamma`.*  `n(gamma^-1 x) = |E|^-1 sum_{t in E gamma^-1} m(t x)`,
  hence `sup_x ||n(gamma^-1 x) - n(x)||_1 <= |E gamma^-1 Δ E|/|E| < epsilon`
  for `gamma in R`.

**4. QAP.**  Let `A` act on `l^2(G, A)` diagonally and let
`(g.xi)(h) = alpha_g(xi(g^-1 h))`.  Using `||p^{1/2} - q^{1/2}||_2^2 <= ||p - q||_1`
for probability vectors (Powers--Størmer on `l^1`), pointwise in `x` and then
the supremum over `x` (all entries lie in the commutative algebra `C(X)`):

```text
|| xi - g.xi ||^2   = sup_x sum_h |n(x)(h)^{1/2} - n(g^-1 x)(g^-1 h)^{1/2}|^2
                   <= sup_x || n(x) - g.n(g^-1 x) ||_1 < epsilon          (g in S),
|| u_gamma xi u_gamma^* - xi ||^2 <= sup_x || n(gamma^-1 x) - n(x) ||_1 < epsilon  (gamma in R),
f xi = xi f   for all f in C(X).
```

Since `||xi|| = 1`, `||a xi - xi a||` is controlled by these estimates on the
generators `C(X) union {u_gamma}` and hence tends to `0` for every `a` in the
dense `*`-algebra and then in `A`.  Letting `S`, `R` exhaust `G`, `Gamma`,
and `epsilon -> 0` gives a net `xi_i in C_c(G, A)` with `<xi_i, xi_i> = 1`,
`||a xi_i - xi_i a|| -> 0` and `||xi_i - g.xi_i|| -> 0`.  This is the
quasi-central approximation property of Buss--Echterhoff--Willett, which
implies amenability of `alpha` (Buss--Echterhoff--Willett; the converse is
Ozawa--Suzuki, Selecta Math. 2021).

Hence `alpha` is an amenable action of `G` on the unital stably finite
classifiable algebra `A`.  QED.

*Calibration.*  With `G` nonexact no amenable `X` exists, so nothing false is
produced.  Consistency with `amenable-action-invariant-trace-forces-amenability`:
a `G`-invariant trace would be `mu o E` with `mu` a `G x Gamma`-invariant
measure, which topological amenability of `G` on `X` forbids for nonamenable `G`.
