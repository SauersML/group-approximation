---
rg: 2
id: stw93-matrix-ultraproduct-centralization-no-go
kind: route
title: Put a trace-zero rank-one projection into the defining relative commutant
target: stw93-abstract-central-factorization-can-fail
requires: []
artifacts:
  - research/artifacts/stw93-central-factorization-no-go-audit-2026-08-30.md
---

Let `n_k->infinity`, fix rank-one projections `p_k in M_(n_k)`, and form
the norm ultraproduct

```text
M=product_omega M_(n_k),          p=[(p_k)] in M.
```

The matrix algebras have uniform singleton Dixmier constants independent of
dimension.  Coordinatewise averaging therefore shows that `M` has its
unique normalized trace

```text
tau([(x_k)])=lim_omega tr_(n_k)(x_k).
```

Put `B=C*(1,p)` and `D_0=M intersect B'=M intersect {p}'`.  This is a
separable defining algebra and a genuine relative commutant.  Commutation
with `p` removes the off-diagonal corners, so

```text
D_0=pMp direct_sum (1-p)M(1-p).                         (1)
```

Since `tr_(n_k)(p_k)=1/n_k->0`, the projection `p` belongs to
`I_0=J_tau intersect D_0`.  Its first corner is

```text
pMp=Cp,                                                  (2)
```

because every `p_k M_(n_k) p_k` is one-dimensional.  Projection onto the
first summand of `(1)` therefore defines a normalized trace `s` on `D_0`
with `s(p)=1`.  Every self-commutator in `D_0` is killed by `s`, so

```text
p notin Com_sa(D_0).                                     (3)
```

On the other hand, unique trace of `M` and the Cuntz--Pedersen annihilator
theorem give

```text
Com_sa(M)={x in M_sa:tau(x)=0}.
```

Thus `p in Com_sa(M)`, proving the failure of ambient-to-relative
centralization.  More generally every element of `(I_0)_sa` has zero
ambient trace, so the same annihilator identity gives
`(I_0)_sa subset Com_sa(M)`.

It remains to check that the tracial quotient has the same factor form as
in the XCIII reduction.  Let `J_tau` be the square-null ideal of `M`.  The
quotient `M/J_tau` is the tracial ultraproduct of the growing matrix
algebras and is a II_1 factor.  The map

```text
D_0 -> M/J_tau
```

is onto.  Indeed, for a bounded representative `(x_k)`, replace it by its
`p_k`-block diagonal part

```text
x_k'=p_kx_kp_k+(1-p_k)x_k(1-p_k).
```

Then `[(x_k')] in D_0`, while the two discarded off-diagonal corners have
normalized `2`-norm at most `||x_k||/sqrt(n_k)` and hence vanish in the
tracial quotient.  The kernel is exactly `I_0`, so

```text
D_0/I_0 ~= M/J_tau,
```

a II_1 factor.

Finally, exact central block assembly cannot reduce norm defects.  If
`e_1,...,e_m` are orthogonal central projections and each `e_j` commutes
with `x_j` and `a`, then

```text
[sum_j e_jx_j,a]=sum_j e_j[x_j,a],
||sum_j e_j[x_j,a]||=max_j ||e_j[x_j,a]||.               (4)
```

The same orthogonality makes self-commutator sums split cornerwise.  Thus
Z-central block cutdowns preserve algebraic sums but replace averaging by a
maximum in operator norm; they cannot by themselves centralize the moving
Powers factors.

**Trust boundary.**  The ambient algebra, its trace, its uniform averaging,
the relative commutant, and the factor quotient all have the desired formal
features.  The base algebra `B=C*(1,p)` is not faithfully traced because it
contains `p in J_tau`.  The actual XCIII diagonal copy is faithfully traced
and contains the full free-group factor, so this example rules out only an
abstract factorization lemma which ignores those extra inputs.
