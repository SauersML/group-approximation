---
rg: 2
id: kazhdan-approximate-coefficients-have-curved-hodge-control
kind: claim
title: Approximate coefficients of a finitely presented Kazhdan group obey a curved Hodge bound
artifacts:
  - research/artifacts/curved-hodge-heat-transfers-fixed-schreier-mass-2026-09-05.md
distinct_from:
  two-kazhdan-correction-has-quadratic-rank-curvature: that uses all-unitary H2 vanishing to change a tuple and concentrate its relator defects; this uses H1 vanishing to bound cochain energy for an unchanged tuple and an exact comparison representation.
  moving-subgroup-schreier-correction-has-no-index-loss: that extracts exact corners and estimates regular-host spectral count; this supplies the general curved Hodge inequality and contractive heat estimates used to improve a supplied spectral seed.
---

Let G=<S|R> be a fixed finite presentation of a property-(T) group,
with h=|S| and M=|R|. If S lists a generator and its formal inverse
as independent labels, R includes the inverse-consistency relations.
Let U_s be unitaries on C^d, and let rho:G->U(D) be genuine. Set

```text
delta=max_(r in R)||U(r)-I||_(2,d),
T_s(A)=rho(s) A U_s*,       A:C^d->C^D.
```

Normalize every rectangular HS norm by sqrt(d). On cochains use the
sum of the squared component norms. Define d0 by `(d0 A)_s=(T_s-I)A`
and d1 by free-word cocycle extension followed by evaluation on R.
In particular `(d1 d0 A)_r=(T(r)-I)A`, even when U is approximate.

There exist mu>0, C<infinity and delta_*>0, depending only on the
presentation, such that every delta<delta_* and every S-cochain f obey

```text
mu ||f||_2^2 <= ||d0* f||_2^2+||d1 f||_2^2
                  +C delta^2 max_s||f_s||_op^2.       (KCH1)
```

No dimension or operator-norm closeness to rho is assumed. The exact
comparison representation is supplied; this does not construct it.

For any operator contraction A_0, put

```text
L0=d0* d0,        A_t=exp(-t L0)A_0,
E(t)=||d0 A_t||_2^2,       N(t)=||A_t||_2^2,
K0=M+4C.
```

Then A_t remains an operator contraction, and for every t>=0,

```text
E(t)<=E(0)exp(-2mu t)+(K0/mu)delta^2,
N(t)>=N(0)-E(0)/mu-(2K0/mu)delta^2 t.                 (KCH2)
```

Thus positive initial mass with sufficiently small relative energy
survives logarithmic heat time while its energy falls to O(delta^2).
This theorem improves supplied mass; it asserts no positive mass for
an arbitrary approximate tuple in a finite regular host.

DERIVATION
small-curvature-module-and-contractive-heat-proof
