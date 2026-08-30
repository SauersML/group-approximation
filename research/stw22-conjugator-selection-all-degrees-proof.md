---
rg: 2
id: stw22-conjugator-selection-all-degrees-proof
kind: route
title: Lift finite-dimensional sphere families through uniformly contractible conjugator fibres
target: stw22-hyperfinite-stiefel-all-sphere-fillings
requires: []
artifacts:
  - research/artifacts/stw22-all-degree-weighted-selection-audit-2026-08-30.md
---

Use the conjugator fibres from
`stw22-lift-and-contract-small-stiefel-loops-proof`:

```text
G(e,p;v_0,v)={u in U(eRe):uv_0=v} subset L^2(R).       (AD1)
```

That route proves uniformly over all parameters that these fibres are
nonempty and closed, that the resulting multifunction is lower
semicontinuous, and that

```text
dist(e,G(e,p;v_0,v))<13||v-v_0||_2.                   (AD2)
```

## Uniform equi-connectivity in every degree

Fix one fibre `G=u_0H`, where

```text
H={h in U(eRe):hv_0=v_0}
 =q_0+U((e-q_0)R(e-q_0)),       q_0=v_0v_0^*.
```

The Popa--Takesaki semigroup on the hyperfinite complement corner gives a
jointly continuous contraction `alpha_t:H->H` with

```text
alpha_0=id,       alpha_infinity=e,
||alpha_t(h)-alpha_t(h')||_2<=||h-h'||_2.               (AD3)
```

The zero-complement case is trivial.  If a map `h:S^j->G` has image
diameter below `delta`, choose `z_0` and contract

```text
(z,t) |-> h(z_0)alpha_t(h(z_0)^*h(z)).                 (AD4)
```

This remains in `G`, extends over `B^(j+1)`, and has image diameter at
most `2delta`.  The same estimate works for every `j` and every fibre.
Hence the family `(AD1)` is uniformly equi-`LC^n` for every finite `n`,
with moduli independent of `e,p,v_0,v`; every fibre is contractible.

## Controlled lifting of small sphere maps

Fix `k>=1`.  Apply Gutev's controlled Michael theorem, Theorem 5.3, with
`n=k-1` to the common uniformly equi-`LC^(k-1)` family `(AD1)`.  It gives,
for every `epsilon>0`, a number `gamma_k(epsilon)>0` depending only on the
uniform modulus `(AD4)`.  If

```text
sup_z||v(z)-v_0||_2<gamma_k(epsilon)/13,
```

then `(AD2)` makes the constant map `z|->e` a continuous
`gamma_k(epsilon)`-selection of

```text
z |-> G(e,p;v_0,v(z)).
```

The controlled theorem supplies an exact continuous lift

```text
u:S^k->U(eRe),       u(z)v_0=v(z),
sup_z||u(z)-e||_2<epsilon.                             (AD5)
```

The Popa--Takesaki contraction of `U(eRe)` fills `u` without increasing
its radius; multiplication by `v_0` gives the required Stiefel filling.
The case `k=0` is the principal-log path estimate already proved in the
degree-zero argument.  Taking
`rho_k(epsilon)=gamma_k(epsilon)/13` proves the uniform assertion.

For an arbitrary, not necessarily small, map `S^k->V(p,e)`, apply
Michael's *Continuous Selections II*, Theorem 1.2, with parameter space
`S^k`, complete target `L^2(R)`, and `n=k-1`.  The dimension hypothesis is
`dim(S^k)=k=n+1`.  The multifunction `(AD1)` is lower semicontinuous with
nonempty closed values; `(AD4)` makes the value family equi-`LC^(k-1)` and
each value `(k-1)`-connected (indeed contractible).  The theorem therefore
selects an exact continuous unitary lift.  Contracting that lift proves
that every `V(p,e)` is `k`-connected.  For `k=0`, transitivity followed by
a principal-log unitary path gives path connectivity directly.

The controlled theorem used here is V. Gutev,
[*Constructing selections stepwise over skeletons of nerves of covers*](https://www.math.bas.bg/serdica/2018/2018-137-154.pdf),
Serdica Math. J. 44 (2018), Theorem 5.3.  The contraction estimate is
Popa--Takesaki, Corollary 2, in the nonexpansive form reproduced by
Theorem 2.3 of
Farah--Vaccaro,
[*Continuous Selection of Unitaries in II_1 Factors*](https://arxiv.org/abs/2501.01272).
