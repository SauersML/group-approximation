---
rg: 2
id: finite-schreier-holonomy-is-the-simultaneous-lamp-gauge-obstruction
kind: claim
title: Finite Schreier holonomy is the exact obstruction to a simultaneous lamp gauge
distinct_from:
  moving-lamp-refinement-cocycle-has-diffuse-fibers: that identifies the refinement/action-groupoid cocycle and proves union gluing; this computes its finite simultaneous-gauge obstruction on every exact regular packet.
  elementary-abelian-regular-normalizers-have-diffuse-fibers: that gives a diffuse multiplicity countermodel far from monomials; this gives an exact spanning-tree criterion and a multiplicity-one bent-phase countermodel which no commutant gauge spatializes.
  spherical-short-holonomies-admit-local-gauge: that is an open geometric-local permutation correction theorem; this is an exact unconstrained unitary connection theorem with no geometric locality conclusion.
artifacts:
  - notes/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md
---

**ESTABLISHED EXACT FINITE CRITERION; GLOBAL LIMIT OPEN.**  Let `Y` be a
finite connected directed multigraph with reverse edges, and put one copy of
`C^k` at each vertex.  A unitary connection is a family `c_e:C^k->C^k`
with `c_(bar e)=c_e^*`.  Given two connections `c,p`, choose a root
`o` and a spanning tree `T`.  Let `C_v,P_v` be their transports along
the tree path from `o` to `v`.  For every oriented chord `e:v->w`, put

```text
Hol_c(e)=C_w^* c_e C_v,       Hol_p(e)=P_w^* p_e P_v.   (FSH1)
```

There are vertex gauges `z_v in U(k)` satisfying

```text
p_e=z_w c_e z_v^*                                      (FSH2)
```

on every edge if and only if one unitary `W in U(k)` simultaneously
conjugates every fundamental-cycle holonomy:

```text
Hol_p(e)=W Hol_c(e) W^*                                 (FSH3)
```

for every chord.  This is also quantitatively exact.  For arbitrary `W`,
set `z_v=P_v W C_v^*`.  All tree-edge errors vanish, and on each chord

```text
||p_e-z_w c_e z_v^*||_2
 =||Hol_p(e)-W Hol_c(e)W^*||_2.                         (FSH4)
```

Thus the maximum, sum, or sum of squares of the residual chord errors is
exactly the corresponding holonomy-conjugacy cost.  There is one independent
root gauge `W` per connected component.

## Lamp-Schreier consequence

Let `B` be finite elementary abelian and let

```text
rho=lambda_B tensor 1_k
```

be its regular packet.  Fourier decomposition gives equal fibers indexed by
`dual(B)`.  Actor generators produce a finite Schreier graph on these
characters.  Any two exact unitary normalizer families `U_s,V_s` inducing
the same action on `B` give two connections on that graph.  There is a
single lamp-commutant gauge

```text
Z=direct_sum_(chi in dual(B)) z_chi
```

with `V_s=Z U_s Z^*` for every generator if and only if their chord
holonomy tuples satisfy `(FSH3)` on every character orbit.  In particular,
gauging `U_s` to a proposed permutation normalizer family is exactly a
finite simultaneous conjugacy test on stabilizer holonomies.  If the actor
relations are exact, these holonomies factor through the character
stabilizers.

This is the precise finite-cycle datum absent from lamp covariance.
Covariance fixes the endpoints of each block transport; it puts no
smallness or spatiality condition on a return around a stabilizer loop.
Property `(T)` alone does not make an arbitrary finite-dimensional
stabilizer representation trivial or permutation.

## Multiplicity-one canonical-trace obstruction

The failure is already present with one regular orbit and no diffuse
multiplicity.  Let

```text
B_m=(C_2)^(2m),       d_m=|B_m|=2^(2m),
q_m(x)=sum_(j=1)^m x_(2j-1)x_(2j) mod 2,
f_m(x)=(-1)^(q_m(x)).
```

On the Fourier side of `ell^2(B_m)`, let `U_m=diag(f_m)`.  Then
`U_m^2=1` and `U_m` commutes with the regular lamp action.  The quadratic
form is bent:

```text
|d_m^(-1) sum_x f_m(x)(-1)^(a dot x)|=d_m^(-1/2)        (FSH5)
```

for every `a in B_m`.  Consequently, for
`A=direct_sum_N C_2`, the exact representations

```text
pi_m(a,t^epsilon)=lambda_(B_m)(a|_(2m)) U_m^epsilon,
                     t^2=1, [t,A]=1                    (FSH6)
```

have canonical group trace asymptotically: every fixed nonidentity word has
normalized trace tending to zero.

No lamp-commutant gauge sends `U_m` to a permutation normalizer inducing
the identity on `B_m`.  Indeed the regular permutation centralizer consists
of right translations, whose Fourier phases are the linear characters
`x |-> (-1)^(b dot x)`; the nonlinear bent phase `f_m` is none of them.
Since the regular commutant is diagonal on the one-dimensional Fourier
fibers, its gauges do not change `f_m`.

In the original group basis every entry of `U_m` has modulus
`d_m^(-1/2)`.  Hence

```text
inf_(M monomial)||U_m-M||_2^2 >= 2-2/sqrt(d_m).         (FSH7)
```

After adjoining an arbitrary unitary block of size `r_m=o(d_m)`, the
right side becomes at least

```text
2-2(sqrt(d_m)+r_m)/(d_m+r_m) -> 2.                     (FSH8)
```

All actor products, all lamp covariances, and all finite-window refinement
identities are exact.  This rules out both metric rounding of the supplied
normalizers and their spatialization by lamp-commutant gauges under the
stated local hypotheses.

It still does **not** rule out permutation transfer: the identity permutation
is a different exact actor representative for the amenable group
`A times C_2`.  The surviving Kun--Thom seam is to construct some coherent
permutation target from the matrix model, not to conjugate the given
normalizers to one.  Across growing moving windows one must also choose
targets whose stabilizer-holonomy profiles and root gauges are compatible
under every refinement.  No such theorem is proved here, so the
nonhyperlinearity route remains OPEN.

DERIVATION
finite-schreier-holonomy-criterion-proof
