---
rg: 2
id: flat-calibrations-refute-bounded-degree-two-primitives-proof
kind: route
title: Pack compact flat calibrations into residual finite covers
target: flat-calibrations-refute-bounded-degree-two-primitives
requires: []
---

Write

```text
X = SL_N(R) / SO(N).
```

We construct a uniformly bounded coboundary whose boundary pairing forces
every primitive to have norm linear in a free scale `R`.

## 1. A compactly supported flat calibration

Let

```text
H = [[2,1],[1,1]],
A = diag(H,I_(N-2)),
B = diag(I_2,H,I_(N-4)).
```

The matrices `A,B in Gamma` commute and translate independently on a common
Euclidean 2-flat in `X`. After rescaling two Busemann-coordinate
combinations, choose smooth functions `x,y:X->R` whose restrictions to this
flat are affine coordinates with

```text
x(Ap)=x(p)+1,  x(Bp)=x(p),
y(Ap)=y(p),    y(Bp)=y(p)+1,
```

and whose differentials are uniformly bounded.

Let `chi_R` equal one on a neighborhood of the flat rectangle with vertices
`p,A^R p,A^R B^R p,B^R p`, have support in an `O(R)`-neighborhood of it,
and satisfy `||d chi_R||_infty=O(1/R)`. Put

```text
omega_R = chi_R x dy.
```

On the support of `chi_R`, `|x|=O(R)`, and therefore

```text
d omega_R = chi_R dx wedge dy + x d chi_R wedge dy,
||d omega_R||_infty <= C
```

with `C` independent of `R`. The cutoff width of order `R` is essential in
the second estimate. Stokes on the flat rectangle gives

```text
integral_(boundary rectangle) omega_R = kappa R^2
```

for a fixed `kappa>0`.

Map the universal cover `K_tilde` equivariantly to `X`: send vertices by the
orbit map, each generator edge by a fixed path, and each translate of a
relator cell by the corresponding translate of a fixed filling disc. Define
the cellular 1-cochain

```text
v_R(e) = integral_(Phi(e)) omega_R.
```

Properness of the `Gamma`-action and compact support of `omega_R` make
`v_R` finitely supported. For

```text
c_R^0 = delta v_R,
```

Stokes on the finitely many fixed relator discs gives

```text
||c_R^0||_infty <= C_0                                  (1)
```

with `C_0` independent of `R`.

Let `b_R` be the cellular word loop labelled `[A^R,B^R]`. Replacing each
straight flat side by the repeated fixed word path costs `O(R)` strips of
uniformly bounded area. Enlarging the cutoff-one region to contain those
strips and using the uniform bound on `d omega_R` yields constants `a,b>0`
such that, for all large `R`,

```text
|<v_R,b_R>| >= a R^2,        ||b_R||_1 <= b R.           (2)
```

The loop is null because `A` and `B` commute. Choose a finite cellular
2-chain `z_R` in `K_tilde` with `partial z_R=b_R`; an `R` by `R` grid of a
fixed diagram for `[A,B]` will do. Cellular Stokes gives

```text
<c_R^0,z_R> = <v_R,b_R>.                                 (3)
```

## 2. Positive-density packets in finite covers

Fix `R`. Since `Gamma` is residually finite, choose normal finite-index
subgroups `Gamma_n` with quotients `Q_n=Gamma/Gamma_n`, with `|Q_n|->infty`,
such that the quotient maps are eventually injective on every prescribed
finite subset.

Choose a finite label-neighborhood `E_R subset Gamma` containing the
supports of `v_R,c_R^0,z_R,b_R` and their cellular incidence neighborhoods.
Require injectivity on `E_R^(-1)E_R`.

Finite-support cochains descend by **periodization**, not by naive
pushforward. If `q_n:Gamma->Q_n` and `Gamma_n=ker q_n`, set, in cellular
coordinates,

```text
(P_n f)(Gamma_n g e_j) = sum_(h in Gamma_n) f(h g e_j).
```

The sum is finite, `P_n` commutes with `delta`, and injectivity on
`E_R^(-1)E_R` makes `P_n f` one undistorted local copy of `f`. Chains use
the ordinary cellular pushforward. Pairings between the periodized cochains
and pushed chains are preserved.

In each sufficiently large `Q_n`, choose a maximal set `T_n` for which the
translates `t q_n(E_R)`, `t in T_n`, are pairwise disjoint. Maximality gives

```text
Q_n = T_n q_n(E_R E_R^(-1)),
k_n := |T_n| >= |Q_n| / |E_R E_R^(-1)| =: p_R |Q_n|,     (4)
```

where `p_R>0` because `R` is fixed. Sum the disjoint translated packets:

```text
V_n = sum_(t in T_n) t P_n(v_R),
C_n = delta V_n = sum_(t in T_n) t P_n(c_R^0),
Z_n = sum_(t in T_n) t (q_n)_*(z_R),
B_n = partial Z_n.
```

Disjointness, (1)--(3), and normalized cellular pairing give

```text
||C_n||_infty <= C_0,                                    (5)
|<C_n,Z_n>_n| >= (k_n/|Q_n|) a R^2,                      (6)
||B_n||_(1,n) <= (k_n/|Q_n|) b R,                        (7)
||Z_n||_(2,n)^2
  = (k_n/|Q_n|) ||z_R||_2^2 = O_R(1).                    (8)
```

The positive lower density in (4) is essential: a single packet would
vanish in normalized trace as `|Q_n|->infty`.

## 3. Diagonal matrix coefficients

Let `lambda_n` be the left regular permutation representation of `Q_n` on
`l^2(Q_n)`, let `D_n` be the diagonal maximal abelian subalgebra of
`M_(|Q_n|)`, and form

```text
M_R = product_omega M_(|Q_n|) / I_2,
pi_R = [lambda_n o q_n].
```

If `K` has `m_j` cell orbits in degree `j`, the standard identification

```text
C^j(K; (D_n)_(Ad lambda_n)) = D_n^(m_j)
                            = C^j(Gamma_n\K_tilde; C)
```

intertwines the cellular differentials. Matrix operator norm on `D_n` is
the cellular supremum norm, and normalized matrix `L^2` norm is normalized
cellular `l^2` norm (up to fixed packet conventions depending only on `K`).

Thus `C=[C_n]` is an `M_R`-valued 2-cocycle for `Ad pi_R`. It is already an
`M_R`-valued coboundary:

```text
C = delta [V_n].
```

Indeed, for fixed `R`, disjointness gives
`sup_n ||V_n||_infty=||v_R||_infty<infinity`. Equation (5) gives
`||C||_op<=C_0`.

## 4. Conditional expectation cannot hide the calibration

Let `U=[U_n]` be any `M_R`-valued 1-cochain with `delta U=C`. Choose lifts
of its finitely many components bounded by `||U||_op+epsilon`. Let

```text
E_n : M_(|Q_n|) -> D_n
```

be diagonal conditional expectation. It is operator-norm and `L^2`
contractive and is `Ad lambda_n`-equivariant. Hence, for `F_n=E_n(U_n)`,

```text
e_n := delta F_n - C_n,
||e_n||_(2,n) ->_omega 0,
||F_n||_infty <= ||U||_op + epsilon.                     (9)
```

Pair (9) with `Z_n`. Using (6)--(8) and cellular duality,

```text
(k_n/|Q_n|) a R^2
 <= (||U||_op+epsilon) (k_n/|Q_n|) b R
    + ||e_n||_(2,n) ||Z_n||_(2,n).
```

Take the ultralimit. Since `k_n/|Q_n|>=p_R>0`, divide by that density and
then let `epsilon->0`. Every primitive satisfies

```text
||U||_op >= a R / b.                                    (10)
```

Equations (5) and (10) prove the target. If the constant `C_N` asserted by
[[bounded-degree-two-primitives-for-higher-rank-lattices]] existed, choose
`R>b C_N C_0/a`. The cocycle `C` is even a bounded coboundary, but no
primitive can satisfy `||U||_op<=C_N||C||_op`, a contradiction. `QED`
