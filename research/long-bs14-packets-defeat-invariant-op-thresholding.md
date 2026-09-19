---
rg: 2
id: long-bs14-packets-defeat-invariant-op-thresholding
kind: claim
title: Long irreducible BS14 packets defeat invariant operator-threshold deletion
distinct_from:
  bs14-residual-invariant-hull-has-unbounded-packet-loss: that uses a Weil boundary vector inside one packet; this gives two explicit exact BS packets which are HS-close but operator-far and computes the thresholded mismatch directly.
  bs14-exact-representation-variety-is-hs-locally-rigid: that proves dimension-free HS near-conjugacy; this shows why it cannot be upgraded to operator proximity by deleting the high singular coordinate subspace.
  bs14-hs-stability-does-not-supply-relative-op-basin: that gives a one-line topology separation; this gives an irreducible long-packet obstruction in which the high-coordinate rank is bounded but its invariant hull and exact type-balancing cost are full rank.
---

For `m>=2`, put

```text
N_m=4^m-1,                 zeta_m=exp(2 pi i/N_m).
```

On the basis `e_j`, `j in Z/m`, let `R_m e_j=e_(j-1)` and define

```text
S_m e_j=zeta_m^(4^j)e_j,
T_m e_j=zeta_m^(2*4^j)e_j.                            (LPT1)
```

Both pairs `(R_m,S_m)` and `(R_m,T_m)` satisfy the exact relation

```text
R U R^*=U^4.                                          (LPT2)
```

The fourth-power orbits in `(LPT1)` have length exactly `m`, and they are
distinct: `2` is not a power of `4` modulo `4^m-1`.  Each representation is
irreducible.  Indeed `S_m` and `T_m` have simple spectrum, so an invariant
subspace is spanned by a subset of their eigenlines, while `R_m` acts
transitively on those lines.

The two exact cores are normalized-HS close.  Pairing equal indices and
using chord length at most angular distance gives

```text
||S_m-T_m||_2^2
 <= (1/m) sum_(j=0)^(m-1) (2 pi 4^j/N_m)^2
 <= 64 pi^2/(135m),                                  (LPT3)
```

while their `R` generators agree exactly.

They nevertheless stay uniformly operator-far under every conjugacy.  The
last spectral point of `T_m` has circle coordinate

```text
2*4^(m-1)/N_m = 1/2+1/(2N_m),
```

whereas every spectral point of `S_m` has coordinate at most

```text
4^(m-1)/N_m = 1/4+1/(4N_m).
```

Its circular distance from `spec(S_m)` is therefore at least `1/4`, so the
spectral Hausdorff distance is at least `sqrt(2)`.  Spectral variation for
normal matrices yields

```text
inf_(W in U(m)) ||W T_m W^*-S_m||_op >= sqrt(2).       (LPT4)
```

This obstruction is concentrated on few coordinate lines.  For every fixed
`theta>0`, the number of indices for which

```text
|zeta_m^(4^j)-zeta_m^(2*4^j)|>theta
```

is `O(log(1/theta))`, independently of `m`; this follows from
`|zeta_m^(4^j)-zeta_m^(2*4^j)|<=2 pi 4^(j-m)/(1-4^(-m))`.
Thus ordinary singular-value thresholding deletes only `o(m)` coordinates
and makes the remaining diagonal matrices operator-close.

But that coordinate cut is not a BS subrepresentation.  By irreducibility,
the smallest BS-invariant projection containing any one of its high lines
has rank `m`.  Exact flexible type balancing has the same full-rank cost:
if `pi,tau` have dimension less than `m`, then

```text
(R_m,S_m) direct_sum pi
```

cannot be unitarily equivalent to

```text
(R_m,T_m) direct_sum tau.
```

Unique decomposition of finite-dimensional unitary representations would
force the irreducible `(R_m,T_m)` type to occur inside `pi`, already costing
dimension at least `m`.

Therefore the proposed synthesis

```text
HS alignment -> singular threshold -> delete/pad the high coordinates
              -> operator-norm aligned exact cores
```

is false whenever deletion and padding must respect the exact BS packet
structure, as they must before applying the exact-point Newton theorem.  A
positive route would have to modify/reconnect the long packet non-invariantly
and prove convergence of the resulting approximate core; invariant hulling
or exact packet balancing turns bounded active rank into full relative rank.

This does not refute every conceivable stabilized **approximate**
operator-alignment: a non-invariant reconnection followed by a joint repair
could in principle evade the representation-monoid obstruction.  It does
refute the direct flexible outlier-removal bridge posed above.
