---
rg: 2
id: three-carrier-hidden-line-source-selector-proof
kind: route
title: Cover all four hidden sectors with the three nonzero F2 lines
target: three-carrier-hidden-line-join-crosses-target-but-has-no-range
requires:
  - two-carrier-linear-interference-misses-target-by-five-over-2304
  - jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16
---

## 1. The third line

The three nonzero covectors in the active two-dimensional dual module
are

```text
phi_0=(1,0),             phi_1=(1,1),             phi_2=(0,1).
```

They form one `<k>` orbit and satisfy `phi_0+phi_1+phi_2=0`. Since
`a=qT` has square zero, the corresponding hidden involutions obey

```text
Z_0Z_1Z_2
 =I+aE_(v,phi_0+phi_1+phi_2)
 =I.                                                        (THL7)
```

Thus `Z_2=Z_0Z_1`. It is not a third independent bit; it is the third
nonzero line in the two-bit hidden-sign plane.

The calculation `(TCC3)` applies to all three indices:

```text
mathsf Y_i^(-1)A mathsf Y_i=AWZ_i,
mathsf Y_i^(-1)W mathsf Y_i=WZ_i.                       (THL8)
```

It follows that, in the surviving `tau=+` row,

```text
X_i^*X_i=K_i=G_(sigma,+)(1+Z_i)/2.                     (THL9)
```

Conjugating in the other direction gives
`X_iX_i^*=K_i` as well. Moreover every `mathsf Y_i` fixes all
`Z_j`, so `X_i` commutes with the joint `Z_0,Z_1` spectral
projections. Hence `X_i` is a unitary on the sectors with `Z_i=+1`
and is zero on the sectors with `Z_i=-1`.

## 2. An explicit bounded-below sum

Decompose `G=G_(sigma,+)` into its four hidden-sign sectors

```text
D_(epsilon_0,epsilon_1)
 =G(1+epsilon_0Z_0)(1+epsilon_1Z_1)/4.
```

Because `Z_2=Z_0Z_1`, the active-carrier table is

| sector `(Z_0,Z_1)` | active carriers |
|---|---|
| `(+,+)` | `X_0,X_1,X_2` |
| `(+,-)` | `X_0` |
| `(-,+)` | `X_1` |
| `(-,-)` | `X_2` |

The sum `X=X_0+X_1/4+X_2/16` is block diagonal for this
decomposition. On the last three rows it is a nonzero scalar multiple of
a unitary. On the all-plus row, for every vector `xi`,

```text
||Xxi||
 >=||X_0xi||-(1/4)||X_1xi||-(1/16)||X_2xi||
 >=(1-1/4-1/16)||xi||
 =(11/16)||xi||.                                        (THL10)
```

Therefore `X` is bounded below on every sector; a uniform lower bound
is `1/16`. This proves

```text
X^*X >=(1/256)G,                 supp abs(X)=G.          (THL11)
```

For any projection `R`, `(THL11)` implies that `XR` and `GR` have
the same kernel and hence the same initial support rank. Applying the
established qutrit-cut rank table gives `(THL5)`.

## 3. Exact range obstruction

Left multiplication by the unitary `g_2` preserves the range-support
trace, so

```text
tau(supp abs((g_2XR)^*))=tau(supp abs(XR)).
```

If `g_2XR` had range in `Ee_b`, its range-support trace would be at
most `tau(Ee_b)=1/18`. This contradicts either value in `(THL5)`.
Therefore

```text
(1-Ee_b)g_2XR !=0                                      (THL12)
```

for every target atom `b`. This is a direct algebraic noncontainment,
not merely absence of a proof of containment.

The target-compressed operator `Ee_b g_2XR` does have range in
`Ee_b`, but Murray--von Neumann dimension forces its initial support to
have trace at most `1/18`. Comparing with `(THL5)` gives the stated
minimum losses.

Finally, all three carriers commute with the central line `<h>`: that
line is the kernel of the active `C`-type and fixes the two trivial
coordinates. The two summands of `R` have different `h` characters.
Thus `X` itself preserves, rather than merges, the two source
`h`-sectors. This identifies the missing relation precisely: a future
router must authenticate a nontrivial `h`-transport while retaining the
three-line source support.
