---
rg: 2
id: summed-reynolds-cut-synchronizes-kernel-corners
kind: claim
title: One summed Reynolds cut synchronizes every kernel-word polar corner
distinct_from:
  reynolds-defect-cut-gives-regular-relator-corner: that constructs a carrier for one relator; this uses one spectral cut for a whole finite family and synchronizes all of their polar corrections on it.
  hs-defect-operator-norm-quarantine: that cuts an arbitrary finite defect family but produces no invariant carrier or leakage control; this Reynolds-averages over a finite overlap subgroup, preserves its regular core, and controls every compressed word's Julia leakage.
  compact-hyperbolic-km-regular-microstates-synchronize: that must propagate the common overlap-subgroup carrier through all three rank-two charts; this settles simultaneous extraction for the finite kernel basis at one fixed overlap subgroup.
  summed-reynolds-carrier-transports-only-tautologically: that proves this high-density projection and every corner polar correction extend through all rank-two charts at dimension-free cost, but also proves the extension names only the tautological identity/kernel-word paths and supplies no coefficient from the independently exactified P_13 chart.
---

**ESTABLISHED.**  Let `rho:H->U(D)` be exact for a fixed finite group and
let `Y_1,...,Y_r in U(D)`.  Put

```text
E=sum_a ||Y_a-I||_2^2,
Delta=|H|^(-1) sum_(a,h)
 rho(h)(Y_a-I)^*(Y_a-I)rho(h)^*.                       (SRC1)
```

For `s>0`, set `q=1_[0,s](Delta)` and `beta=tr(q)`.  Then `q` commutes with
`rho(H)` and

```text
beta>=1-E/s.                                           (SRC2)
```

For every `a`, put `C_a=qY_aq`.  There is a unitary `B_a in qM_Dq`
extending the polar part of `C_a` such that

```text
tr_q(q-C_a^*C_a)<=|H|s,
||C_a-B_a||_(2,q)<=sqrt(|H|s),
||C_a-q||_(2,q)<=sqrt(|H|s),                           (SRC3)

||B_a-q||_(2,q)<=2sqrt(|H|s),
||B_a-B_b||_(2,q)<=4sqrt(|H|s).                        (SRC4)
```

Thus all polar corrections live on one carrier and synchronize to the same
corner identity.  Their coherent two-path averages

```text
K_a=(q+B_a)/2
```

satisfy simultaneously

```text
||qY_aq-K_a||_(2,q)<=sqrt(|H|s).                       (SRC5)
```

If `0<E<1`, choosing `s=sqrt(E)` gives

```text
beta>=1-sqrt(E),
||qY_aq-K_a||_(2,q)<=sqrt(|H|) E^(1/4),
||B_a-B_b||_(2,q)<=4sqrt(|H|) E^(1/4).                 (SRC6)
```

When the ambient `H` representation is a regular multiple, `q` contains a
regular `H` summand of ambient relative dimension at least

```text
max(0,1-|H|E/s),                                       (SRC7)
```

and hence at least `1-|H|sqrt(E)` for the optimized choice.

For the finite free basis of the triangle kernel `N`, this removes both the
noncommuting-cut problem and independent polar gauges at one overlap
subgroup.  It does not yet make `q` invariant under `P_1`, `P_3`, or the
three rank-two vertex groups.  The remaining Kac--Moody step is transport of
this one `P_0`-regular carrier through those larger finite charts without
reintroducing cycle holonomy.

The projection-transport part is now closed by
`summed-reynolds-carrier-transports-only-tautologically`: replacing `q` by
the full carrier costs only `E^(1/4)` at the optimized cut.  What remains is
the relative coefficient comparison between its polar path and the
separately exactified `P_13` chart path.
