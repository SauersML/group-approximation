---
rg: 2
id: raw-unitary-traffic-gauge-instability-proof
kind: route
title: A conjugated regular C2 representation sweeps the full fork-moment interval
target: raw-unitary-traffic-gauge-instability
requires: []
---

Take

```text
P = [[0,1],[1,0]],             e = (1,1)/sqrt(2).
```

`P^2=I` and `tr(P)/2=0`, so `P` is the two-dimensional regular
representation of `C_2`.  For any `Q in U(2)`, `U=Q P Q^*` has the same two
properties, hence gives exactly the same zero-defect regular group table.

Let `T` be the fork with root `r`, leaves `v,w`, the edge `r -> v` labelled
by `g`, and `r -> w` labelled by the identity.  The plain traffic moment is

```text
tau_T(U)
 = (1/2) sum_{i,j,k} U_{j i} I_{k i}
 = (1/2) sum_{i,j} U_{j i}
 = <e, U e>.
```

Therefore

```text
tau_T(Q P Q^*) = <Q^* e, P Q^* e>.
```

Let `v_+=(1,1)/sqrt(2)` and `v_-=(1,-1)/sqrt(2)` be the `+1` and `-1`
eigenvectors of `P`.  Given any `t in [-1,1]`, set

```text
v_t = sqrt((1+t)/2) v_+ + sqrt((1-t)/2) v_-.
```

Then `||v_t||=1` and `<v_t,Pv_t>=t`.  Choose a unitary `Q` with `Q^* e=v_t`;
such a `Q` exists because the unitary group acts transitively on the unit
sphere.  This gives `tau_T(U)=t`.

For `U=P` in its permutation basis, every column sum is one, so
`tau_T(P)=1`; equivalently the spanning-tree formula in
`permutation-traffic-is-simultaneous-fixed-points` gives `1` because the fork
has no non-tree edges.  Taking `t=-1` gives deviation `2` with exact table
relations and exact regular trace.

The obstruction is pure gauge: `P` and every `Q P Q^*` are the same
representation up to simultaneous conjugacy.  Hence raw matrix-entry traffic
moments cannot be the basis-free quantity that bridges a hyperlinear table to
a permutation traffic law.
