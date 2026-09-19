---
rg: 2
id: same-center-whitehead-cross-gram-closes-native-two-scale
kind: route
title: Restrict both literal prefix Whitehead transports to the common q-center carrier
target: binary-leavitt-native-two-scale-cross-gram-positive
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
  - opnorm-packet-exactification-is-dimension-free
---

The two coefficients in the native scale rows are exactly

```text
c_1=s_(00)t_0,              c_2=s_(000)t_(00),
```

with reverse coefficients `d_1,d_2` as in `(SCW3)`.  Thus `W_1,W_2` are
the literal three-elementary partial-Whitehead stabilizations used by the
depth-one-to-two and depth-two-to-three selector rows; no unrelated unitary
completion or coefficient-path substitute is introduced.

Let `P_z=(1-rho(z))/2` and use the common carrier `F` of `(SCW1)`.  The
same-center construction gives

```text
tau(F)>=tau(P_z)/4.                                    (SCG1)
```

Both Whitehead words commute with the two root involutions defining `F`.
After the fixed Pauli source/target relabelings built into the selector
rows, their restrictions are therefore two unitaries

```text
S_1,S_2:FH->FH
```

and `(SCW5)` gives

```text
tau(S_1^*S_2S_2^*S_1)=tau(F).                         (SCG2)
```

Relative to `F` this is `(NCG1)` with `gamma=1`; relative to the original
marked carrier it has the fixed mass floor `1/4`.  In the Pauli normal form
`(SCW4)`, remove the two canonical adjacent label swaps.  The polar relative
unitary is then `V_1^*V_2` in the common `M_8` multiplicity commutant, so
both mixed source-Pauli commutators vanish.  The braid calculation even makes
the two reservoir involutions conjugate, although `(NCG1)` only needs the
commutant conclusion after the polar cut.

For operator-norm microstates, this is a fixed finite packet.  Apply
dimension-free packet exactification, round the commuting root involutions,
and use fixed-word telescoping for the two Whitehead conjugation tables.
The rounded carrier has trace `(SCG1)-o(1)`, the two restricted maps are
`o(1)`-close to unitaries on it, and `(SCG2)` becomes

```text
tau(S_1^*S_2S_2^*S_1)>=tau(F)-o(1).
```

The mixed commutators are `o(1)` by the same finite-table correction.  All
constants depend only on this depth-three packet.  This proves the scalar
holonomy claim with no Property T, Kazhdan transport, stability theorem, or
literature input.
