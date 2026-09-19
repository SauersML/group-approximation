---
rg: 2
id: el20-order-seven-heads-force-zero-common-hecke-reducing-cut
kind: claim
title: The two EL20 order-seven heads have no positive common reducing subcut of the Hecke character source
invalidates:
  - common-hecke-character-orbit-saturation-closes-oci4
artifacts:
  - research/el20-order-seven-zero-cut-block-proof.md
distinct_from:
  order-seven-first-exit-is-not-seven-step-leakage: that gives a universal seven-cycle counterexample to the claimed one-step telescope; this uses the actual seven Leavitt corner coordinates and proves that the orbit-saturated common-cut repair is zero.
  native-whitehead-corner-collapses-hecke-flags: that treats subcuts reducing the two Whiteheads separately; this treats subcuts reducing the two complete seventh-order heads and obtains an exact incompatible-character commutator.
  middle-index-marked-heisenberg-packet-is-whitehead-equivariant: that gives a positive atom invariant under the two adjacent Whiteheads; this uses the seven-pair packet on all center-chain middle indices and shows why its order-seven invariant atom is disjoint from the required Hecke character.
---

**ESTABLISHED ACTUAL-BLOCK ZERO-CUT FENCE.**  In

```text
G=EL_20(L_(F_2)(1,2))
```

retain the center-chain common source

```text
Q=e_(L_0,lambda_0)
```

from `center-chain-mixed-hecke-overlap-is-common-pauli-source`.  Thus, on
`Q`, the roots

```text
h=x_42(q),       d=x_82(b_2),       f=x_94(b_3)        (OZC1)
```

act respectively as `-1,+1,+1`.  Put

```text
t_1=J_1B_2A_1,                  t_2=J_2B_3A_2.        (OZC2)
```

These are the two exact order-seven heads.  Define

```text
g=t_1^2t_2,                 k=t_1^(-2)t_2t_1^(-1).
```

There is an exact ordinary-word identity in `G`:

```text
[g d g^(-1), k f k^(-1)]=h.                           (OZC3)
```

Consequently, in every unitary representation of `G`, a projection
`E<=Q` which reduces both `t_1` and `t_2` is zero.  Indeed `d` and `f` act
as `+1` on `E`.  Reduction by the two heads makes both conjugates on the
left of `(OZC3)` act as `+1`, so their commutator acts as `+1`; but the
right side acts as `-1`.

The same conclusion holds for asymptotic matrix cuts.  If `E_n<=Q_n` has
positive limiting normalized trace and all word-ball boundary terms needed
to compress `(OZC3)` tend to zero, then the tracial ultraproduct gives a
nonzero `E<=Q` reducing `t_1,t_2`, contradicting the preceding paragraph.
In particular, no orbit-saturated strengthening of `(OCI5)` can retain a
positive common Hecke-character cut.

There is a useful arbitrary-profile interpretation.  The seven middle
coordinates

```text
I={2,4,5,6,7,8,9}
```

carry a seven-pair extraspecial packet centered at the marked root
`z=x_13(q)`.  The all-positive incoming-root atom has exactly `1/128` of
the `z=-1` sector and is fixed by both `t_1,t_2`.  However every element of
`L_0` fixes its label vector with positive sign, whereas `lambda_0(h)=-1`.
Thus this canonical order-seven reducing atom is orthogonal to `Q`.  The
marked Heisenberg packet controls the label factor but leaves precisely the
Hecke-character multiplicity reservoir unconstrained.

This refutes the proposed positive **common reducing active cut**, not the
unconditional non-MF goal.  A surviving route would have to use genuinely
growing, coefficient-sensitive source cuts which change along the six
order-seven iterates and whose separate boundary losses can be paid without
producing one common invariant `L_0`-character corner.  Neither the fixed
order-seven packet, normal-generator active reblocking, nor one-step
operator-norm spectral selection supplies such a construction.

No Property `(T)`, Kazhdan input, canonical trace, or literature result is
used.

DERIVATION
el20-order-seven-zero-cut-block-proof
