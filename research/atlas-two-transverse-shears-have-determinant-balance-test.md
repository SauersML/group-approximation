---
rg: 2
id: atlas-two-transverse-shears-have-determinant-balance-test
kind: claim
title: Two transverse Atlas shears balance CK branches exactly off a determinant-zero face
distinct_from:
  atlas-first-transverse-root-shear-leaves-fixed-character-face: that computes one order-two shear and its three coarse CK cases; this intersects the two shortest independent transverse directions and gives the exact marked-preserving balance criterion.
  atlas-pauli-branch-recurrence-automaton: that asks for recurrent partial-isometry ranges with leakage and Gram control; this is an exact finite character-orbit calculation and supplies no recurrence outside its orbit.
  pauli-two-child-transfer-packet: that produces two equal-trace children from one common source; this determines when two root shears merely pair the pre-existing p/q character cuts.
---

**ESTABLISHED EXACT TWO-SHEAR CLASSIFICATION.**  Put, for
`a in {1,e,f,E,F}`,

```text
C_a=pi(x_12(a)),
D_a=pi(x_13(a)),       S=pi(x_23(1)),
E_a=pi(x_14(a)),       T=pi(x_24(1)).                 (TTS1)
```

The two independent literal Steinberg families give

```text
S C_a S=C_a D_a,       T C_a T=C_a E_a.              (TTS2)
```

The actors `S,T` commute.  The `D` and `E` root families commute with each
other and with both actors.  Therefore, on a joint character atom labelled
by sign vectors `(chi,eta,theta)`, the generated `C_2^2` action is

```text
S : (chi,eta,theta) |-> (chi*eta,eta,theta),
T : (chi,eta,theta) |-> (chi*theta,eta,theta).         (TTS3)
```

Its orbit has size `2^rank{eta,theta}`.  In particular the common face
`eta=theta=+` is fixed pointwise and retains arbitrary `chi` multiplicity.

There is a complete criterion on the CK partition.  Let `p=eE`, `q=fF` and,
on one joint `(D,E)` character sector, write bits

```text
u=(u_S,u_T),       u_R=1 iff the R-family p-sign is -1,
w=(w_S,w_T),       w_R=1 iff the R-family 1-sign is -1.
                                                               (TTS4)
```

Thus `w_R` records whether the shear `R` flips the marked central sign
`Z=x_12(1)`, while `u_R` records whether it flips the `p` branch.  Inside
one `C_2^2` orbit, a word `S^i T^j` preserves the `Z=-1` carrier exactly
when

```text
w_S i + w_T j = 0 mod 2,                              (TTS5)
```

and it exchanges the complementary `p` and `q` cuts there exactly when also

```text
u_S i + u_T j = 1 mod 2.                              (TTS6)
```

Consequently the marked `p/q` multiplicities are forced equal on that joint
character sector if and only if

```text
det [ u_S  u_T ]
    [ w_S  w_T ] = 1 in F_2.                          (TTS7)
```

When the determinant is zero, `u` lies in `span{w}`.  Then every group word
which preserves the marked sign also preserves the `p/q` orientation, so no
rank balance follows.  The common trivial-character face has `u=w=0` and is
the simplest surviving component, but it is not the only one: `u=w!=0` and
`u=0!=w` also lie on the determinant-zero escape locus.

This survivor is not a zero-mass artifact of the fixed label chart.  The
coefficient-one central subgroup

```text
<x_13(1),x_14(1)> ~= C_2^2
```

acts regularly inside the fixed left-regular `A8` label representation, so
its common `(+,+)` character cut has normalized trace `1/4`.  Additional
coefficient signs may refine that cut, but these two shears alone cannot
remove it.

There are exact finite-dimensional models with arbitrary imbalance on every
determinant-zero orbit: represent the finite affine orbit by its permutation
representation and amplify its marked points by arbitrary equal
multiplicities along that orbit.  In particular, on the common fixed face
one may tensor arbitrary `p/q` multiplicities with any commuting nontrivial
representations of `S,T`.

Thus the minimal two-transverse packet gives balance on a precisely described
open set of character types, but does not eliminate the CK multiplicity
escape.  The next relation must charge the determinant-zero types, or a third
direction must be shown to make their common degeneracy face negligible.

DERIVATION
atlas-two-transverse-shears-determinant-proof
