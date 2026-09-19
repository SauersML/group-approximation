---
rg: 2
id: steinberg-cycles-have-big-cell-chord-coordinates
kind: claim
title: Every SL3 Steinberg cycle has unique three-coordinate big-cell chord data
artifacts:
  - research/steinberg-big-cell-spanning-tree-proof.md
distinct_from:
  steinberg-fox-kernel-is-flag-incidence: that identifies the common kernel inside the full flag chain space; this removes the panel equations and replaces every boundary flag by an explicit tree cut-sum.
---

Let `p` be any prime and use the point--plane building notation of `(SFI1)`.
Fix the plane

```text
H_0={x_1=0}
```

and the point `z=[e_3]`.  The set of flags

```text
T={P subset H : P subset H_0 or z subset H}           (SBC1)
```

is a spanning tree in the incidence graph.  Its complementary flags are
parametrized uniquely by triples `(a,b,c) in F_p^3` as

```text
C(a,b,c)=([1:a:b],[ac-b:-c:1]).                        (SBC2)
```

Consequently restriction to the complementary chords is an isomorphism

```text
R_p:St_p=ker partial -> Fun(F_p^3,F_p).                 (SBC3)
```

The inverse `E_p` is integral and explicit: retain the prescribed chord
coefficients, and on a tree edge use the signed sum of the chord boundary
demands on either component cut off by that edge.  Thus there is no division
and no characteristic-dependent exceptional case in the cycle extension.
The tree has diameter at most five: its only nonleaf edges form the double
star with centers `z` and `H_0`.  Hence every exceptional value is a panel
sum or a sum over one branch of this double star, not an unspecified global
extension problem.

For `g in SL_3(F_p)` put

```text
L_g=R_p g E_p.                                         (SBC4)
```

At the chord `C(a,b,c)`, `L_g f` is either the single value of `f` at the
renormalized chord `g^(-1)C(a,b,c)`, or, when that flag belongs to `T`, the
corresponding signed tree-cut sum.  Hence the Steinberg Fox test is the two
exact three-variable recurrences

```text
(L_A-L_(Aq)+L_B-L_(Bs)-I)f=0,
(I-L_q-L_u+L_(uq)-L_(h^(-1)r)+L_(h^(-1)))f=0.          (SBC5)
```

All exceptional Bruhat/denominator strata in `(SBC5)` are therefore
explicit tree cuts, rather than missing Weyl-cell data.

DERIVATION
steinberg-big-cell-spanning-tree-proof
