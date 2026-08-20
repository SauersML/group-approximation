---
rg: 2
id: mixed-central-cnot-completes-relative-rank-one-router
kind: claim
title: A six-generator mixed-central CNOT has an initialized marked flag and exactly one predicate rank jump
artifacts:
  - experiments/mixed_commutator_cnot_completion.py
distinct_from:
  predicate-activated-cnot-routes-relative-pauli-halves: that duplicates the predicate commutator and gives CNOT only when the flag has already been initialized; this uses the fixed marked sign J for the flag and completes the unequal commutator geometry.
  relative-pauli-child-split-gives-one-exit-copy: that obtains equal halves after packet exactification but has no finite routing automorphism; this builds the finite packet and routing automorphism simultaneously.
---

Let `K,J` be central involutions and let `G(K,J)` be the class-two group on
six noncentral involutions `g_0,...,g_5` whose nontrivial commutators are

```text
[g_0,g_1]=K,       [g_0,g_3]=KJ,      [g_0,g_5]=K,
[g_1,g_2]=K,       [g_2,g_3]=J,       [g_2,g_5]=K,
[g_3,g_5]=K.                                           (MCR1)
```

All omitted commutators are trivial.  The word assignment with exponent
columns

```text
g_0 -> g_2 g_4,             g_1 -> g_1,
g_2 -> g_0,                 g_3 -> g_1 g_3,
g_4 -> g_0 g_1 g_2 g_5,    g_5 -> g_0 g_1 g_2          (MCR2)
```

is an automorphism `phi` of `G(K,J)`.  Hence one HNN stable letter implements
`phi` by ordinary conjugacy relations while embedding the finite base packet.

For the four central characters `(k,j)` in additive sign notation, the
alternating commutator ranks are

```text
(0,0):0,       (0,1):2,       (1,0):4,       (1,1):4. (MCR3)
```

Consequently, on the marked sector `J=-1`, `K=+1` has spin dimension 2 and
`K=-1` has spin dimension 4: changing `K` creates exactly one relative Pauli
qubit.

Put `a=g_0`, `b=g_1` and use `d=g_3` as the flag.  Equation `(MCR2)` fixes
`b` and sends `d` to `bd`.  On the violating sector `K=J=-1`, `(MCR1)` gives

```text
[a,b]=-1,       [a,d]=KJ=+1.                            (MCR4)
```

Thus, inside either fixed `d`-flag carrier, `a` preserves that carrier and
swaps the two `b` halves.  They have equal trace, and `phi(d)=bd` routes them
to the two opposite target flag signs.  Meanwhile `[g_2,d]=J` makes the two
source flag signs themselves equal-mass on the entire marked sector.  The
router therefore needs no pure ancillary state and loses no vanishing-density
corner.

The construction does not delete the allowed `K=+1` sectors.  It converts the
remaining global problem to identifying the active target flag charts with
the next clock-level source charts while sending the complementary violating
charts to first-hit E5 layers.
