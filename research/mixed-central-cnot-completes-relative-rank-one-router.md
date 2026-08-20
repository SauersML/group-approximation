---
rg: 2
id: mixed-central-cnot-completes-relative-rank-one-router
kind: claim
title: A four-generator mixed-central CNOT has an initialized marked flag and exactly one predicate rank jump
artifacts:
  - experiments/mixed_commutator_cnot_completion.py
distinct_from:
  predicate-activated-cnot-routes-relative-pauli-halves: that duplicates the predicate commutator and gives CNOT only when the flag has already been initialized; this uses the fixed marked sign J for the flag and completes the unequal commutator geometry.
  relative-pauli-child-split-gives-one-exit-copy: that obtains equal halves after packet exactification but has no finite routing automorphism; this builds the finite packet and routing automorphism simultaneously.
---

Let `K,J` be central involutions and let `G(K,J)` be the class-two group on
four noncentral involutions `a,b,c,d` whose nontrivial commutators are

```text
[a,b]=K,       [a,d]=KJ,
[b,c]=K,       [c,d]=J.                                (MCR1)
```

The omitted commutators `[a,c]` and `[b,d]` are trivial.  The word assignment

```text
a -> c,        b -> b,
c -> a,        d -> bd                                  (MCR2)
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

Use `b` as the control sign and `d` as the flag.  Equation `(MCR2)` fixes `b`
and sends `d` to `bd`.  On the violating sector `K=J=-1`, `(MCR1)` gives

```text
[a,b]=-1,       [a,d]=KJ=+1.                            (MCR4)
```

Thus, inside either fixed `d`-flag carrier, `a` preserves that carrier and
swaps the two `b` halves.  They have equal trace, and `phi(d)=bd` routes them
to the two opposite target flag signs.  Meanwhile `[c,d]=J` makes the two
source flag signs themselves equal-mass on the entire marked sector.  The
router therefore needs no pure ancillary state and loses no vanishing-density
corner.

Explicitly, put

```text
Q=(I-J)/2,   F=(I-K)/2,
D_sigma=(I+sigma d)/2,   B_epsilon=(I+epsilon b)/2.
```

On every exact finite-dimensional representation,

```text
tau(Q F D_sigma B_+)=tau(Q F D_sigma B_-)=tau(QF)/4, (MCR5)
```

and the stable letter sends the `(sigma,epsilon)` source block to the
`(epsilon sigma,epsilon)` target block.  Summing over `sigma`, the violating
carrier splits into active and exit mass exactly `tau(QF)/2` each; active
preserves its flag and exit flips it.  Allowed `K=+1` mass is not charged.

Because `G(K,J)` is one fixed finite group, flexible finite-group
exactification makes `(MCR5)` dimension-free in approximate HS models.  The
four HNN covariance relators then control block leakage by the same sign-
transport estimate as `(HST1)`.

The four-generator size is minimal for this normal form because distinct
control and flag Pauli pairs already require `a,b,c,d`.  Exhaustion confirms
that the uncoupled block-diagonal commutator form admits no automorphism with
`b -> b,d -> bd`; the two cross commutators in `(MCR1)` are essential.

The construction does not delete the allowed `K=+1` sectors.  It converts the
remaining global problem to identifying the active target flag charts with
the next clock-level source charts while sending the complementary violating
charts to first-hit E5 layers.
