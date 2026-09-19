---
rg: 2
id: constant-repetition-v4-needs-only-disjoint-tags
kind: claim
title: Constant repetition removes the parent-exclusivity requirement from the V4 tag ledger
distinct_from:
  disjoint-tag-covariance-controls-cross-gram: that bounds Gram overlap for supplied disjoint tag types; this combines that bound with constant duplication and the robust BCS gap so the whole ambient space supplies capacity.
  globally-conditioned-v4-exit-capacity: that requires tag types to be absent outside the forbidden parent and controls off-parent leakage; this needs only pairwise disjoint target types and bypasses the parent projection.
  classical-pcp-gap-is-not-tracial-pvm-gap: that warns classical repetition does not amplify contextual quantum soundness; this repeats an already established robust non-CE BCS energy inequality a fixed number of times and uses only linear trace accounting.
---

Let the robust gap of the fixed non-CE BCS be written

```text
E_base+q >= beta,                                      (CRV1)
```

where `q` is the total forbidden carrier mass after fixed-packet
exactification and fixed transfer loss has been absorbed into `E_base`.
Duplicate every context packet `L` times while retaining the same original
shared selector words. In each duplicate, split the synchronized V4 failure
projections into their five radical-atom occurrences. Their total source
mass is

```text
s=(5/4)Lq.                                             (CRV2)
```

Suppose a joint decoder places the resulting fixed finite family of partial
isometries `T_i` in one ambient matrix amplification of normalized capacity
`M_0`, and supplies pairwise disjoint finite tag types with total covariance
energy at most `C_tag E_rel`. Then
`disjoint-tag-covariance-controls-cross-gram`, followed by
`gram-branching-capacity-with-overlap` with parent projection `I`, gives

```text
M_0 >= (5/4)Lq-C_1 E_rel.                              (CRV3)
```

Here `M_0=1` when no bookkeeping amplification is used; any fixed
amplification merely changes the fixed repetition count.

Choose once and for all

```text
L>4M_0/(5 beta).                                       (CRV4)
```

Combining `(CRV1)` and `(CRV3)` yields a dimension-independent lower bound
on `E_base+E_rel`. Explicitly, if `E=E_base+E_rel`, then

```text
M_0 >= (5/4)L(beta-E)-C_1E,
E >= ((5/4)L beta-M_0)/((5/4)L+C_1)>0.                 (CRV5)
```

Thus the global V4 programme does not logically need tag exclusivity from
the complement of the forbidden parent. Constant repetition converts the
whole ambient identity into the capacity ceiling. The remaining construction
gate is strictly weaker: obtain pairwise disjoint target tag types and their
covariances jointly from the shared contextual tuple.

This is not classical PCP amplification. `L` is a fixed constant chosen
after the dimension-free compactness gap `beta` exists, and `(CRV1)` is not
reproved or strengthened by repetition. The argument only multiplies an
already positive source mass before applying a Hilbert-space capacity bound.
