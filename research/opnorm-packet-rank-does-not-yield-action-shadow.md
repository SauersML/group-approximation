---
rg: 2
id: opnorm-packet-rank-does-not-yield-action-shadow
kind: claim
title: Operator-norm packet rank rigidity does not produce a Leavitt finite-action shadow
distinct_from:
  leavitt-nonsoficity-does-not-close-macroscopic-mf-branch: that identifies the missing shadow-to-action arrow abstractly; this audits the proposed finite-packet implementation of that arrow and locates its exact failure at the normalizer/opposite-root boundary.
  binary-leavitt-finite-actor-minimal-atom-dichotomy: that gives the exact finite crossed-product countermodel for one invariant root window; this explains why operator-norm exactification and rank rigidity do not escape that countermodel or synchronize several windows.
  opnorm-packet-exactification-is-dimension-free: that rounds an approximate finite matrix-unit packet on a common identity carrier; this records that a common identity is not a common invariant atom algebra and therefore is not a finite action.
artifacts:
  - research/leavitt-nonsoficity-does-not-close-macroscopic-mf-branch.md
---

**ESTABLISHED FENCE.**  Consider the proposed Property-`(T)`-free converter
starting from a surviving norm-matrix-corona model of

```text
Delta=St_20(L_(F_2)(1,2))
```

or its elementary image.  Active-core reblocking makes the marked involution
macroscopic.  Operator-norm exactification then turns every **fixed** finite
elementary-`2`, Heisenberg, or matrix-unit packet into an exact packet in the
same coordinate, and every projection comparison of norm less than one fixes
the corresponding ranks.  These facts do not produce the finite action/atom
shadow required by Leavitt nonsoficity.

The obstruction is a sharp two-case boundary.

1. If the chosen actors preserve a finite abelian root window, their action on
   its character atoms is an honest finite action.  On that window the exact
   crossed-product model `(FAM1)` of
   `binary-leavitt-finite-actor-minimal-atom-dichotomy` satisfies the entire
   finite root table and actor covariance, retains a marked atom, and permits
   arbitrary unitary multiplicity gauges.  Every atom return is
   rank-preserving and Morita-neutral.  Hence exact ranks, support profiles,
   and the finite atom action do not yield the two-to-one Leavitt return.
2. A genuine opposite-root actor, which is necessary to read coefficient
   multiplication rather than only a finite parabolic covariance table, does
   not normalize that abelian root algebra.  For

   ```text
   x=I+qE_(ij),            y=I+E_(ji),
   yxy^(-1)|_(i,j)=[[1+q,q],[q,1+q]],
   ```

   the conjugate has diagonal and opposite-root entries and is not another
   atom label in the selected root window.  Thus this actor has no induced
   permutation of the packet atoms to exactify.

Exactifying a second packet on the same identity projection does not bridge
the cases.  The common-carrier conclusion of
`opnorm-packet-exactification-is-dimension-free` identifies only the sums of
the packet diagonal projections.  It neither identifies their individual
spectral atoms nor supplies a common invariant masa.  Two exact packet
algebras on the same finite-dimensional carrier may have arbitrary relative
unitary position.  The ranks of all their minimal projections can agree while
their intersections, and therefore every proposed common atom refinement,
vanish or depend on the uncontrolled multiplicity gauge.

Likewise, replacing each exact finite-group representation by a regular
permutation representation is not an operation on the original corona
homomorphism.  Such a replacement may be made for one finite subgroup after
adding representation summands, but those summands need not extend to the
ambient Leavitt group and independently chosen replacements need not agree on
overlaps.  Coherently making them agree for every word in a growing finite
test is already the missing finite-action converter, not a consequence of
rank rigidity.

Therefore the implication

```text
active-core + fixed-packet opnorm exactification + rank(<1) rigidity
   => Leavitt finite-action shadow
```

is unavailable and cannot be inserted into
`leavitt-nonsoficity-does-not-close-macroscopic-mf-branch`.  A successful
Property-`(T)`-free argument must add genuinely new information: either a
word-authenticated common atom algebra invariant under the required mixed
actors, or a moving coefficient-sensitive occurrence compiler which never
claims that the opposite-root transport acts on one fixed atom table.

No Property `(T)`, Kazhdan projection, canonical trace profile, or literature
input is used in this fence.

## Attempts

- **Exactify every fixed finite subgroup and take its support profile.**  The
  profile records irreducible multiplicities but no common basis or overlap
  data.  Independent exactifications retain arbitrary relative multiplicity
  gauges.
- **Regularize each finite packet.**  Adding the missing irreducibles can turn
  one finite-group representation into copies of its regular representation,
  but the added representation generally does not extend to the ambient
  group.  Doing this on every overlapping packet is exactly the unproved
  coherence statement.
- **Use the common identity carrier from matrix-unit exactification.**  Equal
  identities do not imply commuting diagonal algebras or a joint atom
  refinement.  Rank rigidity controls dimensions only after the relevant
  projections have already been identified in operator norm.
- **Close under all actors.**  Parabolic closure remains in the finite-actor
  countermodel.  Adding an opposite root leaves the atom-normalizer category
  and returns to the moving-boundary/occurrence problem.

DERIVATION
opnorm-packet-rank-action-shadow-fence-proof
