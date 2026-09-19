---
rg: 2
id: stw84-finite-stabilizer-menu-wreath-bound
kind: claim
title: A finite menu of arbitrary stabilizers gives finite nuclear dimension for permutation wreath products
distinct_from:
  stw84-almost-free-permutation-wreath-bound: that theorem permits infinitely many stabilizer types but requires every stabilizer to be finite; the present theorem permits infinite positive-rank stabilizers drawn from a finite menu.
  stw84-commensurable-stabilizer-wreath-bound: that theorem requires one subgroup contained with finite index in every point stabilizer; here the finitely many stabilizers can be pairwise noncommensurable and can have trivial intersection.
  stw84-common-stabilizer-wreath-bound: that theorem extracts a common split subgroup fixing every site; no common positive-rank subgroup and no splitting are required here.
artifacts:
  - research/artifacts/stw84-finite-stabilizer-menu-wreath-2026-08-30.md
---

Let `L` be a countable locally finite group, let `A` be a countable abelian
group of finite rational rank

```text
r=dim_Q(Q tensor_Z A),
```

and let `A` act on a countable set `S`.  Suppose that the point stabilizers
take only finitely many distinct values: there are subgroups
`H_1,...,H_m<=A` such that

```text
{A_s:s in S} subset {H_1,...,H_m}.                       (FSM1)
```

For

```text
G=(direct_sum_S L) rtimes A
```

one has, when `r>=1`,

```text
r <= dim_nuc(C*(G)) <= 2(r+1)9^r-1 < infinity.           (FSM2)
```

If `r=0`, then `G` is locally finite and

```text
dim_nuc(C*(G))=0.                                        (FSM3)
```

This reaches stabilizer geometry excluded by both earlier mechanisms.  For
example, let

```text
A=Z^2,
H_1=Z times {0},
H_2={0} times Z,
S=A/H_1 disjoint_union A/H_2,
L=Z/2.
```

Both stabilizers are infinite, so the finite-stabilizer theorem does not
apply.  Their intersection is zero and has infinite index in each, so there
is no common finite-index core as required by the commensurable-stabilizer
theorem.  Nevertheless `(FSM2)` gives

```text
2 <= dim_nuc(C*(G)) <= 485.
```

The finite-menu hypothesis replaces common commensurability by a lattice
separation argument.  At each stabilizer fiber, intersect only those
stabilizer types which support non-scalar tensor orbits.  After removing
that central trivial-action subgroup, one finite-index free lattice can be
chosen so that its intersection with every remaining stabilizer is pure.
Every nonzero lattice element then has an infinite orbit through some
non-scalar tensor block, forcing strong outerness.
