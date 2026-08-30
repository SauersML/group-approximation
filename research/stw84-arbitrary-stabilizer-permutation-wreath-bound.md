---
rg: 2
id: stw84-arbitrary-stabilizer-permutation-wreath-bound
kind: claim
title: Arbitrary permutation stabilizers preserve finite nuclear dimension for finite-rank abelian wreath actors
distinct_from:
  stw84-finite-stabilizer-menu-wreath-bound: that theorem performs the simultaneous lattice purification when the full action has finitely many stabilizer types; the present theorem shows that every finite approximation automatically has a finite menu, so no global restriction on the stabilizers is needed.
  stw84-almost-free-permutation-wreath-bound: that theorem allows infinitely many stabilizer types only when all stabilizers are finite; here stabilizers may be arbitrary infinite subgroups with unbounded indices and no common commensurability core.
artifacts:
  - research/artifacts/stw84-arbitrary-stabilizer-wreath-2026-08-30.md
---

Let `L` be a countable locally finite group, let `A` be a countable abelian
group of finite rational rank

```text
r=dim_Q(Q tensor_Z A),
```

and let `A` act arbitrarily on a countable set `S`.  No hypothesis is imposed
on the point stabilizers.  For

```text
G=(direct_sum_S L) rtimes A
```

one has, when `r>=1`,

```text
r <= dim_nuc(C*(G)) <= 2(r+1)9^r-1.                    (ASW1)
```

If `r=0`, then `G` is locally finite and

```text
dim_nuc(C*(G))=0.                                       (ASW2)
```

Thus an infinite menu of infinite, pairwise noncommensurable stabilizers
causes no additional dimension.  Finiteness is needed only at each finite
approximation stage, where it is automatic: the invariant hull of finitely
many sites under a finitely generated abelian subgroup is a finite union of
orbits and consequently has finitely many stabilizer types.

For example, put `A=Z^2` and

```text
H_n=Z(1,n),
S=disjoint_union_(n in Z) A/H_n.
```

The stabilizers form an infinite family of infinite rank-one subgroups;
distinct types have zero intersection and are not commensurable.  With any
nontrivial finite lamp `L`, neither the finite-stabilizer, finite-menu, nor
common-core theorem applies to the full action, whereas `(ASW1)` gives

```text
2 <= dim_nuc(C*(G)) <= 485.
```
