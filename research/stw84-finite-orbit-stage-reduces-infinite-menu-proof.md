---
rg: 2
id: stw84-finite-orbit-stage-reduces-infinite-menu-proof
kind: route
title: Exhaust an arbitrary permutation action by finite-orbit-menu stages
target: stw84-arbitrary-stabilizer-permutation-wreath-bound
requires:
  - stw84-finite-stabilizer-menu-wreath-bound
  - stw84-directed-union-uniform-bound
  - stw84-abelianization-rank-lower-bound
artifacts:
  - research/artifacts/stw84-arbitrary-stabilizer-wreath-2026-08-30.md
---

Enumerate `S={s_1,s_2,...}`.  Choose increasing finite subgroups `F_j` whose
union is `L` and increasing finitely generated subgroups `V_j` whose union is
`A`.  Put

```text
R_j={s_1,...,s_j},
T_j=V_j R_j=union_(l<=j) V_j s_l,
G_j=(direct_sum_(T_j) F_j) rtimes V_j.                  (ASW3)
```

The sets `T_j` are `V_j`-invariant and increase with `j`, so the `G_j` form
an increasing sequence of amenable subgroups.  Every element of `G` has one
actor coordinate and finitely many nontrivial lamp coordinates.  Enlarging
`j` to contain all of those data shows that

```text
G=union_j G_j.                                          (ASW4)
```

Fix `j`.  Each point of `T_j` has the form `v s_l` for some `v in V_j` and
`l<=j`.  Since `A` is abelian,

```text
(V_j)_(v s_l)=V_j intersection A_(s_l).                (ASW5)
```

Thus the `V_j`-action on `T_j` has at most `j` stabilizer types.  Applying
`stw84-finite-stabilizer-menu-wreath-bound`, with
`q_j=rank_Q(V_j)<=r`, gives

```text
dim_nuc(C*(G_j))+1
 <= 2(q_j+1)9^(q_j)
 <= 2(r+1)9^r                                           (ASW6)
```

whenever `q_j>=1`; a rank-zero stage is locally finite and has dimension
zero, so it satisfies the same uniform estimate.  The directed-union theorem
applied to `(ASW4)` proves the upper bound in `(ASW1)`.  Killing all lamps
gives a quotient `G -> A`, and the abelianization-rank lower bound gives the
lower bound `r`.

If `r=0`, then every finite subset of `G` is contained in a finite subgroup.
Indeed, put the finitely many actor coordinates inside a finite subgroup
`V<=A`; the `V`-hull of the finite lamp support is finite; and put the
finitely many lamp values inside one finite subgroup of `L`.  The resulting
finite permutation wreath product contains the original finite set.  Hence
`G` is locally finite and `(ASW2)` follows.

The purification integer used inside the finite-menu theorem may diverge
with `j`.  This is harmless: its dimension estimate is independent of that
integer and of the number, indices, and ranks of the active stabilizers.
