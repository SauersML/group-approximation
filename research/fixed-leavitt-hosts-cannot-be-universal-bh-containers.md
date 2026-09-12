---
rg: 2
id: fixed-leavitt-hosts-cannot-be-universal-bh-containers
kind: claim
title: No decidable fixed Leavitt host such as L_F2(1,2) contains every finitely generated group with solvable word problem
invalidates: [boone-higman-via-universal-leavitt-host]
distinct_from:
  weyl-algebra-blocks-a-universal-leavitt-host: that is an algebra non-embedding theorem valid only over fields of characteristic zero; this is a group-level non-universality statement for the repository's characteristic-2 host, from word-problem complexity, and it needs no statement about the Weyl algebra.
  complexity-bounded-host-classes-are-not-universal: that is the general principle for any class of hosts sharing one recursive word-problem bound; this is its instance for the fixed Leavitt host, including subgroups of its elementary groups and the units of its unital subalgebras, and it is what invalidates the universal-Leavitt-host route over F_2.
  uniform-wp-bound-excludes-bh-universal-targets: that excludes a finitely presented residually finite input from any uniformly bounded class; this records the consequence for one fixed ring host and the route built on it.
---

**ESTABLISHED.** Let `R = L_(F_2)(1,2)` and `U = R^x`. There is a two-generated
group with solvable word problem that embeds in none of the following:
- `U`;
- any elementary group `E_n(R)`;
- the unit group of any unital subalgebra of `R`.

So no Boone--Higman route can embed every admissible input into the one fixed
host `R`, whether through a group ring, through a `K`-algebra built from it,
or through its units or elementary groups. This holds with no appeal to the
first Weyl algebra, and in particular in characteristic 2, where
`weyl-algebra-blocks-a-universal-leavitt-host` does not apply.

The argument uses only decidability of the word problem of `U` together with
the general complexity principle. So the same conclusion holds for every fixed
finitely generated host with decidable word problem. The constructions that
remain live are families of hosts whose word problems are allowed to grow
with the input, as in `leavitt-tensor-elementary-host-criterion`.

Derivation: `fixed-leavitt-hosts-not-universal-proof`.

## Attempts

- The characteristic-zero Weyl obstruction was the earlier invalidator of the
  universal-host route. It does not reach `F_2`, because `xy - yx = 1` holds
  in `M_2(F_2) ⊆ R`. This claim replaces it there.
