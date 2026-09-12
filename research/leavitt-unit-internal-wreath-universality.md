---
rg: 2
id: leavitt-unit-internal-wreath-universality
kind: claim
title: One simple Kazhdan MF black hole internally realizes every finite MF reflection
root: true
artifacts:
  - research/leavitt-unit-internal-wreath-proof.md
---

Let

```text
U=L_(F_2)(1,2)^x.
```

The group `U` is nontrivial, finitely generated, simple, Kazhdan, and has
full MF radical.  It has the following internal universality.

For every finite group `F`, the group `U` contains a subgroup

```text
W_F=U wr F=U^F semidirectProduct F,
```

where `F` acts on itself regularly, and

```text
Rad_MF(W_F)=U^F,             W_F/Rad_MF(W_F) ~= F.       (IW1)
```

If `d!=1` is placed in one base coordinate, then

```text
Rad_MF(W_F)=normalClosure_(W_F)(d),                       (IW1a)
cl_MF^(W_F)(N)=N normalClosure_(W_F)(d)                  (IW1b)
```

for every normal subgroup `N` of `W_F`.  In particular,

```text
W_F/N is MF  iff  d belongs to N.                        (IW1c)
```

Thus one involution classifies MF across the entire quotient lattice of
each internal wreath subgroup.

More precisely, the quotient map `W_F->F` induces a natural bijection on
homomorphisms into every MF group.  The same is true for homomorphisms into
finite groups, residually finite groups, compact Hausdorff groups, and
finite-dimensional linear groups over every field.  Thus `F` is
simultaneously the complete MF-visible, profinite, Bohr, and all-fields
finite-dimensional-linear quotient of `W_F`.

If `F` and `F'` are nonisomorphic finite groups, then `W_F` and `W_(F')`
are nonisomorphic, because their universal MF quotients are respectively
`F` and `F'`.  Hence `U` contains infinitely many pairwise nonisomorphic
finitely generated Kazhdan non-MF subgroups, canonically distinguished by
their MF reflections.

The subgroup `W_F` is finitely generated and has property `(T)`.  If `F` is
nontrivial, then `W_F` is non-MF but does not have full MF radical.

Consequently every finite group occurs as the universal MF quotient of a
finitely generated Kazhdan subgroup of the one fixed simple Kazhdan group
`U`.  For nontrivial `F`, the inclusion `W_F<=U` gives the strict failure

```text
Rad_MF(W_F)  <  W_F intersect Rad_MF(U)=W_F.             (IW2)
```

Thus the MF radical is not hereditary to subgroups even when the ambient
group is simple and both groups are finitely generated Kazhdan groups.

There is also one internal countable limit:

```text
W_infinity=U^(N) semidirectProduct Sym_fin(N) <= U,
Rad_MF(W_infinity)=U^(N).                                (IW3)
```

Its universal MF quotient is the finitary symmetric group.  The base is the
normal closure of one nonidentity involution `d` in one coordinate, and for
every normal `N` one again has

```text
cl_MF^(W_infinity)(N)=N normalClosure_(W_infinity)(d).
```

Thus `W_infinity/N` is MF exactly when `d belongs to N`.
