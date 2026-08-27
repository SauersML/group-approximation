---
rg: 2
id: finite-group-selector-induction-barrier-proof
kind: route
title: Induce every selector character from the abelian subgroup
target: finite-group-selector-induction-barrier
requires: []
---

Because `J` is central and the `z_i` are commuting involutions,

```text
A=<J,z_1,...,z_m>
```

is an elementary abelian `2`-group.  Fix any character

```text
chi:A->{+1,-1},   chi(J)=-1.
```

Form the finite-dimensional induced representation

```text
Pi = Ind_A^F chi.
```

It is nonzero because `F` is finite.  In the standard induced model, the
function supported on the identity coset and taking value `1` at the identity
is a nonzero `A`-eigenvector of character `chi` (up to the harmless inverse
convention, which is identical here because every character has order at most
two).  Hence the joint signs

```text
(chi(z_1),...,chi(z_m))
```

occur in `Pi`.

Since `J` is central in `F`, its action on every induced coset is the same
scalar `chi(J)=-1`.  Thus

```text
Pi(J)=-I.
```

This proves that every character in the `chi(J)=-1` slice contributes its
selector pattern to `Sigma`.

Conversely, if `pi(J)=-I` and `0!=xi` is a common eigenvector for the commuting
involutions `pi(z_i)`, then the `A`-cyclic line through `xi` is a one-dimensional
`A`-representation: its character sends `J` to `-1` and the `z_i` to the
observed signs.  Therefore no other patterns occur.

The character group `Hom(A,{+1,-1})` is an `F_2`-vector space.  Imposing
`chi(J)=-1` is an affine hyperplane (or, if `J=1`, the slice is empty; the
selector application always has a genuine phase involution).  Restriction to
the coordinates `z_i` is affine-linear, so its image `Sigma` is affine.

For `m>=3`, the one-hot set is not affine by
`one-hot-selector-parity-barrier`.  Hence `Sigma` cannot equal the one-hot
set.  If all one-hot patterns occur, their affine hull is contained in
`Sigma`, so `Sigma` necessarily contains a spurious non-one-hot pattern.  This
proves the claim.
