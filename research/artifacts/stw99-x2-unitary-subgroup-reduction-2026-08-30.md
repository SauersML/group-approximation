# X(2): unitary-subgroup reduction and the hyperfinite-character boundary

## Scope and status

This audit records an unconditional reduction of STW Problem X(2), together
with one obstruction and two open witness searches.  It does **not** assert
that the hyperfinite II1 factor `R` is non-quasidiagonal.

The established implication is

```text
R quasidiagonal
  => every countable subgroup of U(R) is MF.
```

Consequently, a countable non-MF subgroup of `U(R)` would refute X(2).  No
such subgroup is constructed here.  The nodes
`non-mf-subgroup-of-hyperfinite-factor-unitary-group`,
`literal-group-embeds-in-hyperfinite-unitary-group`, and
`hyperfinite-factor-not-quasidiagonal` remain open claims.

## The unconditional reduction

Let `Gamma <= U(R)` be countable and put `A=C*(Gamma) subset R`.  If `R` is
quasidiagonal, then its C-star subalgebra `A` is quasidiagonal.  Hence `A` is
MF and embeds in a norm matrix ultraproduct.  Restriction to the distinguished
unitaries gives operator-norm almost-representations of `Gamma` which separate
every nonidentity element.  Thus `Gamma` is MF.

Taking the contrapositive gives the live route
`hyperfinite-factor-not-qd-via-non-mf-unitary-subgroup`: one non-MF subgroup
of `U(R)` would imply that `R` is not quasidiagonal.  This reduction is
strictly about an honest embedding into `R`; an embedding into `R^omega`,
such as the one supplied by soficity, is insufficient.

## Which groups embed in `U(R)`

A countable group embeds in `U(R)` precisely when it has a faithful character
whose GNS von Neumann algebra is hyperfinite.  Here faithfulness on the group
means `tau(g) != 1` for every `g != 1`.  This criterion makes the remaining
witness problem concrete:

```text
find a non-MF group with a faithful hyperfinite character.
```

Amenable and residually finite groups provide many embeddings but are MF, so
cannot be witnesses.  Known non-MF groups therefore require a character very
different from their regular character.

## Property-(T) obstruction

There is an unconditional obstruction to the most immediate candidates.  If
a finitely generated property-(T) group embeds in `U(R)`, its induced faithful
character has hyperfinite GNS closure and is amenable.  Kirchberg's
property-(T) rigidity for amenable traces approximates that character by
finite-dimensional characters.  Since the character separates group
elements, finite-dimensional representations separate them as well.  Their
finitely generated linear images are residually finite by Mal'cev, and the
original group is residually finite.

Therefore every finitely generated Kazhdan subgroup of `U(R)` is residually
finite and hence MF.  The known simple and torsion-free Kazhdan non-MF groups
cannot embed in `U(R)`.  This invalidates the route
`non-mf-unitary-subgroup-via-kazhdan-non-mf-groups` but says nothing decisive
about non-Kazhdan groups.

## Literal-group candidate

The remaining recorded candidate is the literal non-MF group `E`.  Its
soficity embeds it in `U(R^omega)`, not in `U(R)`.  An embedding into `U(R)`
would amount to a faithful hyperfinite character.  Splitting at its central
involution mark `w` reduces one proposed construction to:

1. a faithful hyperfinite character of `E/<w>`; and
2. a hyperfinite projective representation on which `w` acts as `-1`.

Both pieces are open.  Finite-dimensional representations kill the mark, so
the second piece would have to be genuinely infinite dimensional.  The
coherence needed to replace an ultrapower representation by an honest
representation in `R` is exactly the unresolved step.

## Integrity boundary

The graph deliberately separates established and open nodes:

- `hyperfinite-factor-qd-forces-unitary-subgroups-mf` and
  `kazhdan-groups-in-hyperfinite-unitary-group-are-rf` are established;
- `non-mf-subgroup-of-hyperfinite-factor-unitary-group` and
  `literal-group-embeds-in-hyperfinite-unitary-group` are open;
- `hyperfinite-factor-not-quasidiagonal` is an open target reached only if a
  non-MF subgroup witness is supplied.

No route in this lane currently closes X(2).
