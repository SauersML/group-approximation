# Unitized support floor for a Leavitt corner witness

Let `e=[g]+[g^2]` and `z=1-e=[1]+[g]+[g^2]` in
`S=F_2[L_(F_2)(1,2)^x]`.  Since `ez=ze=0`, any corner pair

```text
a,b in eSe,       ab=e,       pi(ba)!=1
```

unitizes to

```text
alpha=a+z,        beta=b+z,       alpha beta=1!=beta alpha.
```

This elementary move allows the universal group-algebra rank-pair results to
be applied to the corner without needing a presentation of `eSe`.

Both supports have odd cardinality because their augmentations multiply to
one over `F_2`.  Rank one is impossible: if, say, `alpha` is one group basis
unit, then its evaluation is a unit of the Leavitt algebra.  Evaluation kills
`z`, so `pi(a)` is a unit; the equality `pi(a)pi(b)=1` then forces the reverse
product to be one, contradicting visibility of the defect.  Thus both ranks
are odd and at least three.

Dykema--Heister--Juschenko prove direct finiteness over `F_2` for all rank
pairs `(3,n)` with `n<=11`, symmetrically, and for `(5,5)`.  Therefore the
first surviving ordered profiles are

```text
(3,13),       (5,7).
```

This does not prove a witness exists at either profile.  It is a universal
floor for the corner lane and replaces the earlier statement that the
support-thirteen information was not known to transfer into the corner.  The
stronger subgroup-location obstruction still kills the particular compressed
rank-three lift at every support.
