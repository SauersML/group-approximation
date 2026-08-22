# The complete residue beyond the area-ten short atlas

## Low-word gate

The exact wrapper
`research/artifacts/classify-leavitt-even-through-eight.py` reuses the
free-factor normal form and moved-vector representation from the odd-word
classifier.  It considers only cyclically formally reduced words nontrivial
in

```text
Q=V4(h0,h2)*V4(k0,k1)*F(h1,k2).
```

The MSI output is

```text
length  orbit reps  Q-nontrivial  certified nonidentity  extras  unknowns
2                18            18                     18       0         0
4               334           332                    332       0         0
6            10,014        10,014                 10,014       0         0
8           361,660       361,656                361,656       0         0
```

Together with the established odd classifications at lengths five, seven,
and nine (and the elementary length-one/three screen), every actual corner
identity of length at most nine is already trivial in `Q`.  Hence a picture
outside the short atlas has an internal `Q`-nontrivial identity of length at
least ten.

## Curvature and forced digons

At area ten there are six internal faces, one outer face, and 30 corners.
An internal identity outside `Q` has even length at least ten or odd length
at least eleven.  Every other internal identity has even length at least
two.  Enumerating integer budgets gives exactly 52 designated
`(internal lengths; outer length)` configurations.  Their counts by number
of internal digons are

```text
one: 2, two: 6, three: 14, four: 20, five: 10.
```

Thus every residue has a gate digon.  This is only a topological contraction
device: contracting a non-dipole gate digon does not preserve the two
adjacent coefficient identities, so no algebraic induction is asserted.

The certificate
`research/artifacts/classify-leavitt-area-ten-long-residue.py` contracts all
forced internal digons and compares the remaining face lengths with the
complete cubic core partitions on six, four, and two vertices (and the
terminal circle).  The six-vertex list is certified independently by
120,528 planar oriented ribbons and has 25 face partitions.  Exactly 13 of
the 52 budgets survive:

* twelve even budgets, all with one designated internal length-ten face;
  after forgetting which face is outer, these occupy only
  `(2,2,2,2,2,10,10)`, `(2,2,2,2,4,8,10)`,
  `(2,2,2,2,6,6,10)`, `(2,2,2,4,4,6,10)`, and
  `(2,2,4,4,4,4,10)`;
* one odd budget: internal `(2,4,4,4,4,11)` and outer length one.

## Exact even labels

`research/artifacts/search-leavitt-area-ten-long-even.py` selects the 88
exact ribbon maps in those five even partitions from the 276-map restoration
atlas.  Over 243,152 valid orientations and 15,880,608 dipole-admissible
colorings, only 84 cyclic length-ten words could serve as the required
internal identity.  Exact free-factor reduction and moved-vector witnesses
certify every one nontrivial.  There is no even residue disk.

## The odd core is absent

Contracting the unique internal digon of the odd budget would leave one of

```text
(1,4,4,4,4,7), (1,2,4,4,4,9), (1,2,2,4,4,11).          (OR1)
```

The first contains a monogon and is the inverse loop-lollipop expansion of
a six-vertex cubic ribbon map.  The other two contain a digon and are inverse
digon expansions of such a map.  The exact certificate
`research/artifacts/search-leavitt-area-ten-long-odd.py` starts from all 16
connected cubic multigraph types on six vertices, flips every local rotation
(231 planar ribbon representatives, reproducing all 25 six-vertex face
partitions), and restores the loop and digon gadgets on every edge.  None of
the three partitions in `(OR1)` occurs.  Therefore the odd budget has no
planar ribbon core even before coefficient labels are restored.

The residue beyond the short atlas is empty.  There is no reduced area-ten
kernel disk for the paired three-gate relative presentation.
