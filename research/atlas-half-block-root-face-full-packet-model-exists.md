---
rg: 2
id: atlas-half-block-root-face-full-packet-model-exists
kind: claim
title: Growing full-coefficient Atlas models exist on the first-root half-block commutant face
distinct_from:
  atlas-order-one-weyl-common-root-exists: that restricts the two coefficient variables to one Heisenberg/Weyl relation and is refuted by the first relator; this permits arbitrary noncommutative two-unitary moments but imposes the exact positive face actually cut out by that relator.
  atlas-first-root-relator-is-half-block-commutant-face: that identifies the necessary half-block equation from one relator; this asks to solve every remaining packet equation while staying on that face and retaining full coefficient algebras.
---

**OPEN.**  Do there exist dimensions `r_n -> infinity` and pairs
`Z_(1,n),Z_(2,n) in U(r_n)` such that

```text
C*(Z_(1,n),Z_(2,n)) = M_(r_n)(C),                    (HRM1)
Omega(Z_(1,n),Z_(2,n)) -> 0,                         (HRM2)
max_(s in T_St \ {root_12_1e})
  ||pi_(U_(Z_1,Z_2))(s)-I||_2 -> 0?                  (HRM3)
```

By `atlas-first-root-relator-is-half-block-commutant-face`, `(HRM2)` is
exactly the first packet equation.  Thus this is the unrestricted
non-Heisenberg survivor of the refuted common-Weyl-root ansatz, expressed on
the smallest positive face currently forced by a literal rank-five word.

The condition does not assume that `Z_1,Z_2` commute.  Indeed `(HRM1)` rules
out a commutative coefficient algebra.  By
`atlas-root-triangle-is-heisenberg-character-fibers`, `(HRM3)` further
localizes the search to the `D8` multiplicity summands and central-character
atoms `(HTF6)`--`(HTF8)`: the neighboring root variables preserve those
atoms and satisfy the scalar Pauli signs `(HTF7)`.  The remaining search is
whether the other roots can couple these noncommutative character fibers
while satisfying the other packet entries.

The next unused Cuntz--Krieger dual-pair triangles are now resolved by
`atlas-ck-dual-pair-cell-leaves-one-partition-multiplicity`.  Every negative
`D8` atom is a two-qubit Pauli block, and the CK partition `eE+fF=1` refines
its multiplicity space into complementary `eE` and `fF` branches.  Crucially,
that entire local subsystem admits every branch-size ratio exactly.  Thus the
remaining full-packet question is narrower than arbitrary fiber coupling:
some relation outside the local `(1,5,2)` CK cell must transport, compare, or
eliminate those two multiplicity branches.  Repeating local Heisenberg or
extraspecial rows cannot close `(HRM1)--(HRM3)`.

The first such transverse direction is computed by
`atlas-first-transverse-root-shear-leaves-fixed-character-face`.  The five
rows `[x_12(a),x_23(1)]=x_13(a)` shear joint character labels by
`(chi,eta) |-> (chi*eta,eta)`.  They balance the `eE/fF` branches on one
nontrivial `eta` sector, but leave the trivial-`eta` face completely free and
send the remaining sector through an order-two marked/unmarked cycle.  Thus
one transverse root direction still does not close the model: a positive
construction may live on its fixed face, while a negative argument must
intersect at least two transverse shears or force mass out of that face.

The minimal two-direction intersection is now exact by
`atlas-two-transverse-shears-have-determinant-balance-test`.  On every joint
character type it reduces branch balance to one `2 by 2` determinant over
`F_2`.  Nonzero determinant gives an actual marked-preserving branch swap;
determinant zero leaves the branch orientation free.  The common fixed face
has label trace `1/4` in the regular chart, so it cannot be discarded as a
vanishing label block.  The remaining positive construction may concentrate
its coefficient multiplicity on this degeneracy face; a negative argument
must charge it using a third direction or a genuinely non-character row.

The third and final rank-five transverse direction is now exhausted by
`atlas-three-transverse-shears-leave-fifteen-character-types`.  The balance
criterion becomes `u notin span(w)` in `F_2^3`: 49 of 64 target-character
types balance, but 15 remain degenerate.  Their canonical mass is `15/64`,
and their marked part has ambient mass `15/128`.  Exact affine-orbit models
retain either marked orientation on each degenerate type.  There is no fourth
transverse root available from `12` in rank five, so the next row must be
genuinely non-shear: it must compare the two degenerate orientation orbits,
not merely add another adjacent coefficient-one target.

The shortest apparent non-shear continuation is also exhausted by
`atlas-target-gl3-preserves-the-fifteen-type-degeneracy`.  The roots
`x_rs(1)`, `r,s in {3,4,5}`, generate simultaneous `GL_3(F_2)` basis changes
on the three target sign vectors.  They preserve `u in span(w)` and split
the fifteen types into strata of sizes `1,7,7`; each stratum still has two
disjoint marked orientations.  Hence no coefficient-one target-basis word
can close the face.  The next genuinely new family must carry a nontrivial
coefficient on a moving target root or use a different incidence pattern.

The first such nontrivial rows are now computed by
`atlas-ef-target-rows-shrink-but-do-not-remove-degenerate-face`.  Coefficient
`e` translates `(u,w)` by `(e_r,e_r)` and coefficient `f` by `(0,e_r)`, so
active rows really do mix the `1,7,7` strata and can expose balanced types.
But the common positive character of the six target `e/f` roots is fixed;
its intersection with the old degeneracy face has exact canonical target
mass `15/4096` and marked ambient mass `15/8192`.  Thus the positive model
still has a dimension-independent place to hide.  The next new rows must use
`E,F` or return their longer coefficient images to this finite CK window.

ROUTES
atlas-half-block-root-face-model-proves-leavitt-hyperlinear
