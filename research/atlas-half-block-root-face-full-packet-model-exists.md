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

The `E/F` continuation and its returns are now identified by
`atlas-ef-dual-rows-create-the-prefix-depth-tower`.  At depth one, the twelve
new `pE,qE,pF,qF` target signs leave a smaller marked face of mass
`15/2^25`.  Iterating the relations `Ee=Ff=1`, `Ef=Fe=0` produces `2^n`
independent Heisenberg pairs over the marked root, so exact finite-dimensional
models collapse as `2^(2^n)` spin divisibility tends to infinity.  Every
fixed depth nevertheless has a marked finite regular model.  The remaining
positive construction is therefore precisely an ultra-deep coherent prefix
tower, not another bounded character face.

The natural depth-free scalar closures of that tower are now exhausted by
`atlas-ultradeep-prefix-tower-survives-bounded-scalar-closures`.  Coherent
Schrodinger windows survive tensoring with the exact regular-`A8` margin;
fixed tags leave atom mass `2^(-2^n)`, bounded phase menus have bounded
approximate rank, the Renyi-2 address rate is critical, and the canonical
Whitehead/swap completion still exchanges label and reservoir dimensions
rectangularly.  This does not construct a model of all `4,648` words.  It
isolates the first genuinely untested datum: one non-scalar mixed packet row
must authenticate the coarse and fine selectors on the same multiplicity
reservoir.  The already known three-elementary coarse-to-fine partial swap
would then give the depth-free trace floor; finding another divisibility,
tag, phase, entropy, or diagonal-copy argument cannot close the remaining
face.

The literal first-row continuation is now also exhausted. Under the
canonical packet order, after discarding one-root rows, same-orientation
roots, and rows with a displayed constant coefficient, the first survivor is
`orth_12_32_ee=[x_12(e),x_32(e)]`. By
`atlas-first-nonscalar-mixed-row-is-same-source-commutation` this is an
automatic same-source matrix-unit commutation: it holds exactly on every
coherent prefix window for arbitrary unequal target reservoirs. Hence the
next useful datum is not simply the earliest non-scalar mixed row. It must
be a coupled family of mixed rows whose joint block data survive the
rectangular Morita escape and authenticate the coarse/fine covariance.

Even the first shared-occurrence pair is insufficient. The next row is
`orth_12_32_ef`, so entries `281,282` share `x_12(e)` and compare the two
fine labels `e,f`. By
`atlas-first-two-mixed-rows-have-zero-reservoir-rank`, both commutators are
simultaneously automatic for arbitrary fine coefficient maps; their
nuisance-quotient reservoir rank is zero. Thus coupling adjacent rows inside
the initial same-source orthogonality block does not improve the situation.

Nor does moving to genuinely distinct sources. The first canonical pair
with distinct source columns and target rows is
`orth_12_43_ee,orth_12_43_ef` (packet entries `381,382`). By
`atlas-first-disjoint-mixed-pair-has-zero-reservoir-rank`, the disjoint
matrix blocks again multiply to zero in both orders, leaving the two fine
maps arbitrary and contributing zero nuisance-quotient rank. The first
viable coupled family must therefore include a composable multiplication or
return row rather than only orthogonality rows.

The first composable family is now exhausted as well. Packet entries
`3261,3262` are the two St3 rows with common first leg `x_13(e)`, second legs
`x_32(e),x_32(f)`, and RHS paths `x_12(ee),x_12(ef)`. By
`atlas-first-composable-mixed-pair-has-zero-quotient-rank`, retaining those
two RHS paths as nuisance columns gives coefficient matrix `[I_2,-I_2]` and
quotient-rank increment zero. The next useful family must contain a return
which identifies a product RHS with an already authenticated occurrence;
another multiplication row with a fresh product nuisance cannot suffice.

The first literal return does create some rank, but not enough. The three
factorizations of the common RHS `x_12(ee)` through intermediate indices
`3,4,5` form the earliest complete return star. By
`atlas-first-common-rhs-return-star-has-rank-two`, its coefficient matrix is
`[I_3,-1_3]`: the two path differences survive nuisance elimination, while
the common product mode does not. Arbitrary unequal intermediate reservoirs
factor the same common map exactly. The next family must therefore return
that common RHS to an independently authenticated chart occurrence, not just
factor it through another rank-five index.

The obvious chart seam does not supply that occurrence. By
`atlas-reverse-dictionary-does-not-close-ee-return`, the complete reverse
dictionary uses only the one-letter coefficient roots `1,e,f,E,F`; none of
its twelve rows contains the two-letter RHS `x_12(ee)`. Appending those rows
therefore leaves the star's literal nuisance-quotient rank at two and retains
the common seam mode. This is a scoped incidence fence, not a proof that no
longer normal-closure consequence exists. The next useful family must
actually meet the two-letter occurrence, or prove a quantitative transfer
from the one-letter chart seam rather than infer it from presentation
surjectivity.

ROUTES
atlas-half-block-root-face-model-proves-leavitt-hyperlinear
