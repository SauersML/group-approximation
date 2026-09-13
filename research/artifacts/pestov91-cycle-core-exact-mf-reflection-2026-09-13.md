# The exact MF reflection of every binary-field subshift group

2026-09-13. Written proof, not Lean-verified.

Let `X` be a nonempty subshift on a finite alphabet, let
`R_X=LC(X,F_2) semidirect_T Z`, and put `G_n(X)=EL_n(R_X)`.
No minimality, finite-seam decomposition or aperiodicity is assumed.
The level-`r` word graph has vertices `L_r(X)` and edges `L_(r+1)(X)`.
An edge is cyclic if its endpoints are in the same strongly connected
component. Define

`Y={x in X : every window of length at least two is a cyclic edge`
`                in its corresponding word graph of X}`.          (1)

Write `U=X\Y` and `I_U=LC_c(U,F_2) semidirect_T Z`, embedded in `R_X`
by extension by zero.

## Theorem

The set `Y` is a nonempty subshift satisfying the finite-word cycle
condition (C), is the largest subshift of `X` satisfying (C), and is
the chain-recurrent set of the shift. The ideal `I_U` is locally
matricial: every finite subset lies in a finite product of full matrix
algebras over `F_2`, whose identity can be a proper local unit.

For every `n>=4`, restriction gives

`1 -> K_n(U) -> G_n(X) -> G_n(Y) -> 1`,
`Rad_MF(G_n(X))=K_n(U)`,                              (2)

where `K_n(U)` is locally finite and `G_n(Y)` is LEF. Thus every group
in this entire family is an extension of a LEF group by its locally
finite MF radical. Formula (2) identifies the entire radical, beyond
the earlier criterion that only detects whether it is nontrivial.
For finite directed seams it specializes to deletion of noncycle edges.

For `n>=2` the general linear restriction kernel is also `K_n(U)`.
For `n>=4` this is the full MF radical of `GL_n(R_X)`, whose maximal
MF quotient is its image in `GL_n(R_Y)`. General linear restriction
is not asserted to be surjective.

## 1. Decreasing cyclic finite-type models

Let `Z_r` be the subshift of finite type whose permitted length-`r+1`
words are the cyclic edges of the level-`r` word graph of `X`. Every
point of `Z_r` stays in one strongly connected component. Every finite
path can be closed there, so every word of `Z_r` occurs in a periodic
point of `Z_r`. In particular `Z_r` satisfies (C) and is nonempty.

These compact subshifts are nested: projecting a higher word-graph
cycle gives a closed walk in the lower word graph, whose every edge
is cyclic. Consequently

`Y=intersection_(r>=1) Z_r`.                         (3)

Compactness makes the intersection nonempty. It lies in `X` since all
its finite words belong to the language of `X`. For each fixed length
`h`, the finite decreasing languages `L_h(Z_r)` eventually stabilize
to `L_h(Y)`: a word occurring at coordinate zero in every stage has
a point in the intersection of those nested compact cylinders. For
`h>=2`, the level-`h-1` word graph of `Y` therefore agrees with that
of a sufficiently late `Z_r`. All its edges are cyclic, proving (C).

If a subshift `W subset X` satisfies (C), every word-graph cycle of
`W` is also a cycle in the corresponding graph of `X`. Thus `W subset Y`,
proving maximality.

The identification with chain recurrence uses finite-window approximate
orbits. At a prescribed window scale, an approximate orbit gives a
path through overlapping words in a sufficiently long word graph.
A closed approximate orbit based at `x` gives a closed walk through
the corresponding word of `x`. Conversely a cycle through a sufficiently
long centered word of `x` gives a closed approximate orbit at any
prescribed smaller scale: realize each cycle edge by a point of `X`,
so consecutive realizations agree on the required shifted window, and
choose the initial and final point to be `x`. Testing arbitrarily long
words in (1) is therefore exactly chain recurrence. The argument above
also proves (C) for the restricted dynamics on that set.

The existing finite-field cycle theorem implies that `R_Y` is ring-LEF
and that every `GL_n(R_Y)` and each of its subgroups is LEF.

## 2. Wandering clopen sets cover the complement

Take a noncyclic word-graph edge `a->b`. The vertices reachable from
`b` form a forward-closed set excluding `a`. Its cylinder union `P`
satisfies `T(P) subset P`. The nonempty clopen set

`D=P\T(P)`

is wandering: the nesting of the translates of `P` makes distinct
integer translates of `D` disjoint. If `x` begins with that edge,
then `Tx in D`.

These defect sets and their translates lie in `U`. Indeed restriction
to `Y` gives a compressed clopen subset of a system whose crossed
product is directly finite. The explicit inverse-pair calculation
therefore forces its defect `D intersection Y` to be empty.

Every point outside (1) exhibits a noncyclic edge at a shifted
coordinate, so these wandering clopen sets cover `U`. Every compact
`C subset U` has a finite such cover, say of size `m`, and hence

`every shift orbit meets C in at most m points`.       (4)

Also `U` has no periodic points, since periodic points lie in `Y`.

## 3. Local matrix-algebra lemma

More generally, suppose an invariant open part of a zero-dimensional
compact shift system is covered by wandering clopen sets. Its compactly
supported crossed-product ideal over any finite field is locally
matricial, as follows.

Write a prescribed finite set of elements as finite linear combinations
of characteristic functions of compact clopen partial shift graphs.
Include inverse partial shifts. The union `C` of all source and range
sets is compact clopen and satisfies (4). Let `d` bound the absolute
shift exponents of these finitely many partial maps. The equivalence
relation `H` they generate on `C` has classes of size at most `m`.
Erase loops in a path between related points to shorten it to at most
`m-1` steps. Every arrow of `H` is consequently represented by one of
finitely many words of length at most `m-1` in these maps, with compact
clopen domain and exponent bounded by `d(m-1)`.

Thus `H` is a compact open finite equivalence relation in the
transformation groupoid. Freeness on the open set makes arrows
between related points unique: a closed path has total exponent zero.
This excludes nontrivial isotropy from the matrix decomposition.

Choose a finite clopen partition of `C` separating distinct points
in each `H`-class and refining all original coefficient partitions.
Such a partition exists: the off-diagonal part of `H` is compact,
has finitely many nonzero exponents with compact clopen domains, and
none has a fixed point. Finitely many clopen source-range separations
give the partition. Order its atoms and choose the point in the first
occupied atom as each class's representative. The representative set
is clopen, since whether a related point lies in an earlier atom is
a finite clopen test along the finitely many maps describing `H`.

Refine the representative set finitely according to the occupied
atoms, the exponents of the arrows from the representative, and the
original coefficient values on the resulting levels. On each cell
`B`, classes have a fixed size `h` and clopen continuously enumerated
levels `B_1,...,B_h`. The characteristic arrows from level `j` to level
`i` form matrix units `E_ij(B)`. All prescribed elements have constant
matrix entries on each such cell. The resulting finite direct sum of
algebras `M_h(F_q)` contains them all. It has a local identity supported
on `C`. No global transversal or uniform bound for all of `U` is needed.

This proves the lemma and the locally matricial assertion for `I_U`.

## 4. Identify the full restriction kernel

A locally constant function on a closed subshift extends to `X` by
a finite clopen partition. Crossed-product normal forms give

`0 -> I_U -> R_X -> R_Y -> 0`.

The kernel coefficients have compact support in `U`, because locally
constant functions on compact `X` have clopen support. Lifting elementary
coefficients gives an epimorphism `G_n(X) -> G_n(Y)`.

For `g in GL_n(R_X)` restricting to the identity, write `g=1+A` and
`g^{-1}=1+B`, with all entries of `A,B` in `I_U`. Place these entries
in one finite matrix-product subalgebra `F subset I_U`, with local
identity `p`. The inverse equations give

`g=(1-p)I_n+h`, `h in GL_n(F)`.

For `n>=2` and `F=product_j M_(h_j)(F_2)`,

`GL_n(F)=EL_n(F)=product_j SL_(n h_j)(F_2)`.           (5)

All invertible matrices over `F_2` have determinant one. Elementary
flattening works with two outer blocks: a scalar root within one
block is a commutator through the other block; cross-block roots are
entries of block elementary matrices. Consequently `g` lies in
`EL_n(R_X)` and is generated by roots with coefficients in `I_U`.
Conversely every such root is in the restriction kernel. This proves
that general linear and elementary kernels agree.

For finitely many kernel elements, put all deviations from identity
and their inverse deviations in one `F`. They then lie in the same
finite group `GL_n(F)`, proving local finiteness of `K_n(U)`.
The field `F_2` is essential to (5): over larger finite fields
determinant classes may survive. The local algebra lemma itself
holds over every finite field.

## 5. All of that kernel is MF-invisible

For every compressed clopen `P` from section 2, put `p=1_P` and
`d=1_(P\T(P))`. The earlier explicit calculation gives

`s=u p+1-p`, `t=p u^{-1}+1-p`, `ts=1`, `1-st=d`.

The printed finite-order torsion-defect theorem puts every `e_ij(d)`
in the MF radical of `EL_n(R_X)` for `n>=4`.

The ideal generated by all these indicators is exactly `I_U`:
their translates cover `U`, and every compact coefficient support
has a finite subcover. Subdivide into clopen pieces subordinate to
that cover. Each piece indicator is a coefficient multiple of a
translated defect, and Laurent sums give the ideal assertion.

In rank at least three, normal kernels propagate invisible root
coefficients to their generated two-sided ideal. For distinct indices,

`[e_ik(a),e_kj(d)]=e_ij(ad)`,
`[e_ik(ad),e_kj(b)]=e_ij(adb)`;

conjugation supplies root positions and root addition supplies sums.
Thus every root with coefficient in `I_U` is invisible. Section 4
says these roots generate all of `K_n(U)`. The LEF quotient `G_n(Y)`
gives the opposite radical inclusion, proving (2).

Any MF-target map out of `GL_n(R_X)` kills the same kernel by restriction
to its elementary subgroup. Its restriction image in `GL_n(R_Y)` is
LEF, proving the general linear assertion.

## Scope

The analytic input remains the printed rank-four torsion-defect theorem.
Ranks two and three with short periodic orbits remain unsettled. This
result identifies the full radical for all finite-alphabet subshifts
over `F_2` in ranks at least four. It decides neither soficity nor
hyperlinearity. These are written deductions, with no Lean verification
or global priority assertion.

## Dependency validation

Cairn 2.13.1 checked the six new nodes on MSI against snapshot
`244f2890c77f198f57f74e86ac528dc933f366f9` in 32.145 seconds.
Both `check --changed` and `preview` returned zero, all three claims
were `ESTABLISHED`, and neither graph had errors. The graph contained
10,408 claims and 10,670 routes. The
[receipt](pestov91-core-cairn-receipt-2026-09-13.json) records the source
delta and runner hashes. This paragraph and that receipt were added
after the run. This batch has a written proof and dependency checks;
no finite computation or Lean verification is claimed to establish
the general topological and algebraic assertions above.
