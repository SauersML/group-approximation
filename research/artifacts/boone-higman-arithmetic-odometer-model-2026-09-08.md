# An odometer model for the arithmetic germ groups, 2026-09-08

The A5*A5 arithmetic shell envelope's finite-presentation question
remains open. Its near group and full isotropy germ group now have
explicit finitely presented ambient groups. This supplies a concrete
setting for the relation problem without identifying a subgroup with
its ambient group or identifying the envelope with its germ quotient.

## Prefix tables and near index

On r h-adic Cantor roots, an element of B=V_(h,r)(Z_odometer) has
prefix tables with integer carry labels c_i. On the nonnegative
integer points each branch gives a positive affine map between
residue progressions. It omits c_i range points when c_i is positive,
or -c_i domain points when negative. Hence its near index is sum c_i.
The integer points remain dense after finite deletions, so this near
action is faithful.

The odometer is a bounded automata group, so B has type F_infinity
by [Belk--Hyde--Matucci, Theorem 2.12](https://arxiv.org/html/2407.03149v1#S2.SS3).
The charge kernel is finitely generated: take V_(h,r) and one
involution exchanging two proper cones with opposite carry labels.
Prefix conjugacy and a plain cone exchange give any pair of opposite
localized odometers. Every table with zero total carry is a product
of such pairs after finite refinement. This is a generation proof;
finite presentation of the charge kernel is not claimed.

## Apply the model to the benchmark

For h=59 and r=2, the single-ray A5 generator branches have source
step 118 and image steps 6962, 118, or 2. These are respectively
two-root prefix charts with output depths 2, 1, or 0, followed by
integer odometer carries. The near shift itself exchanges the roots
and adds one on the second-root carry. Thus R_nu embeds in B with
its original near-index character.

The symmetric fiber product F_B=B x_Z B is finitely presented by
[Martinez-Perez, Proposition 3.8](https://arxiv.org/pdf/1302.2745v2),
using the finite generation of the charge kernel. In the wreath
product B wr C_2, adjoining (s,1)*omega to F_B gives an index-two
finitely presented extension D. Its conjugation and square formulas
match those of the full shell germ group Q, yielding Q<=D.

## A necessary parity restriction sharpens the ambient group

Because 59 is odd, leaf-permutation parity epsilon is invariant
under table refinements: an expansion inserts 58 entries and its
odometer child permutation is an even 59-cycle power. Hence
epsilon:B->Z/2 is a homomorphism. The perfect input has parity
zero, while s has both parity and charge one. Consequently R_nu
lies in B_0=ker(epsilon-(chi mod 2)), an index-two subgroup of B.
A pure prefix transposition is excluded, so R_nu is not all of B.

B_0 is finitely presented and still has a surjective charge with
finitely generated kernel. Using B_0 instead of B gives a smaller
finitely presented fiber-product germ host. Whether R_nu equals
B_0 has not been proved.

## What remains unresolved

No finite-index assertion for R_nu in B_0, or Q in its ambient,
has been proved. A finitely generated subgroup of a finitely presented group
need not be finitely presented. Even finite presentation of Q would
leave the one-singularity stabilizer's neighborhood kernel to handle;
the whole E_nu is not embedded in D by this construction.

The universal input route remains wider still: its arbitrary decidable
inputs need not have residue-affine regular actions. These models
advance the explicit arithmetic benchmark without replacing the full
Boone--Higman objective by that benchmark.

These are written mathematical arguments with imported finiteness
theorems identified above. They were not checked by Lean or a GPU.
No local computation, build, or cloud resource was used.

## Remote validation record

The odometer index kernel and germ ambient constructions were
committed as `d832e46c3`; the parity restriction as `4bfa78d74`.
Both are integrated into main at
`7629daf11535a1170e33cbd0540275f275990a1a`.

[Remote research check 34301242813](https://github.com/SauersML/group-approximation/actions/runs/34301242813)
passed for that exact commit. It ran source syntax checks, the
existing exact finite negative and cyclic-shift controls, and Cairn
graph validation. The optional Lean preflight was skipped. No new
mathematical argument here was checked by Lean or by GPU computation.
The downloaded record is `.cairn/bh-odometer-model-check-20260908/`.

The actual `node_status` fields and derivations were inspected:
the finitely generated odometer index kernel, the finitely presented
germ ambient groups, and the parity-charge constraint are
`ESTABLISHED` in the written-proof graph. The A5 shell envelope's
finite presentation, the universal perfect-input presentation claim,
and Boone--Higman remain `OPEN`.
