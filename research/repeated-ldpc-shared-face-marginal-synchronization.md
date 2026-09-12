---
rg: 2
id: repeated-ldpc-shared-face-marginal-synchronization
kind: claim
title: Synchronize repeated LDPC face PVMs to literal shared marginals without losing the local code structure
distinct_from:
  constant-size-private-basins-give-uniform-root-control: that transfers one selected root to one anchor through a fixed basin; this must synchronize every parity-face occurrence while retaining its joint PVM.
  binary-face-pvm-is-determined-by-coordinate-reflections: that gives uniqueness once marginals are literally equal; this must obtain literal equality from average occurrence defects.
  averaged-commutators-do-not-give-abelian-table: that refutes the tempting reduction from averaged shared-coordinate commutators to a full approximate table; this claim can only survive by using the redundant parity faces inside the rounding step.
---

OPEN.  Use the **balanced** repeated LDPC occurrence system: every original
parity face is repeated `Theta(M)` times before it is mixed with the
`Theta(M^2)` pair-sum faces.  From small average fixed-face PVM defect and
bounded-degree equality-expander defect, produce exact local
codeword PVMs on the same Hilbert space whose copies of each logical binary
coordinate are literally one shared reflection, with total squared movement
bounded by a dimension- and length-independent modulus.

The balancing is load-bearing even classically.
`unbalanced-pair-sum-overlay-has-scalar-syndrome-escape` shows that an unbalanced overlay
with one copy of each original face forgets the all-one syndrome: all pair
sums pass, the original defect has density `O(1/M)`, yet bounded column
degree keeps the tuple a constant distance from every exact code
representation.  Repeating originals `M` times removes this escape while
using only `O(M)` occurrences per logical coordinate, so the existing
quadratic repetition absorbs it at bounded physical degree.

Correcting each bounded face separately is uniform, and synchronizing bare
reflections on an equality expander is uniform in average.  Doing both at
once is not formal: replacing a face marginal by the synchronized reflection
can destroy joint commutation and parity, while re-correcting the face can
move its marginal again.  This is the finite-overlap agreement step needed
before the adjoint face-Hamiltonian gap can be applied.

The natural damp-then-return implementation is now excluded, not merely
unproved.  `damped-cloud-face-return-has-an-exact-scalar-fixed-sheet` uses a
balanced length-three original-plus-pair-sum packet whose exact scalar face
characters have zero cloud means.  Every nonterminal damped average retains
the old occurrence signs, so the sign-first Loewner face return restores the
inconsistent tuple exactly; its positive equality cross term cancels the
whole cloud-energy gain.  Direct-sum weighting puts this fixed sheet at
arbitrarily small normalized defect.  Therefore local face exactification
and equality damping need a genuinely coordinated global character choice;
their separate uniform cost bounds cannot be composed into the required
rounding modulus.

`shared-face-synchronization-is-uniform-lcs-hs-stability` identifies this
step exactly with uniform same-dimension HS stability of the growing
homogeneous LCS colimits in their redundant occurrence presentations.  In
particular, the Lipschitz face-atom formula cannot be applied to independently
averaged spectral signs until their within-face commutation is already known.

Nor can one now invoke uniform HS stability of all finite abelian groups.
That theorem assumes an approximate multiplication table on all pairs of
group elements.  `averaged-commutators-do-not-give-abelian-table`
exhibits Clifford pairs whose averaged generator commutator energy vanishes
while the ordered-word table has defect at least one.  Thus any successful
proof must consume the redundant parity faces before constructing the
abelian table; extracting only average pairwise commutation loses the needed
information.

The obstruction is not a density loss in the quadratic overlay.
`pair-sum-faces-control-shared-commutator-energy` assigns every logical pair
to an original or pair-sum face with bounded congestion, and proves that
face-to-shared occurrence movement controls the complete averaged logical
commutator energy with a uniform constant.  What is missing is exactly the
upgrade from that generator statistic, together with parity, to an exact
shared code representation.

Published quantum tensor-code pasting does not supply this upgrade as a
black box.  `jnvwy-pasting-does-not-close-ldpc-synchronization` verifies that
JNVWY constructs its global codeword PVM in the same tracial algebra, but its
error is polynomial in the tensor/interpolation parameters and its test
assumes one point measurement across growing line and subcube incidence.
Bounded-degree occurrence splitting therefore recreates the present gate;
for binary tensor codes, unbounded message dimension forces either a growing
line-answer packet or growing tensor dimension and robustness loss.

The noncentral sector is now sharply localized by matrix type.
`bounded-type-balanced-occurrences-synchronize` proves the full same-Hilbert
conclusion, including reconstruction of every face PVM, whenever the algebra
generated by all occurrence reflections has uniformly bounded irreducible
block dimension.  Thus neither a fixed finite packet nor any central mixture
of bounded nonabelian blocks can witness failure.  A remaining countermodel
must carry positive trace in irreducible dimensions tending to infinity;
controlling that unbounded-type mass is still open.

The scalar fixed sheet also admits an explicit coordinated repair, rather
than only the bounded-type compactness argument.
`balanced-occurrences-have-linear-character-decoder`
diagonalizes the entire abelian occurrence algebra once, takes cloud
majorities on every common spectral atom, and applies the classical LTC
decoder there.  It gives a linear same-Hilbert modulus, uniformly over
arbitrary direct sums and nonatomic scalar mixtures.  Hence the fixed-sheet
no-go diagnoses the locality of the return map: it does not leave a scalar
or centrally mixed obstruction to synchronization.  The unresolved sector
must fail to supply one common abelian spectral space.
