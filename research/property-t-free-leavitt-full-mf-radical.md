---
rg: 2
id: property-t-free-leavitt-full-mf-radical
kind: claim
title: Derive binary-Leavitt full MF collapse without Kazhdan hypotheses
root: true
goal: true
artifacts:
  - research/property-t-free-leavitt-via-corona-module-decoder.md
  - research/property-t-free-leavitt-via-full-support-hs-decoder.md
  - research/property-t-free-leavitt-via-opnorm-return-row.md
  - research/property-t-free-leavitt-via-atomic-morita-return.md
  - research/property-t-free-leavitt-via-chromatic-code.md
  - research/property-t-free-leavitt-via-nested-prefix-conjugacy-code.md
  - research/leavitt-nonsoficity-does-not-close-macroscopic-mf-branch.md
  - research/maximal-sparse-character-atom-does-not-return-multiplicity.md
  - research/three-active-atoms-do-not-form-binary-reynolds-frame.md
  - research/three-active-atoms-reynolds-type-audit-proof.md
  - research/dual-prefix-heisenberg-table-has-two-simultaneous-unit-orbits.md
  - research/dual-prefix-two-simultaneous-unit-orbits-proof.md
  - research/spectral-cut-removes-cz-orientation-but-not-carrier-holonomy.md
  - research/cz-spectral-cut-carrier-holonomy-audit-proof.md
  - research/two-shared-gauge-selector-rows-have-an-affine-rank-obstruction.md
  - research/two-shared-gauge-selector-rank-proof.md
  - research/binary-leavitt-two-shared-gauge-selector-compiler.md
  - research/property-t-free-leavitt-via-two-shared-gauge-rows.md
  - research/binary-leavitt-native-two-scale-cross-gram-positive.md
  - research/two-scale-cross-gram-implies-shared-gauge-compiler.md
  - research/active-core-density-keeps-rectangular-capacity-critical.md
  - research/positive-density-critical-capacity-proof.md
  - research/trace-cyclic-balance-does-not-bypass-native-two-scale-occurrence.md
  - research/local-morita-sibling-cells-have-a-two-qubit-periodic-absorber.md
  - research/involution-normal-product-forces-one-factor-overlap.md
  - research/finitely-presented-amenable-undecidable-word-problem.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

OPEN.  Let `R=L_(F_2)(1,2)` and let

```text
Delta=St_20(R),                    z=x_13(s_1t_1).
```

The root `z` is a nontrivial involution and normally generates `Delta`.
Prove

```text
Rad_MF(Delta)=Delta
```

without assuming property `(T)` for either a compression source or the
ambient group.  More general elementary-group versions are welcome, but the
literal binary-Leavitt Steinberg group is the fixed target of this goal.

The proposed route is intrinsic to norm matrix coronas.  A surviving root
has exact finite additive and Heisenberg multiplicity germs.  The remaining
step is to assemble those germs into one nonzero finitely generated
projective corona module carrying a unital action of `R`.  Rank-germ
Hilbert-hotel cancellation would then force that module to vanish.

There are now seven sharply separated analyzed routes; the seventh is
refuted below.

1. Assemble finite root germs into one finite-projective norm-corona
   coefficient module and apply rank-germ Hilbert-hotel cancellation.
2. Reblock to a positive-density active core, construct the corresponding
   normalized-Hilbert--Schmidt coefficient module, and apply tracial
   cancellation.
3. Recover exact depth-one and depth-two packets on one nonzero carrier and
   authenticate one operator-norm coarse-to-fine return row.
4. Return only the two diagonal inverse rows and completeness row of one
   binary Leavitt cell to the prescribed nontrivial `z`-spectral atom and
   apply the Atomic Leavitt Gap.
5. Avoid projection decoding entirely: compile the marked root into an
   infinite-chromatic diagonal/off-diagonal commutator code whose discrepancy
   words have uniformly bounded relator area, and apply operator-norm
   compactness in each frozen matrix coordinate.
6. Reblock the surviving root to positive density and authenticate two
   scale-changing selector rows whose controlled groupifications retain one
   common multiplicity involution; their incompatible affine rank equations
   then force a fixed normalized-HS defect.
7. The refuted nested-prefix route uses idempotent roots as an infinite
   complete graph whose pairwise differences are conjugate to the mark; its
   required uniform filling-area bound is algebraically impossible.

The fourth route proves that positive carrier density, global module gluing,
off-diagonal Leavitt rows and exact `M_2/M_4` packet ranks are unnecessary at
the terminal MF step.  Its unresolved content is still a genuine
finite-matrix same-atom decoder: the algebraic root presentation does not by
itself identify the returned coefficient arrows with that prescribed
spectral projection.

The fifth route has a different open seam.  Infinite orbit geometry is not
enough: choosing representatives introduces stabilizer holonomy whose
relator cost can grow with address length.  It needs a bounded-area section
or another finite-coordinate coherence mechanism.  Thus the two live
frontiers for these branches are explicit: authenticate a Leavitt return on
one prescribed atom, or authenticate an infinite-chromatic commutator code
at bounded presentation cost.

The tempting composition with the already proved Leavitt nonsoficity theorem
has also been audited.  A surviving torsion mark does reblock to a faithful
operator-norm asymptotic model with pointwise normalized-HS separation, but
the available nonsoficity derivations obtain their finite action charts from
Kazhdan expansion.  The exact missing arrow is recorded in
`leavitt-nonsoficity-does-not-close-macroscopic-mf-branch`: a
Leavitt-specific, Property-`(T)`-free shadow-to-action converter.  Generic
hyperlinear-to-sofic conversion is not assumed.

The sparse-global-atom route has also been tightened.  Choosing a
coordinatewise maximal exact character atom does not force a rank return:
the branch/shear image is a character atom in the corona but can split among
arbitrarily many finer exact atoms at every moving coordinate.  The precise
comparison failure is
`maximal-sparse-character-atom-does-not-return-multiplicity`.
On the positive side,
`norm-corona-sparse-character-atom-reduces-pointwise-centralizer` shows that
the sparse atom may be chosen to reduce both branch actors and the entire
countable Heisenberg self-copy subsystem, since they fix the common central
root pointwise.  Together with
`binary-leavitt-two-branch-character-restriction-is-faithful`, this removes
actor movement and global character-label ambiguity.  The remaining corona
seam is strictly the joint multiplicity coupling: the two reducing branch
representations can still occupy independent tensor coordinates, and no
Leavitt coefficient action on the selected projective carrier has yet been
decoded.

The apparent `3+1` affine-packet shortcut has likewise been type-checked.
Those four involution-character atoms are not the `p^2` adjoint Reynolds
return channels: the affine coefficient field has characteristic `p>=5`,
and the packet idempotents do not survive a characteristic-two
specialization.  The precise numerical and operator-type firewall is
`three-active-atoms-do-not-form-binary-reynolds-frame`.

The bounded-area branch has acquired a stronger algebraic reduction.  Every
dual-prefix row/column pair is simultaneously stabilized-conjugate to one of
the two depth-one prototypes, according only to equality or inequality of
the prefixes.  This is
`dual-prefix-heisenberg-table-has-two-simultaneous-unit-orbits`.  The
remaining issue is no longer cancellation of long coefficient words; it is
coherent wordization, because the simultaneous conjugator depends on the
ordered pair while the compactness argument must choose each vertex word
once.

There is now a strictly stronger one-indexed reduction.
`binary-leavitt-cumulative-complete-graph-table` replaces
the equality/off-diagonal prefix table by cumulative rows
`C_j=A_0+...+A_j` and adjacent column pairs `H_j=B_j+B_(j+1)`.  In
characteristic two the diagonal product is `q`; a later row sees both
adjacent coordinates and gives `q+q=0`, while an earlier row sees neither.
Thus the full pairing is `C_kH_j=delta_(kj)q`, and canonical vertex words
realize complete graphs of unbounded size.  The two families are global dual
triangular bases, so one finite-chart basis change normalizes the entire
table simultaneously.  The remaining bounded-area problem no longer needs
pair-dependent vertex charts: it is the narrower question whether this one
growing triangular basis change admits a fixed-cell self-similar fold instead
of a length-`M` elementary-row telescope.

That proposed repair is now fenced for the existing vertex words.
`leavitt-chromatic-tables-have-area-divergence` freezes one adjacent column
in the cumulative table and obtains infinitely many distinct cosets in the
centralizer of a fixed involution, so no self-similar rewording of those same
rows can make their edge areas uniform.  The canonical Morita-tree variant
also fails even after synchronizing the two tail depths:
`level-synchronous-first-mismatch-area-is-centralizer-impossible` conjugates
one column at each level back to a fixed involution and produces
exponentially many bounded-area centralizer cosets.  A viable chromatic route
therefore needs genuinely different vertex data, not a faster proof of the
cumulative or canonical-tree commutators.

The corona route has likewise crossed a precise language boundary.  The
range-sum fold is object-erasing but remains a positive-unipotent word.
`finite-positive-root-fragments-have-marked-regular-models` gives exact
marked finite regular models for every finite positive-root fragment with
all literal coefficient occurrences, including that fold; its identity
carrier is already common and reducing.  A single non-scalar signed
Whitehead cell is still finite-model compatible by
`partial-whitehead-cell-has-marked-finite-model`.  Consequently the remaining
corona return must be a two-branch non-scalar mixed/opposite-root occurrence
which destroys the scalar Whitehead specialization and couples directly to
the Heisenberg multiplicity payload.

There is an exact orbit obstruction inside that remaining corona seam.
`surviving-leavitt-corona-character-has-infinite-parabolic-orbit` proves that
every nontrivial global character atom for a last-column root module has an
infinite orbit of pairwise orthogonal equivalent projections under the
upper-left Steinberg vertex; one elementary root subgroup already suffices.
A finite orbit would produce a nonzero finite-dimensional right module over
the binary Leavitt algebra.  The resulting inequalities `M[P]<=[1]` for all
fixed `M` are compatible with sparse escape and still fall short of
`2[P]<=[P]`.  Thus no bounded character menu or finite parabolic atom cycle
can return the sparse carrier.  The load-bearing mixed-root row must fold
this intrinsically infinite orbit back to one finite projective reservoir.

The rank scale along that orbit is now uniform.
`binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale` uses the fixed
two-commutator saturation formula and, in the reverse direction, a sandwich
`uav=1` inside two more Steinberg commutators.  Every nonzero elementary root
and the marked root are products of four conjugates of one another.  Hence
after active-core reblocking every fixed nonzero coefficient root has a
common positive normalized-rank floor.  This rules out coefficient-dependent
rank decay but not diffuse Haar escape, and the eventual coordinate may still
depend on the coefficient.  A successful return must preserve this uniform
rank scale while authenticating a moving coefficient or mixed-root orbit
fold.

The same four-conjugate formula now gives more than rank comparison.
`involution-normal-product-forces-one-factor-overlap` telescopes a product of
`k` involutions on the output's nontrivial spectral carrier and proves that
one input carrier has at least a `1/k^2` share of its trace there.  Thus every
nonzero binary-Leavitt root carrier has at least `1/16` of its mass in one
addressed conjugate of the marked carrier, robustly for matrix microstates.
This is a genuine fixed positive overlap, but the selected conjugate depends
on the coefficient/normal word.  It does not yet identify the two prescribed
native scale transports, so it strengthens rather than closes the scalar
holonomy leaf.

The seventh route supplies a concrete moving-coefficient family, but is now
also refuted by fixed-centralizer properness after an exponent-two triangle
reduction.
`leavitt-nested-prefix-conjugacy-clique` takes
the nested idempotents `e_m=s_(0^m)t_(0^m)`.  For `j<k`, their
characteristic-two difference is the nonzero annulus projection

```text
e_j+e_k=sum_(ell=j)^(k-1)
           s_(0^ell 1)t_(0^ell 1),
```

which is explicitly Murray--von Neumann equivalent to `q=s_1t_1` by matching
the annulus leaves with a complete prefix code below `q`.  Thus every
`x_12(e_j)^(-1)x_12(e_k)` is conjugate to the marked root, and the vertices
form an actual infinite clique.  The general established criterion
`bounded-area-conjugacy-difference-code-kills-mf-mark` turns this directly
into MF collapse if those edge conjugacies have one uniform presentation
area.  That quantitative leaf is refuted.  Relative to `b_0`, the three
edge cells `(0,1)`, `(0,m)`, and `(1,m)` would uniformly fill the commutator
of two basepoint differences.  Those differences are commuting involutions
in infinitely many distinct cosets modulo the fixed first one, contradicting
`finite-mark-centralizer-commutator-area-is-proper`.  Thus even a
self-similar fold of the whole annulus cannot make this clique uniform.

On the atomic/controlled-reflection branch, the multiplicity orientation is
now separated from the actual carrier problem.  An adaptive eigenspace cut
of the multiplicity involution makes either `T` or its central-sign correction
the literal fine reflection on a nonzero cut.  The cut need not be preserved
by the Whitehead actuator, however, and its coarse and fine completions retain
the `2`-versus-`4` typed escape.  This exact boundary is
`spectral-cut-removes-cz-orientation-but-not-carrier-holonomy`.

There is also a new two-row alternative to literal orientation cancellation.
If two scale-changing selector rows on one packet carrier have conjugate
multiplicity involutions, their source/fine rank ratios impose two affine
equations on their common positive-sign fraction.  The
binary `1/2 -> 1/4` row forces that fraction to be `1/2`, while the next
`1/4 -> 1/8` row forces it to be `5/6`.  This is the dimension-independent
obstruction
`two-shared-gauge-selector-rows-have-an-affine-rank-obstruction`.  It narrows
the compiler target: a mixed Leavitt two-cell may share one gauge across two
incompatible rows instead of producing a literal fine reflection.  Cairn's
outer-class audit shows that ordinary packet dressing cannot supply this
sharing, so the remaining construction is genuinely scale-changing.
The corresponding sixth route is now wired through
`binary-leavitt-two-shared-gauge-selector-compiler` and
`property-t-free-leavitt-via-two-shared-gauge-rows`.
Only conjugacy on a nonzero reducing subcorner, not literal global gauge
equality, is needed: the established fixed-mass cross-Gram cutoff plus two
mixed Pauli commutators supplies the analytic alignment once one native
positive cross-Gram overlap is authenticated.
The affine rank endpoint is insensitive to unused tensor spectators, so the
spectator-gap failure of the older mutual-bicommutant route does not apply.
This has been factored to one scalar leaf,
`binary-leavitt-native-two-scale-cross-gram-positive`: authenticate any
fixed positive cross-Gram mass for the native depth-one/next-refinement
transport pair and two mixed Pauli tests.  The established fixed-mass corner,
polar, and commutant lemmas then close the entire shared-gauge compiler.
The direct/two-step coefficient identity
`(s_(000)t_(00))(s_(00)t_0)=s_(000)t_0` does not supply that scalar: Cairn's
rectangular mixed-loop and Whitehead/swap models realize the identity exactly
while retaining different completed carrier objects.  The surviving row
must erase that object distinction rather than add another associativity
triangle.
Positive-density reblocking also does not create the required overlap:
`active-core-density-keeps-rectangular-capacity-critical` embeds
the coherent nested packet in the entire active core while keeping every
two-branch capacity inequality critical and every sibling cross Gram zero.
The alternative trace-cyclic triangle bookkeeping does not bypass this leaf:
`trace-cyclic-balance-does-not-bypass-native-two-scale-occurrence` proves
that its third balance edge must first authenticate the two actual gauge
projections on equal normalized carriers, which is itself the missing
object-erasing occurrence coupling.

A seed-free computability shortcut has also been excluded.  Operator-MF does
not make the complement of the word problem recursively enumerable: a single
finite matrix tuple with small relator defect is not a sound nontriviality
certificate because the necessary defect threshold depends on an unknown
filling of the tested word.  This is not merely a logical caution;
`finitely-presented-amenable-undecidable-word-problem` supplies a fixed
finitely presented solvable (hence operator-MF) counterexample with
undecidable word problem.
