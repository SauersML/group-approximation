---
rg: 2
id: property-t-free-leavitt-full-mf-radical
kind: claim
title: Derive binary-Leavitt full MF collapse without Kazhdan hypotheses
root: true
goal: true
artifacts:
  - research/proposed-property-t-free-whitehead-proof-safe-prefix-audit.md
  - research/proposed-property-t-free-whitehead-proof-safe-prefix-route.md
  - research/property-t-free-leavitt-via-corona-module-decoder.md
  - research/property-t-free-leavitt-via-full-support-hs-decoder.md
  - research/property-t-free-leavitt-via-opnorm-return-row.md
  - research/property-t-free-leavitt-via-atomic-morita-return.md
  - research/moving-signed-source-does-not-localize-paid-sheet-detector.md
  - research/moving-signed-source-sheet-detector-fence-proof.md
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
  - research/finite-packet-rank-polytope-is-complete.md
  - research/finite-packet-rank-polytope-proof.md
  - research/finite-packet-holonomy-cuts-the-multiplicity-simplex.md
  - research/finite-packet-holonomy-fixed-simplex-proof.md
  - research/holonomy-rank-gap-is-a-carrier-local-mf-certificate.md
  - research/carrier-local-holonomy-rank-mf-proof.md
  - research/artifacts/property-t-free-rank-polytope-holonomy-integration-2026-08-25.md
  - research/binary-leavitt-two-shared-gauge-selector-compiler.md
  - research/property-t-free-leavitt-via-two-shared-gauge-rows.md
  - research/binary-leavitt-native-two-scale-cross-gram-positive.md
  - research/two-scale-cross-gram-implies-shared-gauge-compiler.md
  - research/canonical-cross-gram-does-not-close-arbitrary-mf-active-profile.md
  - research/binary-leavitt-arbitrary-profile-native-cross-gram.md
  - research/arbitrary-profile-cross-gram-implies-shared-gauge-compiler.md
  - research/active-core-density-keeps-rectangular-capacity-critical.md
  - research/positive-density-critical-capacity-proof.md
  - research/trace-cyclic-balance-does-not-bypass-native-two-scale-occurrence.md
  - research/local-morita-sibling-cells-have-a-two-qubit-periodic-absorber.md
  - research/commuting-double-commutator-has-direct-mark-overlap.md
  - research/involution-normal-product-forces-one-factor-overlap.md
  - research/root-valued-relative-transport-forces-cross-gram.md
  - research/seventeen-root-star-has-marked-triple-overlap.md
  - research/marked-root-star-carries-three-anchored-cells.md
  - research/signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped.md
  - research/finitely-presented-amenable-undecidable-word-problem.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
  - research/coarse-fine-offdiagonal-loops-are-morita-blind.md
  - research/single-root-completeness-attachments-are-exhausted.md
  - research/endpoint-whitehead-star-braid-synchronizes-native-gauges.md
  - research/endpoint-whitehead-star-braid-proof.md
  - research/full-moving-hecke-packet-retains-q-kernel-profile.md
  - research/full-moving-hecke-q-kernel-profile-proof.md
  - experiments/full_q_moving_gl8_permutation_audit.py
  - research/b2-pairs-full-hecke-first-support.md
  - research/b2-full-hecke-first-support-proof.md
  - research/b2-b3-pair-full-hecke-four-native-sectors.md
  - research/b2-b3-full-hecke-four-sector-proof.md
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
`k` involutions on the output's nontrivial spectral carrier.  In the specific
binary-Leavitt double commutator, the output commutes with both conjugating
roots, so `commuting-double-commutator-has-direct-mark-overlap` makes all four
factor overlaps equal.  Every nonzero coefficient in a root position
disjoint from the marked indices—canonically `x_42(a)`—therefore puts at
least `1/4` of its own mass, and at least `1/16` of the marked mass, directly
in the original marked carrier, robustly for matrix microstates.  This
removes the conjugate-selection ambiguity on the disjoint root rectangle.
It still does not force two native root slices to meet each other inside the
larger marked carrier, so it strengthens rather than closes the scalar
holonomy leaf.

This direct floor also yields a concrete terminal interface.
`root-valued-relative-transport-forces-cross-gram` rewrites the cross-Gram
energy of two marked-root restrictions `g_1P_z,g_2P_z` as the overlap between
`P_z` and its translate by `g_1^(-1)g_2`.  If that relative word conjugates
`z` to a nonzero marked-index-disjoint root such as `x_42(a)`, the new direct
floor proves `(NCG1)` with `gamma=1/4`.  What remains is therefore an exact
occurrence-typing question: the two native stabilized selector maps must be
those full-unitary restrictions.  The rectangular countermodel shows that
coefficient-path equality without this typing is insufficient.

The direct floor also creates a prescribed positive common carrier for two
ordinary root-position channels.  The seventeen commuting roots
`x_(i,2)(q)`, `4<=i<=20`, are two-transitively permuted by Weyl words fixing
`z`.  `seventeen-root-star-has-marked-triple-overlap` combines that symmetry
with a second moment to prove

```text
tau(P_z P_(x_42(q)) P_(x_52(q))) >= (7/136)tau(P_z).
```

This removes both adaptive pair selection and vanishing carrier mass for a
fixed two-channel root packet.  The two channels are still same-coefficient
root-position transports, not the unequal-scale coefficient transports in
the selector rows.  The next construction must make those scale rows act on
this fixed triple carrier, or prove that their native relative word has the
root-valued form above.

The root-star symmetry extends through five prescribed roots.  In particular
the four-root carrier for `z,x_42(q),x_52(q),x_62(q)` has mass at least
`(11/1360)tau(P_z)`.  On it,
`marked-root-star-carries-three-anchored-cells` realizes three cross-commuting
Heisenberg pairs from the factorizations

```text
q=(s_1t_(0^m))(s_(0^m)t_1),             m=1,2,3.
```

Their cross-products are exactly `s_(00)t_0` and `s_(000)t_(00)`, the two
native scale arrows.  This puts the three arm cells and a literal `M_8`
packet on one fixed positive carrier.  The remaining occurrence seam is now
the comparison between the cross-product coefficient occurrences and their
selector-word occurrences; the index layout making the three Heisenberg
cells cross-commute does not itself make those cross-products operator
products on the carrier.

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

There is now an additional MF-specific quantifier fence on this sixth route.
The current statement of
`binary-leavitt-native-two-scale-cross-gram-positive` is restricted to
canonical-trace normalized-HS microstates.  Active-core reblocking of an
arbitrary norm-corona representation supplies HS-small relator defects and
positive marked mass, but not the canonical trace moments of the other
packet words.  This is
`canonical-cross-gram-does-not-close-arbitrary-mf-active-profile`, which
invalidates the current route from that canonical scalar claim to the
arbitrary-profile shared-gauge compiler.  Consequently the four center-chain
Hecke fractions and any canonical cross-Gram closure remain relevant to the
non-hyperlinear lane, but they do not close this MF goal.  The MF repair must
prove the native estimate uniformly over arbitrary active trace profiles or
derive the needed profile intrinsically from the surviving mark.
The repaired scalar target is now named
`binary-leavitt-arbitrary-profile-native-cross-gram`, and
`arbitrary-profile-cross-gram-implies-shared-gauge-compiler` records the
valid route from that stronger input to the shared-gauge compiler.

The alternate operator-norm prefix-loop probe has also been completed, with
a negative result.  `coarse-fine-offdiagonal-loops-are-morita-blind` writes
all crossed arrows between the depth-one `M_2` and depth-two `M_4` charts.
Their shortest forward and reverse paths have three coefficient factors, and
every ordinary non-opposite Steinberg loop obtained by pasting them is exact
in a finite marked six-object model.  In that model the two packet identities
are orthogonal and their difference has operator norm one.  Therefore neither
route 3 nor route 4 can be closed by adding a fixed family of purely
multiplicative off-diagonal loops.  The missing word must attach the additive
coefficient-completeness occurrence, or an equivalent spectral support
incidence, to the selected marked carrier.

The smallest literal completeness continuation is exhausted as well.
`single-root-completeness-attachments-are-exhausted` classifies all root
positions relative to `x_ab(p)x_ab(q)=x_ab(1)`.  The only noncommuting
possibilities are the one-sided composable intermediate-arm cell and the
opposite-root partial-Whitehead cell; their strongest native specializations
already have exact marked finite models.  Consequently an operator-norm
repair must relate at least two new root occurrences and lock their relative
reservoir gauge.  There is no remaining one-root word to try between the
additive fold and the marked support.

The first genuinely full-presentation operator-norm payment on this repaired
route is now established.  `native-t00-y1-collision-pays-marked-opnorm`
compares the actual row-two arm `x_78(t_00)` with the first prefix arm
`Y_1=x_78(s_0t_00)`.  Their discrepancy coefficient has an explicit
single-sandwich inverse, so its root normally returns to `z` in four
conjugate factors.  On the direct marked/discrepancy overlap, of relative
mass at least `1/16`, the two arms differ by operator norm two.  Thus the
finite `GL_8` collision is not a full-presentation model.

This payment still stops one incidence short of collapse.
`marked-t00-separation-has-gl10-model` separates the two arms, saturates the
discrepancy back to the surviving mark, and realizes all currently named
Hecke/return rows while storing the separation on transverse vertices.
Likewise `fine-idempotent-biaction-return-has-gl10-model` names
`e_00=s_00t_00` and both of its Morita absorption rows, but its literal root
has half negative spectral rank rather than the physical quarter-corner
rank.  The formal operator-norm localization alternative is now established
by `paid-t00-carrier-has-signed-hecke-reynolds-dichotomy`: signed Reynolds
averaging either keeps the paid discrepancy above one half on the actual
common source, or makes one member of a fixed `8192`-word detector menu pay
at least one half on the paid carrier.  The remaining live statement is the
ordinary occurrence step: derive smallness of those detector words from the
presentation relators, or use the source-compressed discrepancy to recover
the unequal native row.  The Reynolds estimate itself supplies neither
implication.

The full detector menu is now algebraically exhausted by
`signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped`.  Apart
from `r_1=1`, every detector normally saturates to `z` in at most sixteen
conjugate occurrences, and conversely every detector is a uniformly bounded
normal word in `z`.  This does not advance the missing occurrence estimate:
the exact `8192`-element audit finds `31` positive-character conjugacy
classes whose internal `L_0` normal closures contain no root.  Those branches
necessarily use external spare-index probes, which lose `Q`-typing.  Thus
normal saturation alone is fenced; the live input remains a source-preserving
occurrence relation or an upper bound on the detector defects.

The external probe menu itself is now exhausted in
`middle-pauli-probes-leave-three-hecke-classes-untyped` and
`five-return-legs-cover-hecke-detectors-not-source-gauge`.  The
literal paid dual menu and the full primal middle menu leave exactly three
endpoint classes, represented by matrices supported from actor sources
`6,9` into targets `2,4`.  Adding `x_12(s_1),x_14(s_1)` closes that endpoint
gap: together with the three middle `X_m` legs, the resulting `240`-cell
menu extracts a nonzero elementary root from all `31` classes.  This is an
algebraic moving-source cover, not the missing MF occurrence.  Exactly two
paid-menu words preserve `(L_0,lambda_0)`, and both centralize it; every
useful probe moves among `24` named conjugate sources with arbitrary
multiplicity chart.  The three endpoint classes have exact mark profile
only at depth `3`, and the current prefix Whitehead fixes the endpoint leg
instead of transporting its coefficient to the adjacent depth.  The
endpoint-Whitehead candidate is now fully computed in
`endpoint-whitehead-profile-has-maximal-gram-overlap`.  It carries the
paired endpoint occurrence through adjacent depths with exact full Grams,
but the resulting six moved types are the reversible `S_3` Cayley profile.
Both incoming edges at each target are onto the whole same target, so their
cross-Gram square equals the complete target mass: the formal
Perron--Frobenius factor `2` is fully paid by maximal overlap.  Retaining one
edge gives spectral radius `1`, and a regular `S_3` reservoir realizes the
moving gauges as exact coboundaries.  The live detector seam is consequently
narrower: supply proper orthogonal subranges, or a source-preserving
fixed-frame multiplicity occurrence, on the already established moving
`R_0 -> P` channel.  Iterating conjugate source names alone cannot close it.

The detector/probe occurrence itself has now also been included, rather than
inferred from the isolated endpoint pair.
`endpoint-detector-cell-retains-coboundary-gauge` proves the exact ordinary
word identities

```text
[g_3,Y_3]=x_23(b_3),
[x_12(a_3),[g_3,Y_3]]=z,
```

and transports the detector, dual probe, signed source and mark-return cell
together through the fresh endpoint Coxeter braid.  This is genuine
same-reservoir transport in moving coordinates, but it still does not close
the MF radical: both incoming maps at every profile target are onto the
whole same range, and the complete occurrence admits the regular `S_3`
coboundary gauge model.  The remaining theorem must create proper unequal
subranges or lock this already-typed cell to one fixed native
quarter/eighth frame.

Using both actor endpoints simultaneously still does not provide that lock.
`two-endpoint-source-intersections-retain-character-square` computes the
full source-character obstruction:

```text
|Ann(K_2)|=4,        |Ann(K_4)|=8,
|Ann(<K_2,K_4>)|=2.
```

The surviving twist yields an exact four-character square in which `Q`,
its `r=2` image and its `r=4` image are pairwise orthogonal.  Every one of
the three exceptional endpoint detectors has positive sign under both
twists, and all nested commutator returns extend chartwise.  Therefore
neither intersecting the two endpoint sources nor imposing the complete
endpoint detector menu forces simultaneous positive subranges in one fixed
`Q` frame.  The full-radical seam remains a twist-breaking mixed native
occurrence with proper range or nonzero fixed-frame Gram.

The obvious fixed-frame compression by the existing unequal Hecke flags is
now also closed as a fence.
`endpoint-whiteheads-are-center-chain-hecke-spectators` proves that the
fresh endpoint braid on `(10,11,2)` centralizes the center-chain atom, its
nested quarter/eighth supports, and both Hecke arms; the only possible
index collision dies by the literal coefficient identity `q c_2=0`.
Consequently its two compressed endpoint words have cross-Gram support
exactly the one-eighth flag.  That attractive scalar match does not close
the radical: it is a commuting spectator dressing, and the canonical
regular Hecke model tensored with the regular `S_3` endpoint reservoir keeps
nontrivial coboundary gauges while satisfying the complete compressed
table.  The missing row must be a noncentral odd ordinary occurrence tied
to an individual raw native/Hecke polar, not a fixed flag compression.

All noncentral endpoint coordinate placements are now classified as well.
`endpoint-whitehead-hecke-flag-trichotomy`
shows that an endpoint edge either dresses both flags, ejects the quarter
flag, or preserves the quarter flag while ejecting the eighth.  The last
case occurs for `(8,2;2)` and has the exact proper compression

```text
p_2 What p_2=What p_*,
```

with canonical mass `tau(e)/16`.  This is not the missing positive carrier:
an exact two-dimensional swapped-character representation has `p_2!=0`
but `p_*=0`, so no arbitrary-profile mass floor exists.  On a surviving
`p_*` both fine label bits are already `+1`; the polar retains the entire
uncontrolled endpoint gauge and conjugates one fine flag only to an
equal-rank fine flag.  Thus neither changing endpoint coordinates nor using
the first noncentral proper compression authenticates an unequal native
row.

The fine collision becomes genuinely positive even on the signed-sheet cut.
`endpoint-order-five-actor-has-half-gram` adjoins the actual native head
`M=J_2B_3A_2`.  Its action with the endpoint word `W` on
`<C_3,s,t,s'>~=C_2^4` is `GL_4(F_2)`, so nonzero-character multiplicities
force the raw `W` cross Gram to retain exactly half of
`1_(C_3=-1,s=+1)` in every finite-dimensional representation.  The same
packet has the new odd relation `(WM)^5=1`.  This is an unconditional
proper Gram, not a regular-trace artifact.  More strongly, the literal
vector-and-covector stabilizer of the marked projective summand is
`diag(1,GL_3(F_2))`.  It fixes signed `K_1` pointwise and acts transitively
on the seven nonzero characters of `<s,t,s'>`.  Thus, writing their common
nonzero multiplicity as `m_1` and the zero multiplicity as `m_0`,

```text
rank(p_1)=m_0+7m_1,
rank(p_2)=m_0+3m_1,
rank(p_2 meet Wp_2W)=m_0+m_1.
```

In every finite-dimensional representation the actual signed source obeys

```text
rank(p_2 meet Wp_2W) >= (1/3)rank(p_2) >= (1/7)rank(p_1).
```

This invalidates the standalone swapped-character zero-meet profile once
the full native actor packet is imposed.  The remaining task is narrower:
type this now-positive endpoint polar as the external gauge of the two
actual unequal native selector occurrences.  The meet is not known to
reduce `M`, so the odd order-five relation alone does not perform that
occurrence attachment.

The bound also does not automatically descend from `p_2` to the complete
common Hecke source `Q=e_(L_0,lambda_0)`.  The exact audit
`endpoint-order-five-return-leaves-full-hecke-fine-sign-free` finds the
literal return word which fixes all ten generators of `L_0` pointwise, but
it acts on the two missing fine roots by `t -> ts'`, `s' -> s'`.  Its exact
two-dimensional compressed covariance permits `s'=-1`, whereas the moved
endpoint source requires `s'=+1`.  Thus the return relations alone still
permit `Q(WQW)Q=0`; an additional moving-sheet orbit or a typed native row
must pay that last sign.

The complete moving-sheet packet does not pay it either.
`full-moving-hecke-packet-retains-q-kernel-profile` uses the literal
eight-projective-summand parabolic chart and the `465`-state orbit of
adjacent characters with covector-vector pairing zero.  All ten `L_0`
generators and the actual `W,M,J_1` act on one common finite Hilbert space,
but

```text
rank(Q)=4,                    QWQ=0.
```

Thus the earlier return profile was not an artifact of omitting the moving
relations: even the entire `GL_5` actor does not descend the `p_2` bound to
the full source.  This exact profile does not refute `(APG1)` for some
different authenticated pair of native rectangular transports.  It rules
out specifically the attempt to prove `(APG1)` by using the full-source
endpoint Gram `QWQ`; a new occurrence outside this packet must pay the four
zero-Gram states.

Adding the first native Whitehead strengthens the bare finite actor but
remains one-sided at the `p_2` level.
`native-j1-extension-gives-gl5-but-only-second-whitehead-gram`
identifies the literal five-projective-summand group as `GL_5(F_2)` without
enumerating it.  Its `diag(I_3,GL_2)` signed-source return forces the actual
`J_2` compression to retain at least one third of `p_2` in every profile.
The same subgroup fixes the missing `J_1` support root `r=x_58(a_2)`, and
therefore supplies no corresponding first-row lower bound.  The bare
five-projective-summand calculation does not model the four additional
coefficient roots of the full source `L_0`; the complete adjacent-character
model above does, and retains a zero full-`Q` endpoint Gram.  Hence this is
genuine native second-row progress, not yet the common two-row selector
attachment.

The additional full-source arm closes precisely that first-support gap.
`b2-pairs-full-hecke-first-support` uses the already authenticated
normalizer `B_2=x_84(b_2)` and

```text
[x_58(a_2),B_2]=x_54(q)=C_2,
```

where `C_2=-1` on `Q`.  Hence `B_2Q` exchanges the two spectral signs of
`r=x_58(a_2)` on `Q`, and the actual first native support obeys

```text
rank(Q(1+r)/2)=rank(Q)/2.
```

So the full-source first row is now paid with the sharp universal fraction
`1/2`, even though the same complete packet can have `QWQ=0`.

The second arm supplies the missing common-source refinement.
`b2-b3-pair-full-hecke-four-native-sectors` verifies that
`t=x_69(a_3)` and `B_3=x_95(b_3)` also normalize `Q`, with
`[t,B_3]=C_3` and `C_3=-1` on `Q`.  Since `B_2` commutes with `t`, it
exchanges the two `r` signs separately inside each fixed `t` sector; the
`B_3` flip balances the two total `t` marginals.  Hence all four joint
`(r,t)` sectors have rank `rank(Q)/4`.  In particular the actual `J_1` and
`J_2` compression supports meet on the literal common source

```text
F=Q(1+r)(1+t)/4,                 rank(F)=rank(Q)/4.
```

The live seam is therefore no longer positivity or common-source incidence.
It is to carry the two typed outputs from this literal quarter source onto
one common target with the synchronized reservoir gauge.

There is no longer an independent **central gauge-parity** ambiguity on the
first row.  `endpoint-whitehead-star-braid-synchronizes-native-gauges`
observes that the three literal swaps `J_1,J_2,W` form a star on the `GL_5`
block.  Their pairwise odd Coxeter rows make all three reservoir involutions
unitarily conjugate on any common reducing homogeneous carrier.  In
particular, the simultaneous central change `J_1 -> J_1D`, `u_1 -> u_1D`
which evades `(J_1u_1)^7=1` is detected by `(J_1W)^3=1` unless the same `D`
is carried by `W`, in which case it is one common endpoint gauge.  This is
the desired algebraic gauge synchronization, but it does not supply the
missing carrier: the signed-`K_2` actor normalizer sends `r` only to
`rv^epsilon`, and
`v=+1` on `p_2`.  Hence it preserves the `r`
sign and permits the scoped profile `r=-1`, `q_1=0` on `p_2`.  The full
source `Q` excludes that profile by the `B_2` pairing above.  The remaining
problem is therefore common-target occurrence attachment, not positive
first support or a free central sign.  The coarser fence is sharp already
for the literal `J_1,W` moving table:
an exact three-character `C_2^6 semidirect S_3` model has maximal `W` Gram
on `p_2` and zero `J_1` support.

Passing to an odd-actor-invariant carrier does not lose all of this progress.
`full-packet-cyclic-aggregates-retain-positive-endpoint-gram` joins the five
`C=WM` translates, or the seven `M` translates, of `p_2`.  These carriers
contain the marked signed source, reduce the corresponding odd actor, and
retain Whitehead Gram fractions at least `1/15` and `1/21`.  What remains
noninvariant is the positive common meet on which the Whitehead polar is
defined.  Consequently the odd relation still cannot be telescoped on that
polar subcorner.  The exact cyclic-only lamp model proves that this failure
cannot be repaired from `C^5=1` or `M^7=1` alone; the returning `GL_3`
incidence is exactly what supplies positivity, while a native source-and-
target occurrence is still needed to lock its gauge.

The original signed source and one endpoint-moved source have now also been
compared exactly.  In
`endpoint-whitehead-signed-source-has-only-relative-hecke-overlap` their
signed subgroup intersection is the endpoint-isolating subgroup, of order
`256` at endpoint `2` and `512` at endpoint `4`.  This gives canonical
Hecke overlaps `tau(Q)/32` and `tau(Q)/16`, respectively, but no
arbitrary-profile rank floor: an exact two-character profile realizes the
same intersection table with orthogonal source projections.  Short
normalizer dressings have maximal cross-Gram and no constant actor word
removes the spare endpoint coefficients.  Hence the new finite overlap is
not the missing unconditional MF occurrence; the required next input is
still a proper unequal subrange or an independently positive fixed-frame
row.

The last bounded fixed-source shortcut on the three exceptional detector
classes is now exhausted too.
`exceptional-endpoint-detector-products-stay-at-depth-three` computes their
entire `L_0`-normal product subgroup: it is positive, elementary abelian of
order eight, and all its endpoint incidence is in the third native column.
It therefore supplies no one actor word giving mark-return cells at adjacent
depths on the original `Q`.  Producing an earlier depth necessarily leaves
this subgroup and reintroduces either a moved signed source or the endpoint
Whitehead coboundary.  This fence does not establish the full MF radical;
it removes only the proposed bounded-product bypass.

The larger finite actor audit gives a genuine occurrence without closing
that bypass uniformly.
`positive-signed-actor-two-scale-profile-is-partial-and-gauged` finds that
`184/511` positive nonidentity classes admit adjacent endpoint depths and
exhibits `x_28(1)x_49(1)` with exact depth-two and depth-three mark-return
cells on the fixed signed source.  But `327` classes have no adjacent
profile, including every one of the `31` hard root-free classes, and the
explicit two-cell word splits into independently gauge-dressable commuting
factors.  The full MF radical therefore remains open: this partial
occurrence neither handles an arbitrary paying detector nor produces the
common unequal native range.

The shortest mixed relation tying the explicit two-depth cells has also
been computed.  In
`mixed-whitehead-cell-moves-signed-source`,
the product of matching endpoint and native prefix Whiteheads fixes the
positive actor and conjugates its whole depth-two mark cell to depth three.
But it does not normalize the signed source: the exact intersection has
order `16`, the canonical overlap is only `tau(Q)/512`, and a finite
two-character profile makes the source charts orthogonal.  The remaining
short cross and common-tail words supply only commutation or the inverse
swap.  Thus even this genuine global occurrence relation does not establish
the full MF radical; one still needs a noninverse positive return to the
same signed source or the prescribed unequal native range Gram.

The first nontrivial second-transport loop has now been found and fenced.
`external-normalizer-dressed-cell-has-full-gauged-gram` takes
`H'=Hx_59(1)`, where `x_59(1)` is the unique external signed-normalizer root
centralizing the concrete depth-two cell.  The relative loop is nonidentity
and source-normalizing, but both transports have the same whole moved range
and their cross Gram is the full unitary `x_59(1)Q`.  On the signed carrier
this word retains an arbitrary external multiplicity involution.  Therefore
the second transport does not establish the full MF radical: it introduces
another spectator gauge rather than returning the source or producing the
unequal native selector Gram.

The first literal Hecke contact is also now audited.
`native-t00-collision-first-hecke-attachment-has-gl10-model` computes the
commutator of the paid discrepancy with the actual `B_2` arm and ejects a
full-rank-scale `t_1` coefficient.  The same marked `GL_10(F_2)` chart still
realizes that attachment and the order-seven head exactly.  Consequently a
nonzero native Hecke ejection alone does not imply positive paid mass on the
signed source; the missing statement must explicitly name its source
projection or charge escape from it.

There is also a profile-uniform localization to the native middle-index
packet.  `paid-t00-pauli-menu-hits-whitehead-constant-atom` averages the paid
carrier over the eight literal Pauli-flip conjugates and places one conjugate
on the constant atom preserved by both prefix Whiteheads, with a fixed mass
floor.  Reynolds-averaging that compression over the six native `S_3` words
and then taking a spectral high cut strengthens this in
`paid-t00-reynolds-cut-is-whitehead-reducing`: one member of a fixed
forty-eight-word menu has positive paid compression on a positive subcut
which reduces both actual Whiteheads.  The exact `GL_8` model in
`native-actor-normal-closure-does-not-localize-paid-t00-support` shows why
the Pauli step is essential: conjugation only by `J_1,J_2` and the two
order-seven heads can fix the constant atom pointwise while the discrepancy
is paid entirely off it.  These results remove total avoidance of the
Whitehead packet, but both label actions on that atom are quarter-scale.
Identifying the localized paid word with the unequal quarter/eighth selector
output remains the final occurrence-typing problem.

The localized payment can now be moved through one literal Hecke row without
reviving the false common-cut argument.  In
`paid-cut-has-moving-hecke-source-or-detector`, either a conjugated signed
detector pays at least one half, or the paid Whitehead overlap yields a
positive model-dependent subcut of the conjugated signed source.  Undoing
the paid conjugation and applying either exact Hecke word transports at least
`3tau(P_z)/31744` of support with zero row boundary.  The actual EL20
incompatible-character commutator forces a quantitative exit from at least
one order-seven head on that same source cut, so it must move at the next
stage.  This is a valid first moving-cut occurrence, but it lands in the
common refined Hecke range and does not authenticate either unequal native
selector output.  The remaining transition must either make the detector
branch a presentation payment or carry this cut, with full source/target
Grams and no moving-frame coboundary, into one actual quarter/eighth row.

Taking the polar part of the paid source incidence does not strengthen this
into a typed row.  `paid-polar-bridge-does-not-type-moving-hecke-target`
tracks the precise raw ordinary-word coefficient
`Q_sC_sEu_i s^(-1)R_s` and shows that its polar normalization may have
arbitrary gauge.  Its acute graph model satisfies the strict source branch,
has full positive polar support and exact order-seven heads, but has zero
Gram with both literal Hecke targets while paying the forced exit.  Hence
the remaining transition must authenticate and lower-bound that raw mixed
Gram (or supply an independent fixed-frame bridge); analytic polar
alignment alone cannot close the MF radical.

Combining that moving cut with the new literal sheet factors does not close
the transition.  `moving-signed-source-does-not-localize-paid-sheet-detector`
exhibits an exact signed-character model in which
`K_Q=[A_1,H]` is globally nontrivial and mark-conjugate but acts identically
on all of `Q`, hence on every extracted `R_0`.  The shorter
`[S_57,H]` cube has no source-compression estimate and pays an uncontrolled
`S_57` boundary.  The forced order-seven exit is a lower bound, not the
full source/range Gram typing of an unequal native output.  Thus the
post-PMH bottleneck is precisely `(MSD7)`: an ordinary odd mixed transition
from the moved cut to an actual quarter/eighth target, with the reservoir
factor fixed in the Hecke frame (or an ordinary relator estimate disposing
of the detector branch).

A seed-free computability shortcut has also been excluded.  Operator-MF does
not make the complement of the word problem recursively enumerable: a single
finite matrix tuple with small relator defect is not a sound nontriviality
certificate because the necessary defect threshold depends on an unknown
filling of the tested word.  This is not merely a logical caution;
`finitely-presented-amenable-undecidable-word-problem` supplies a fixed
finitely presented solvable (hence operator-MF) counterexample with
undecidable word problem.
