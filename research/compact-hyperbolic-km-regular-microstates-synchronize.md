---
rg: 2
id: compact-hyperbolic-km-regular-microstates-synchronize
kind: claim
title: Regular microstates of one compact-hyperbolic Kac-Moody lattice synchronize globally
distinct_from:
  finite-subgroup-near-regular-has-large-regular-core: that extracts a regular core separately on every finite subgroup; this must align all overlap gauges and kill every Curtis-Tits cycle holonomy.
  three-chart-loop-retains-free-multiplicity-holonomy: that exhibits the abstract free cycle gauge; this asks the native Kac-Moody two-cell relations to control it on the canonical regular branch.
  finite-face-flatness-stops-at-fundamental-group-holonomy: that classifies bare face-flat multiplicity connections and shows curvature repair is presentation stability; this can succeed only through additional native label--multiplicity coupling.
  fixed-finite-label-km-holonomy-is-scalar-or-gapped: that rules out every fixed projective-label Schur-product twist; this still permits growing or genuinely label--multiplicity-entangled overlap maps.
  finite-multipath-average-coercivity-has-exact-julia-absorber: that proves finite additive paths coerce their pairwise Gram energy only after complementary leakage is controlled; this must construct that carrier control from native Kac--Moody relations.
  triangle-kernel-relators-charge-authenticated-corner-leakage: that proves the native kernel words pay all complementary leakage on a positive carrier; this must still identify one compressed word with the desired finite-label multipath block.
  km-triangle-local-bimodules-have-finite-nonflat-models: that gives exact regular charts and pairwise overlap intertwiners with a nontrivial native kernel cycle; this must use the kernel relator itself to close the common carrier.
  reynolds-defect-cut-gives-regular-relator-corner: that constructs a large regular-overlap carrier and polar two-path corner for one kernel word; the summed-Reynolds claim below supplies its finite-family upgrade.
  summed-reynolds-cut-synchronizes-kernel-corners: that gives one overlap-subgroup regular carrier and mutually close polar corrections for the whole kernel basis; this must transport that carrier through the rank-two vertex charts.
  summed-reynolds-carrier-transports-only-tautologically: that transports the high-density projection and its polar corrections through every chart by replacing the projection with the full carrier, but shows that the resulting paths are only I and the original kernel word; this must compare the polar path with the independently exactified P_13 coefficient.
  one-state-protected-coefficient-leaves-relative-gh-gauge: that proves a full-trace unitary coefficient pins the relative multiplicity gauge exactly, but a single state-dependent protected coefficient leaves an exact amplified counterpacket even for faithful states; this must obtain operator-level trace control for the Reynolds polar coefficient.
  common-gh-isometry-selects-the-two-overlap-cross-coefficient: that derives this operator-level cross coefficient by averaging the same normalized-HS Gowers--Hatami isometry over P_1 and P_3; this must turn two near coincident subgroup polar supports into one exactly simultaneous invariant source.
  relative-three-chart-correction-is-km-regular-stability: that proves exact relative correction of the three finite vertex charts is equivalent to this terminal global synchronization target, not a smaller semisimple cleanup.
  character-rigidity-equals-hyperfinite-hs-stability: that treats the hyperfinite character branch; this asks for correction of the nonamenable canonical regular branch.
  bounded-degree-holonomy-collapses-for-map-groups: that uniformly kills every holonomy algebra of bounded irreducible degree, regardless of the number or multiplicities of its blocks; this must exclude positive-density blocks whose degree tends to infinity.
  pt-rigidity-allows-nontight-regular-tails: that gives exact projective-plane representations of a higher-rank property-T character-rigid lattice whose characters tend to regular, whose adjoint gaps are uniform, and whose coefficient degree distributions are maximally non-tight; this proves those abstract inputs cannot remove the surviving tail.
  finitely-generated-map-lef-has-perfect-regular-chart-microstates: that gives a finitely generated minimally almost periodic LEF group whose finite-subgroup charts are eventually exactly regular and perfectly coherent on every fixed window, but whose canonical microstates remain a square-root-of-two away from every genuine finite-dimensional representation; this must use the fixed native Kac--Moody relators to prevent the window from escaping.
artifacts:
  - research/artifacts/regular-core-holonomy-universal-attack-integration-2026-08-22.md
  - research/artifacts/high-cascade-holonomy-audit-2026-08-23.md
---

**OPEN.**  Fix an infinite finitely presented simple Kazhdan
Caprace--Remy compact-hyperbolic Kac--Moody lattice `Gamma`.  Every canonical
regular-trace normalized-HS microstate sequence for `Gamma` is, after an
`o(d)` flexible dimension change, `o(1)`-close on a fixed generating set to
a genuine finite-dimensional representation of `Gamma`.

Finite-subgroup exactification already makes every local chart a direct sum
of regular representations up to `o(d)`.  The new content is global: choose
overlap identifications, gauge away a spanning tree, and prove that the
remaining multiplicity-commutant holonomies around the Curtis--Tits/chamber
two-cells are `o(1)`-gauge-equivalent to an exact global representation.
Neither property `(T)`, IRS rigidity, nor local finite-group stability proves
this statement.

## Perfect local synchronization still needs a fixed presentation

The finite-subgroup regular-core theorem cannot be strengthened into the
answer by making its local choices canonical.  The established countermodel
`finitely-generated-map-lef-has-perfect-regular-chart-microstates` takes a
finitely generated infinite simple amenable LEF group `H`.  Its LEF windows,
placed in finite left regular representations, have all of the following
properties simultaneously: every fixed finite subgroup is eventually an
exact full regular multiple; every finite collection of subgroup charts and
overlaps is the restriction of one common finite action; and the normalized
characters converge to the canonical regular trace.  Yet `H` has no
nontrivial finite-dimensional representations, and every nonidentity
microstate matrix stays at normalized-HS distance `sqrt(2)` from the only
possible exact correction.

Thus even *perfect* multiplicity-commutant synchronization on every fixed
finite window does not compactify for a finitely generated minimally almost
periodic group.  The example is not finitely presented and has no property
`(T)`; that is exactly its diagnostic value.  A Kac--Moody proof must turn the
fixed finite list of native kernel relations into a uniform estimate on the
growing regular multiplicity coordinates.  Further refinement of the local
regular core, without such a relation-dependent estimate, cannot close this
claim.

## Bounded-degree holonomy is closed

There is now one further uniform reduction.
`bounded-degree-holonomy-collapses-for-map-groups` proves that an
asymptotically flat holonomy tuple for a group with no nontrivial
finite-dimensional representations collapses to the identity whenever its
finite-dimensional coefficient algebras have a fixed subhomogeneity bound.
The estimate is uniform in the number and multiplicities of the blocks: a
weighted Markov argument discards the small mass of blocks with non-small
relator defect, while compactness in the finitely many dimensions below the
bound collapses every remaining block.

The same proof treats every tight trace-weighted mixture of growing degrees.
Consequently an enemy here must have a quantitatively non-tight degree
distribution: a positive mass escapes beyond every fixed noncommutative
block degree.  Repeated bounded labels or sectors cannot evade
synchronization merely by increasing their multiplicity, nor can a
vanishing high-degree tail carry the marked separation.  The unresolved
relation-dependent common-core theorem must therefore act on a diffuse
large-degree multiplicity regime itself.

The escape cannot be removed by combining property `(T)`, character
rigidity, canonical trace, and asymptotic adjoint spectral gap abstractly.
`pt-rigidity-allows-nontight-regular-tails`
constructs exact irreducible projective-plane representations of
`SL_3(Z)` with all four properties and with degree distribution
`delta_(p^2+p)`.  Thus these inputs are compatible with maximal degree
escape.  The simple Kac--Moody lattice additionally has no nontrivial exact
finite-dimensional representations, but promoting that qualitative fact to
exclusion of high-degree approximate regular tuples is precisely the
regular-branch stability assertion in this claim.

## Curtis--Tits face-gap audit

The established classification
`finite-face-flatness-stops-at-fundamental-group-holonomy` rules out a
strictly smaller lemma based only on multiplicity edge gauges and individual
Curtis--Tits face curvature on a common untwisted reservoir.  After a
spanning-tree gauge, the surviving edge unitaries are presentation generators
and the face curvatures are their relator defects.  Repairing them to a flat
connection is therefore the normalized-HS stability problem for the resulting
fundamental-group presentation, while killing the flat connection is its
trivial-representation branch.

For the simple lattice fixed here, exact finite-dimensional global holonomy
is indeed trivial.  That removes exact nontrivial flat countermodels, but it
does not supply a quantitative repair theorem: excluding asymptotically flat
nontrivial matrix holonomy is exactly the regular-branch synchronization
asserted above.  Local spherical residues or isolated Curtis--Tits triangles
can gauge contractible data only.  A genuine decomposition must add a named
relation which couples a regular finite-subgroup label block to its
multiplicity unitary; another bare cocycle or face-gap estimate would merely
rename this terminal target.

## Fixed finite-label twists are exhausted

The first apparent native coupling is to let each overlap transporter have
Schur form `C_s tensor Q_s`, where `C_s` belongs to a fixed finite projective
intertwiner groupoid and `Q_s` acts on the growing regular multiplicity.
`fixed-finite-label-km-holonomy-is-scalar-or-gapped` gives an exact dichotomy.
If one finite label relator is nonscalar, its spectral spread gives a fixed
normalized-HS defect which no `Q_s` can cancel.  If every label relator is
scalar, the `C_s` define a finite-dimensional projective representation of
the simple lattice, hence are themselves projectively scalar and carry no
sector or adjoint-label information.

Thus finite projective cocycles, sector permutations, and monomial finite
bimodule paths do not provide the missing smaller lemma.  The narrow surviving
native target is a **non-Schur overlap coefficient**: a same-block coherent
sum of at least two finite label paths, or an intertwiner which genuinely
entangles label and multiplicity coordinates.  Its construction must be
forced by a named Curtis--Tits relation; merely allowing its finite label
alphabet to grow with the microstate would abandon fixed-scale extraction.

## Additive multipath interface

Allowing a coherent same-block sum does leave the projective-groupoid
absorber, but addition alone is still insufficient.  The established identity
`finite-multipath-average-coercivity-has-exact-julia-absorber` applies to any
finite family of equal-source/equal-range corner unitaries, even when the
paths entangle label and multiplicity coordinates.  Their average loses
corner-isometry mass by exactly

```text
1/(2m^2) sum_(i,j)||A_i-A_j||_2^2.
```

If a native global unitary has this average as a nearly invariant corner,
that identity is the desired finite coercivity lemma and forces path
consensus with constants `2m^2` and `4m^2`.  Without invariance, the Julia
dilation puts the average in the corner of an exact finite-dimensional
unitary and sends precisely the same Gram energy into the complement.

The first surviving construction target is therefore exact: identify one
Curtis--Tits multipath block on a positive regular carrier and prove either
small complementary leakage or an independent relator-energy charge for that
leakage.  More paths and non-Schur coordinate entanglement do not remove this
carrier obligation.

## Native triangle relators do pay leakage

The triangle presentation has a precise tree-first form:
`G_0=P_12*_(P_2)P_23` is virtually free, and the remaining two-cells are a
free basis `n_a=1` of
`N=ker(P_1*_(P_0)P_3 ->> P_13)`.  These relations are analytically sufficient
once the correct corner is named.  By
`triangle-kernel-relators-charge-authenticated-corner-leakage`, for every
projection `q` of trace `beta`,

```text
tau_q(q pi(n_a)^*(1-q)pi(n_a)q)
 <=beta^(-1)||pi(n_a)-I||_2^2.
```

Combining this with the multipath Gram identity gives `(TKL3)`, with exact
constants `2m^2/beta` and `4m^2`.  Hence a correctly compiled kernel-word
compression has no Julia escape.  The narrowed native problem is algebraic:
construct one common regular-core projection of uniform density and expand
`q pi(n_a)q` as, or approximate it by, the desired coherent finite-label
paths.  A further abstract leakage or face-gap lemma would duplicate the
established estimate.

## Local regular bimodules do not compile the common corner

The remaining coefficient step cannot be derived from the local finite
subgroup tables and pairwise overlap maps alone.
`km-triangle-local-bimodules-have-finite-nonflat-models`
uses residual finiteness of the virtually free tree side `G_0` to separate
any chosen `1!=n_a in N` in a finite quotient.  Its quotient-regular
representation is a regular multiple on `P_12` and `P_23`.  After a fixed
common amplification, an independent regular `P_13` chart has exactly the
same restriction multiplicities on `P_1` and `P_3`, so both overlap
intertwiners and all finite group-algebra matrix units match exactly.  The
returned `n_a` holonomy nevertheless remains nontrivial on the tree side and
is identity on the `P_13` side.

Therefore the desired positive carrier and multipath identity must consume
the native relation `n_a=1` during their construction; they cannot be
selected first from local regular cores and then closed formally.  This does
not weaken `(TKL3)`: once such a relation-dependent common carrier is built,
the kernel defect pays its leakage.  It rules out a local-bimodule-only
compiler and isolates the unresolved step as **relation-dependent common-core
extraction**.

## One relation-dependent carrier is available

There is a positive construction beyond the local counterpacket.
For one kernel word `Y=pi(n_a)` and one fixed finite overlap subgroup `H`,
`reynolds-defect-cut-gives-regular-relator-corner` averages
`(Y-I)^*(Y-I)` over `H` and spectrally cuts the result.  The projection `q`
commutes with `H`; for `d=||Y-I||_2<1`, it satisfies

```text
tr(q)>=1-d,
||qYq-(q+B)/2||_(2,q)<=sqrt(|H|d),
```

where `B` is a genuine unitary in `qM_Dq`.  If the ambient `H` chart is
regular, `q` contains a regular summand of relative dimension at least
`1-|H|d`.  Thus one native relation does produce both a uniformly positive
regular carrier and a coherent two-path corner, with a dimension-free
modulus.

The finite-family issue is now settled by
`summed-reynolds-cut-synchronizes-kernel-corners`: sum the Reynolds defect
Laplacians before taking the spectral cut.  If
`E=sum_a||pi(n_a)-I||_2^2`, one common `H`-invariant projection satisfies

```text
tr(q)>=1-sqrt(E),
||q pi(n_a)q-K_a||_(2,q)<=sqrt(|H|)E^(1/4),
||B_a-B_b||_(2,q)<=4sqrt(|H|)E^(1/4).
```

In a regular `H` chart it retains a regular summand of relative dimension at
least `1-|H|sqrt(E)`.

The projection-transport problem is now closed.
`summed-reynolds-carrier-transports-only-tautologically` observes that the
same trace estimate already gives

```text
||q-I||_2<=E^(1/4),
||[U,q]||_2<=sqrt(2)E^(1/4)       for every ambient unitary U.
```

Thus replacing `q` by the identity transports the carrier through all three
rank-two charts with no loss of regular mass.  Every corner polar correction
also extends by identity to a global unitary `O_H(E^(1/4))` from `I`.  This
does not solve the coefficient problem: the construction then names only the
tautological paths `I` and `pi(n_a)`.  Its polar completion is not a group
word and is not tied to the independently exactified `P_13` chart.  The
precise remaining bridge is a relative finite-group exactification which
compares that corrected chart's two overlap-path coefficients to the
Reynolds polar path on positive regular mass.  No further carrier-invariance
estimate is needed.

There is now a sharp gauge criterion for that bridge.
`one-state-protected-coefficient-leaves-relative-gh-gauge` proves that the
full ambient unitary extension `tilde B_a` is enough: if the two overlap
gauges are `Q_1,Q_2`, then

```text
||Q_2 tilde B_a Q_1^*-tilde B_a||_2
 =||Q_2-tilde B_a Q_1 tilde B_a^*||_2.
```

Thus one normalized-HS operator coefficient fixes the relative gauge with no
loss.  But Lin-style one-state protection is strictly weaker.  On an
amplified regular packet a faithful density can put total weight `O(m^(-2))`
on a trace-`1-o(1)` complement; flipping that complement has vanishing state
error and normalized-HS distance tending to two, while preserving every
packet intertwining equation.  Lin's exact opposite-algebra preservation
does not rescue this because the Reynolds polar coefficient commutes only
with `P_0`, not with the whole `P_13` packet.

For the normalized-HS Gowers--Hatami exactification actually used here, the
identity-gauge audit is positive.
`common-gh-isometry-selects-the-two-overlap-cross-coefficient` averages the
**same** comparison isometry over `P_1` and `P_3`.  The two polar
intertwiners have a cross coefficient `I+o_2(1)` on a `1-o(1)` source, hence
it is automatically close to every `tilde B_a=I+o_2(1)`.  A common target
gauge cancels from this cross coefficient, so arbitrary-gauge examples do
not refute existence of this coherent choice.  The approximate coefficient
selection is therefore closed.

The exact residual is support invariance.  Each polar source is invariant
under its own overlap subgroup, but their large intersection need not be
invariant under either; moreover a near-identity mismatch can have full rank
and no literal fixed subspace.  Turning these selected near-coincident maps
into one exact intertwiner for both `P_1` and `P_3`, while making the analogous
choice around the other two edges, is the nonlinear cochain correction in
`relative-three-chart-correction-is-km-regular-stability`.  Quarantining
`o(d)` dimensions does not make that full-rank near mismatch vanish.

## The kernel basis already builds the missing finite rank-two chart

There is also a direct quotient-level gain.  Choose a finite section
`sigma:P_13->E=P_1*_(P_0)P_3` which is the identity on `P_1 union P_3`.
Every multiplication cocycle

```text
sigma(g)sigma(h)sigma(gh)^(-1)
```

is a fixed word in the free kernel basis.  Therefore
`kernel-section-builds-relative-p13-chart` turns a tree-side representation
whose kernel-basis defect is `d` into an all-pairs approximate `P_13` chart
with defect at most `L_sigma d`.  Before finite-group exactification this
chart agrees exactly with the existing `P_1` and `P_3` restrictions; on the
regular branch its exactification has a `1-o(1)` regular core.

This eliminates the need to guess or independently align a `P_13` chart.
The frontier is now the relative simultaneous correction of the three
finite rank-two charts: after exactifying `P_13`, perturb `P_12` and `P_23`
on their large regular cores so that the `P_1`, `P_2`, and `P_3` overlap
restrictions agree exactly.  That is a finite semisimple synchronization
formulation, rather than an unbounded kernel-word or carrier-density problem.

It is not, however, a smaller final cleanup.
`relative-three-chart-correction-is-km-regular-stability` proves that exact
overlap agreement is, by the triangle colimit universal property, precisely
a genuine finite-dimensional representation of `Gamma`.  Conversely every
global correction restricts to such a compatible triple.  Since `Gamma` is
infinite simple, the exact compatible locus contains no triple retaining a
nonzero regular vertex summand.  Thus rounding near-identity multiplicity
holonomy to that locus is quantitatively the terminal regular-branch
stability theorem itself.

Property `(T)` supplies one sharp conditional endpoint, but it cannot cross
this last gap. `km-kazhdan-holonomy-rounding-starts-after-projective-flatness`
shows that if the free presentation matrices already send every
Curtis--Tits relator to a scalar, their adjoint action is an exact
representation of `Gamma`. The Kazhdan gap then polar-rounds any holonomy
`W` to a unitary in the global commutant with the dimension-free estimate

```text
dist_2(W,U(rho(F)'))
 <=sqrt(2) kappa^(-1) max_(s in S)||[W,rho(s)]||_2.
```

This is the highest-cascade qualitative commutant synchronization available
from property `(T)`. For the simple lattice, however, exact scalar relators
define a finite-dimensional projective representation of `Gamma`, which is
trivial by simplicity and Malcev residual finiteness; all vertex images are
then scalar and no regular finite-subgroup core survives. In a microstate the
relators are only near the identity, so the adjoint maps are only an
approximate `Gamma`-representation and the Kazhdan inequality has no object
to act on. Promoting them to an exact adjoint action while retaining regular
mass is projective normalized-HS stability itself. Thus building geometry,
local regular cores, and property `(T)` do not yield an intermediate
holonomy-collapse lemma unless an additional finite-matrix mechanism first
scalarizes the native face relators.

The obvious finite-matrix scalarization invariants do not provide that
mechanism. `km-su-reservoir-defeats-discrete-scalarization`
inserts a balanced `W_(m,t) in SU(m)` into one exact regular-parahoric
multiplicity chord. All local regular tables, overlap intertwiners,
divisibilities, determinants, and finite Schur-multiplier data remain exact,
while the holonomy is nonscalar and

```text
||W_(m,t)-I||_2^2=2-2cos(t)->0.
```

At the same time `rank(W_(m,t)-I)=m`; a distinct-phase variant has no scalar
reducing subspace of dimension above one. Thus determinant correction sees
nothing, and rank/spectral quarantine can lose essentially all regular mass
at arbitrarily small normalized-HS defect. This does not refute a genuinely
analytic projective-stability theorem, but it proves that such a theorem
must couple the growing multiplicity gauge across native relations rather
than read a determinant, bounded Schur class, divisibility, or defect rank.
