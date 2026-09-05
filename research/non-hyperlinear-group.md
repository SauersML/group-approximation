---
rg: 2
id: non-hyperlinear-group
kind: claim
title: Exhibit an explicit non-hyperlinear group
root: true
goal: true
artifacts:
  - research/artifacts/parallel-arithmetic-holonomy-2026-09-04.md
  - research/artifacts/parallel-group-word-2026-09-04.md
  - research/artifacts/parallel-ui-iteration-audit-2026-09-04.md
  - research/artifacts/moving-schreier-correction-audit-2026-09-04.md
  - research/artifacts/unitary-expander-nonhyperlinearity-audit-2026-09-04.md
  - research/artifacts/nonhyperlinear-literature-delta-2026-08-30.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
  - research/artifacts/compressed-representation-quadratic-curvature-2026-09-05.md
  - research/artifacts/quadratic-curvature-flexible-dilation-2026-09-05.md
  - research/artifacts/opposite-root-character-interface-2026-09-05.md
  - research/artifacts/two-depth-leavitt-overlap-rank-audit-2026-09-05.md
  - research/artifacts/rectangular-seed-quotient-alignment-2026-09-05.md
  - research/artifacts/universal-dimension-schreier-host-2026-09-05.md
  - research/artifacts/low-energy-schreier-frame-construction-2026-09-05.md
  - research/artifacts/second-moment-schreier-positive-corner-2026-09-05.md
  - research/artifacts/positive-canonical-corners-bootstrap-stability-2026-09-05.md
  - research/artifacts/soft-schreier-mass-positive-corner-2026-09-05.md
---

The primary target of the program (AGENDA.md header): an explicit group that
is not hyperlinear, i.e. admits no asymptotic embedding into unitary matrices
with the normalized Hilbert-Schmidt metric.

The September 5 audits leave this target open. Hilbert `H^2` vanishing
now gives uniform fixed-tolerance correction concentrating arbitrary
normalized-HS curvature on supports of quadratic relative rank, but
does not make those subspaces invariant. Compressed irreducibles force
some exact corrections to restore every deleted dimension. A small exact
seed plus regular tails cannot construct the needed dilation: almost
unitary Kazhdan corners must overlap almost entirely with its genuine
finite-dimensional representation sector. The older Ulam route now
explicitly requires a uniform all-pairs operator bound; pointwise
operator-ultraproduct lifting did not supply that bound.
On the group-word route, one character-placement anchor and an
authenticated expanding action on a finite root table control its
normalizer uniformly in matrix multiplicity. The actor covariance and
placement hypotheses, and the eventual finite-matrix obstruction, still
need to follow from the candidate group's relations. Neither result is
an existence proof.

The literal opposite-root audit sharpens the latter boundary. At one
prefix depth r, the native arms and opposite mark root generate exactly
`SL_(2^r+2)(F_p)`; weighted degree-zero packets still have finite marked
models. Combining depths one and two with the same opposite root instead
generates the full `EL_3(L_2(F_p))`. The mixed-depth relations therefore
recover the whole elementary Leavitt problem rather than a larger finite
packet; no matrix obstruction for that full group has been proved here.

The depth calculation now extends to every pair `r<s`. Prefix expansion
identifies its generated subgroup with
`EL_(2^r+2)(L_(1,2^(s-r))(F_p))`. Every adjacent pair generates the full
binary group; a larger gap gives a proper subgroup. Nevertheless each
such subgroup contains an embedded copy of the full binary group, using
the explicit binary corner in the larger-branching Leavitt algebra.
Thus all depth pairs have exactly the same hyperlinearity status. The
reverse embedding need not identify the designated marks, so this does
not give a marked collapse estimate.

The two finite depth groups intersect in exactly `SL_2(F_p) x SL_2(F_p)`.
Their regular representations can be glued over that intersection while
keeping the mark at squared HS distance two. Thus compatible restrictions
and branching multiplicities alone cannot force collapse. The overlap audit
exhibits an explicit length-eight mixed relation missing from the abstract
amalgam; a successful estimate must use relations beyond that overlap.

On the arithmetic side, the moving-Schreier correction theorem now accepts
rectangular frames from a smaller exact subgroup representation. Stacking
the frame and normalizing it once gives error `beta+2sqrt(zeta)`, with no
index loss, where zeta is its normalized trace-norm Gram error. Finite-index
induction can therefore supply the required finite-dimensional sector.
Constructing the genuine seed representation and small frame/edge errors
from arbitrary approximate representations remains open.

The seed choice now has a quantitative test. For an exact input rho and
induced candidate Pi, let R be their maximal common representation
dimension. Every rectangular frame obeys
`R/d>=1-zeta-beta^2/kappa^2`, with an explicit perturbative extension.
For the regular `SL_5(F_p)` input, every seed at a coprime congruence level
must have dimension `(1-o(1))d` if its errors vanish. At the matching
kernel Gamma(p), a one-dimensional seed and coordinate rows give zero
errors. Thus the construction must find the quotient content of the
approximate input; merely increasing the subgroup index cannot do it.

There is now a positive way to choose that host universally for exact
inputs. Every unitary `SL_5(Z)` representation of dimension at most D
factors through level `q_D=lcm(1,...,floor(D^(1/3)))`. Three independent
Heisenberg pairs bound the order of each root eigenvalue; the precise
Bass--Milnor--Serre normal-generation theorem supplies the congruence
kernel. The resulting regular quotient host admits exact frames with
trivial seeds, whose optimal dimension is sublinear along every exact
regular-character sequence. No constituents need to be discarded.
Consequently arbitrary seed holonomy is unnecessary once the exact
comparison exists. The remaining operation is constructing the frame
from an approximate tuple, not guessing a congruence level.

The new spectral construction makes that remaining operation precise.
For a canonical approximate SL5 tuple, take the full low-energy space
of maps into a finite regular quotient host and normalize its source
Gram matrix H to trace one. Its target covariance is automatically
sublinear whenever the space has positive relative dimension. A bounded
second moment `tr(H^2)<=M` then produces a correctable canonical corner
occupying at least `1/(16M)` of the input. The weighted leakage estimate
allows H to have unbounded operator norm. If every canonical sequence
admits such spectral data on a subsequence, maximal recoverable mass
promotes positive-corner correction to full correction; constant-one
ucp untensoring then gives flexible HS stability for all SL5 tuples.
The existing thin co-dense HNN route would give nonhyperlinear existence.
The second-moment hypothesis can now be replaced by the weaker positive
soft mass `tr[H(H+I)^(-1)]>=c>0`. A spectral coarea estimate extracts a
canonical correctable corner of fraction at least c/2 from the bounded
soft polar frame, with an explicit vanishing correction bound. Arbitrary
canonical sequences are not yet known to admit quotient hosts and
cutoffs tending to zero with that positive mass. The spectral theorem
and bootstrap therefore leave this root open.

The organizing mechanism is (T)-compression: `Γ ≤ G` with a compressor `t`
(`tΓt⁻¹ ⪇ Γ`). In every category with a conjugation-invariant strictly
monotone size the compression collapses (invariant-size-collapse); the `II₁` branch survives
because the trace is refinement-blind, and that failure is sharp (trace-blindness-sharpness).
The obstruction, if there is one, can only be stability.

## Existence compression and literature boundary (2026-08-30)

`nonhyperlinear-existence-is-two-generator-simple` proves that a
nonhyperlinear countable group exists if and only if a two-generator
nonabelian simple nonhyperlinear group exists.  In that simple envelope one
nontrivial word is forced to collapse by a finite relator window at every
normalized-HS scale.  The reduction uses locality, subgroup heredity,
Schupp's simple-envelope theorem, and ultraproduct compactness.  It is
non-effective and supplies no explicit presentation, so it sharpens the
search space without establishing this root.

The primary-source delta through 2026-08-30 is recorded in
`research/artifacts/nonhyperlinear-literature-delta-2026-08-30.md`.  No
unconditional discrete-group witness was found.  The closest unincorporated
papers instead reinforce three boundaries: arbitrary non-CE traces can live
on residually finite groups; coordinate recognition for an entire
normalized-HS reduced product does not identify embedded relative
commutants; and recent quantum-group stability theorems do not supply the
nonamenable discrete HS stability needed by the arithmetic candidates.

## Arithmetic exact face closed at large primes (2026-08-25)

The top frontier hole (`projective-trace-square-transfer-for-sl3-pair`) and
the collapse claims now have an explicit refutation gate: Connes
embeddability of the homogeneous-quotient crossed product
`L^infinity(SL_3(Q_2)/Lambda') rtimes SL_3(Z[1/2])`
(`homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`), a much
more concrete enemy than the coset wreath because every compact-subgroup
piece acts profinitely.  On the affirmative side the Lambda-exact face of
`(RC3)` is now confined: coprime levels were already closed, and
`lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible` proves
`b_p (1 - nu_0) <= D epsilon^2/kappa_0^2`, `b_p=min(c_p,1/3)`,
(Atkin--Lehner-type twist `J h^D`,
one orthogonal Kazhdan projection, Clifford count over `sl_3(F_p)`), so
p-divisible levels are invisible unless the tower is deeper than
`1/epsilon^2`.  The
surviving exact-face enemy was the ultra-deep tower; the other survivor is the
outlier sector (`sl3-z-weakly-ucp-stable`).

Later the same day the ultra-deep tower fell too, at large primes:
`p-divisible-lambda-exact-mass-vanishes-at-large-primes` tracks each
constituent of the restriction to `C_0 = SL_3(Z) cap h^-1 SL_3(Z) h` by its
(upper, lower) simple-root depths, the twist by `J h` acts as
`(beta, gamma) |-> (gamma - 1, beta + 1)` and so moves every diagonal type
off the diagonal.  Clifford balancing over `sl_3(F_p)` puts at least
`2 c_p - 1` of every level at least two on the diagonal, while three
conjugate transvection subgroups give the separate level-one bound `1/3`.
Thus, for `a_p=min(4c_p-3,1/3)`,
`a_p(1-nu_0) <= epsilon^2/kappa_0^2` with no depth dependence, and for
`p >= 11` the `p`-divisible `Lambda`-exact sector is empty.  With the
coprime closure (`odd-congruence-lambda-exact-sector-collapses`, made robust
by `coprime-sector-collapse-is-robust-to-small-p-admixture`), the whole
`Lambda`-exact face of the collapse at `p >= 11` is closed, and
`sl3-large-prime-collapse-from-weak-ucp-stability` reduces the collapse --
hence, through `non-hyperlinear-from-sl3-large-prime-collapse`, this goal --
to the single hypothesis `sl3-z-weakly-ucp-stable`.  `cairn impact` confirms
that establishing that hypothesis flips this goal to ESTABLISHED along two
independent edges (the earlier thin-subgroup edge consumes stability of the
host, this one stability of the subgroup through the established
exactification).  The affirmative program is therefore exactly: weak
ucp-stability of `SL_3(Z)` on regular-type hyperlinear approximations.

The homogeneous-quotient enemy now pins this residue down without a hidden
flat-tower alternative.  By
`homogeneous-quotient-ce-forces-sl3-outlier-at-large-primes`, if its crossed
product were Connes embeddable at `p >= 11`, every matrix realization would
restrict to a **flexible lattice outlier**: the cell partition forces a fixed
positive amount of `p`-adic mass, while the depth-free theorem forces that
mass to vanish.  The contradiction is stable under the `o(d)` padding allowed
by weak ucp-stability.  Hence the crossed product is CE only if the remaining
stability statement is false.

The first correction-free spectral localization is also exact.  The theorem
`tempered-selected-conjugation-vector-obeys-rcc` proves a dimension-free RCC
estimate whenever the cyclic conjugation module generated by the selected
stable-letter witness is weakly contained in the discrete regular
representation of the ambient arithmetic group.  Thus any surviving outlier
leak must be non-tempered.  This cannot be strengthened to temperedness of
the whole adjoint complement: `canonical-congruence-adjoint-complement-is-not-tempered`
constructs non-tempered finite-quotient Koopman sectors even in exact regular
congruence models.  Profinite density prevents those particular sectors from
containing the selected lattice-fixed leak, so the live target is precisely
selected-vector non-temperedness, not global spectral regularity.

In rank one the same twist is
the Atkin--Lehner involution and single vertex-orbit levels are maximally
asymmetric (`atkin-lehner-twist-of-vertex-orbit-representation-is-disjoint`,
TV `= 2 - 2p^-k`, verified numerically).  Synthesis:
`research/artifacts/exact-face-state-2026-08-25.md`.

## Exact JNVWY support reflection closes the unchanged affine-lowering arm (2026-08-25)

Perfect line--point consistency gives exact global low-degree proof atoms,
and the literal equality and padding clause families of JNVWY's
`PaddedSuccinctDecider` force the first two proof tables to be Boolean at
every Boolean-cube point.  Thus Boolean decoding is restriction and is
odd-additive on the accepted perfect-atom domain, despite being nonadditive
on arbitrary legal low-degree tables.  Consequently perfect answer reduction
reflects affine safety backward.  Exact oracle-marginal reflection then
returns it through oracularization, while the Pauli-introspection theorem
forces every sampler seed and exhibits a rejected odd xor.  Therefore
`jnvwy-active-output-has-no-affine-safe-perfect-model`: every perfect model
of an active unchanged compression output is affine-unsafe, including exotic
models not generated by the honest completeness strategy.

This removes the last strategy-choice ambiguity in that arm but decides it
on the negative side.  The conditional finite affine-profile/LCS compiler
cannot consume the literal JNVWY active-round output.  A successful game-to-
solution-group route must change the recursive sampler/proof interface or
bypass affine support entirely; noncanonical PCP proofs are no longer a live
escape.

## Positive-density finite-memory frontier (2026-08-24)

The strongest currently isolated matrix-only endpoint is
`culf-mastel-positive-density-power-return`.  Cairn already proves both the
coherent-dilation capacity theorem and its sharper scalar form
`positive-density-hs-power-overlaps-force-finite-depth`.  For a projection
of canonical density `alpha>0`, a unitary word `u`, and a strict
finite-matrix acceptance constant `rho<1`, finitely many bounds

```text
||q u^(kL) q||_2^2 <= (alpha+o(1))rho^(2kL)+o(1)
```

force

```text
(N+1)alpha <= 1+2rho^(2L)/(1-rho^(2L)).
```

Fixed large `L` and then fixed `N>1/alpha` contradict this inequality.  The
remaining theorem is therefore semantic compilation, not a new matrix
inequality: `canonical-positive-density-hs-power-overlap-return` must turn
the Culf--Mastel finite-matrix game gap into those group-word overlaps on one
authenticated positive-density head while preserving a perfect infinite
tracial representation.

There is now a strictly weaker static sibling.  Apply the already established
`marked-copy-collision-forces-overlap-mass` theorem to arbitrary word
translates `v_iqv_i^*`.  If every relative corner has squared normalized-HS
norm at most `alpha epsilon`, its lower and upper overlap bounds give

```text
M alpha <= 1+(M-1)epsilon
```

Thus `canonical-positive-density-pairwise-game-overlap-packing` would also
close the root, without any no-return tail.  Its exact remaining issue is
the one-edge theorem
`canonical-positive-density-amplified-acceptance-corner-actuator`.  Attaching
that actuator to the actual ratios `v_i^*v_j` makes finite cycle consistency
automatic; the load-bearing step is amplifying the selected acceptance
corner without diluting its canonical trace and without imposing a global
block-encoder equality.

The arithmetic `S_9` packet lane is now closed rather than merely calibrated.
Canonical trace does make its marked displacement linear-rank and its internal
`GL(3,2)<AGL(3,2)` Reynolds gap have adjoint density `1/192`, but the inner
packet action leaves a full source representation in the multiplicity
commutant.  `arithmetic-star-packet-is-sofic` globalizes that gauge: diagonal
conjugacy embeds the twisted Bass--Serre packet kernel into finite clique
fibers over `E/ker(theta)`, and Cairn's exact telescope-orbit plus cyclic-stack
models make the resulting graph action sofic.  Graph-wreath permanence makes
the carrier sofic and hyperlinear, refuting
`arithmetic-star-packet-hs-wall-placement`.

Thus **positive-density finite memory is necessary but not sufficient**.  It
must be coupled to a matrix-only semantic return or overlap payment which is
absent from the pure finite packet relations.  The live target remains the
Culf--Mastel compiler into `positive-density-hs-power-overlaps-force-finite-depth`.

The aggregate Thompson--`V` Carmichael-energy shortcut is now refuted.
`scalar-phase-refutes-r5-subquadratic-energy` uses the fact that the marked
three-cycle `b=(01 10 11)` is literally a Bleak--Quick presentation
generator.  Mapping `b` to a small scalar phase and every other generator to
`1` gives arbitrarily small relator defect, while every word conjugate of
`U(b)` remains the same scalar.  Its all-pairs Carmichael energy is therefore
exactly `binom(M,2)|U(b)^4-1|^2`, never subquadratic.  This also kills the
proposed Hodge square-function bound.  The conditional energy-collapse
theorem remains correct, and the separate uniform-per-edge Carmichael lane is
unaffected.

A second live positive-density interface now removes one earlier logical
router.  For commuting context involutions `x_i` and a central involution
`J`, every assignment atom on the `J=-1` sector is exactly

```text
e_<x_i J^(a_i)> (1-J)/2.
```

Thus `central-sign-bcs-atoms-are-subgroup-reynolds-projections` names every
forbidden nonlinear atom by an ordinary finite-subgroup average.
`central-sign-reynolds-atoms-have-fixed-canonical-density` further shows that
an embedded `k`-variable atom already has canonical trace `2^(-(k+1))`.
Accordingly the non-CE gap is not needed to create the initial density; it
must be used to select or charge multiplicity in a way available only in
finite matrices.
`subgroup-hecke-hnn-is-a-regular-safe-rank-actuator` can pay a correctly
oriented Reynolds rank gap.  The central-sign front end now has exactly that
orientation: `central-sign-assignment-atom-is-index-two-reynolds-surplus`
identifies every forbidden atom as
`e_(H_a)-e_<H_a,J>` and produces a one-edge exit of equal trace.  The
remaining gate is not predicate decoding or local rank payment:
`central-sign-reynolds-first-hit-compiler` must route the compulsory
regular-trace exit flow through summable first-hit layers while the
finite-matrix BCS recurrence preserves one active copy.  The
established `branching-plus-first-hit-exits-forces-hs-floor` then closes the
normalized-HS contradiction.  The compiler explicitly cannot be
trace-functorial, by `exact-first-hit-ladder-kills-regular-carrier`.

Fresh BCS copies do not evade this requirement.
`agent-first-hit-fresh-copy-reynolds-tree-is-contractive` computes the exact
finite-depth ledger: if the next active layer is the orthogonal union of the
transported forbidden atoms, then

```text
c q_n-O(sqrt(E)) <= q_(n+1) <= q_n+O(sqrt(E)),
```

so even pairwise orthogonal generations give only the bounded geometric sum
`q_0 sum_n c^n`.  Keeping old layers cumulative merely returns to the address
Kraft bound.  More decisively,
`agent-first-hit-finite-fresh-tree-has-marked-matrix-model` constructs an
exact finite-dimensional `J=-1` representation of every finite presentation
assembled solely from fresh structural copies, finite role/address packets,
and finite-subgroup amalgam/HNN covariance.  Abelianizing each structural
copy and taking common multiples of the negative regular representations
makes every edge restriction match.  Thus no finite fresh-copy Reynolds tree
of this form has matrix soundness at all; an additional payload-sensitive
relation among several intertwiners is indispensable.

The latest shared-carrier audit removes one apparent shortcut in that
compiler.  `prefix-central-reducing-hull-recombines-context-returns` is a
valid way to discard external multiplicity gauges **after** all returned
ranges lie under one common successor prefix; padding an HNN chart by the
pulse packet does not supply that incidence.  The missing placement is now
`shared-schur-retained-children-have-common-next-tag-prefix`.
The local S3 endpoint square does not close it directly:
`schur-commutator-tag-is-not-fresh-under-selector-transport` proves that
transporting the literal Schur selector tuple forces the first target tag to
remain the corresponding affine selector word.  Transporting only the
endpoint table keeps a fresh tag but loses the shared successor context.
Thus the S3 mechanism solves the one-atom active/exit split, not the common
shared-BCS return.  A completion must transport a larger intrinsic type sum
and add a genuinely nonstationary relation on its multiplicity space;
finite packet functoriality alone retains the positive regular profile of
`finite-packet-functoriality-has-positive-regular-profile`.

This remains true after inserting the established local charged section at
every level.  `balanced-schur-finite-depth-reuse-is-regular-absorbed` puts
each Schur square and auxiliary companion flip inside its finite semidirect
vertex packet.  Reynolds proper sections, full-child reuse edges, and finite
first-hit transports are then all finite-subgroup HNN covariance rows.  At
every fixed depth, common negative regular multiples extend across the
entire graph and give an exact finite-dimensional model with payload sign
`-I` and all forbidden/child/address types present.  Therefore the global
reuse gate cannot be closed by simply concatenating the local cells, even
when one HNN edge is enlarged to carry the next prefix.  A genuine relation
between distinct edge intertwiners, or an equivalent matrix-only support
constraint on their common multiplicity space, is now the minimal missing
object.

The residual prefix gauge is now split into a solved local cell and an open
global ledger.  `agent-free-compressor-chart-edge-has-multiplicity-gauge`
proves that conjugating a finite child chart alone leaves an arbitrary
`U(m)` rotation on the multiplicity space; it can make the overlap with a
separately named successor prefix zero at exact relator defect zero.  The
minimal repair is to make the same edge conjugate one non-scalar prefix
involution.  `full-index-two-hnn-edge-creates-own-prefix-split` realizes
that repair for one Reynolds source: extending the HNN map over the full
index-two pair and sending its companion sign `J` to the target pulse `B`
gives

```text
u e_<H,J> u^(-1)=e_<H',B>=e_(H')(1+B)/2,
e_(H')-u e_<H,J> u^(-1)=e_(H')(1-B)/2.
```

So one retained source and its companion land exactly in the positive and
negative successor-prefix sectors, including after earlier first-hit cuts.
The remaining theorem is genuinely global rather than analytic, and one
natural assembly is now ruled out.  In
`full-pair-routing-of-complete-baseline-has-a-prefix-capacity-gap`, if all
`T` retained baseline types are made full-pair sources sharing `B`, then one
companion of the largest type already forces at least a `1/T` loss from every
successor carrier under the positive `B` prefix.  This contradicts lossless
return in the perfect model, where the forbidden surplus vanishes.  Hence
`balanced-schur-active-child-is-next-prefix-source` must use a hybrid ledger:
return the complete allowed/inactive baseline by a companion-free common
prefix mechanism, and use the exact full-pair cells only on the forbidden
surplus.

There is now a second, independent capacity restriction on that proposed
hybrid.  `companion-free-prefix-return-has-exponential-regular-capacity`
shows that any **functorial** lossless return of the complete baseline under
the independent positive pulse prefixes has canonical regular trace at most
`2^(-N)` at depth `N`.  This includes typewise full-chart HNN edges, central
auxiliary-sign coordinate changes, orthogonally tagged paired source halves,
and shared-variable amalgams: all preserve the trace of the recombined type
sum.  Hence `N eta q_0>1` is impossible for that whole class even though no
negative companion is carried inside the baseline.  The surviving version
of the hybrid must make common-prefix incidence a genuinely matrix-only
multiplicity assertion, false in `L(Gamma)`, or replace the independent
first-hit prefix geometry.

The bounded coefficient-ring route has been narrowed in parallel.  A single
payload-coupled finite PVM with oriented subsets would already supply the
missing scalar Morita trace:
`common-oriented-character-table-gives-morita-trace` proves that disjoint
subset union gives carrier additivity and the fixed Steinberg arrow words
give equality of source and range mass.  At one adaptive edge this
orientation is explicit.  After writing `q=b+a` and stabilizing the three
orthogonal coefficient lines `b,a,d`,
`three-line-first-hit-solves-local-morita-edge` uses the arrow involution to
swap the `a` and `d` character coordinates and takes the `d` mass in the
first-hit fiber where the two old coordinates are trivial.  This proves the
two local Morita equations exactly.

That calculation does **not** finish the decoder.  The selected BCS mass must
still be forced into the double-spectator-trivial source fiber, and all
outgoing edge tables must assign one common mass to their shared parent
carrier.  Both clauses are genuine.  The exact one-dimensional model in
`three-line-first-hit-has-invariant-spectator-escape` puts equal nonzero
character charge on the source and destination coordinates, is fixed by the
arrow swap, sees the full source root, and gives zero mass to the oriented
source fiber.  Thus additive root tables and their inner normalizers cannot
prove the missing estimate.  The live theorem is a matrix-only transverse
multiplication/contextual coupling which both suppresses this spectator
escape and aligns the parent measure across the finite adaptive menu.  This
is the sharpened content of
`hs-steinberg-morita-trace-additivity-on-adaptive-blocks`, not a Fourier or
finite-packet bookkeeping problem.

The transverse finite-packet part of that live theorem is now explicit.
`e5-idempotent-root-has-two-pair-extraspecial-cell` observes that the four
roots `x_12(a),x_23(a),x_14(a),x_43(a)` form two commuting Heisenberg pairs
with common center `x_13(a)`.  On every nontrivial central-character sector,
Stone--von Neumann forces the two commuting spectator coordinates to have
uniform joint multiplicity; their double-trivial fiber therefore retains
exactly `p^(-2)` of any packet-reducing source.  This eliminates the local
simultaneous-source/destination character escape **after the source root has
been detected**.  For the bare wordization the remaining analytic wall is
the BCS-to-root support transfer isolated as
`bcs-atom-detects-its-e5-central-root`: for
`E=Q_sigma P_i` and `Z=x_13(a_(sigma,i))`, prove that a fixed fraction of
`E` lies in the nontrivial spectral support of `Z`.  Its conclusion followed
by the two-pair cell retains `c_root p^(-2)` of `E` in a canonical
spectator-trivial fiber.  This is strictly weaker than reconstructing the
whole coefficient quotient, but it is not implied by the abstract root
relations; it is the finite-menu root-kernel reflection estimate.  The bare
statement remains open, but the extended canonical-microstate version is
now closed as follows.

The nonliteral-carrier part of this interface is now separated from the
finite-root part.  `a4-role-atom-has-flat-c3-root-overlap` proves that
on the three-dimensional block of `A4=V4 semidirect C3`, a nontrivial `V4`
role atom has exactly `2/3` of its mass on the nontrivial `C3` spectrum even
after an arbitrary analytic cut in the full `A4` commutant.  Products of
these packets supply a complete finite role menu.  Thus analytic reducing
hulls do not inherently defeat a genuinely mixed finite row.  A cyclic
amalgam may identify the `C3` word with an exact order-three coefficient
root: the perfect model simply represents the entire auxiliary factor
trivially when that root maps to one.  The remaining bare-`A4` issue is
coherent selection of its three-dimensional block along every reached
carrier.  `binary-tetrahedral-conditional-e5-root-bridge` replaces that
block by one common central-sign sector and is the sharper local compiler.
Specifically, attach

```text
(B times <ell>) *_(H times C3 times <ell>)
                    (H times (Q8 semidirect C3))
```

to each source root, sharing the fresh central involution `ell`.  Every
negative-center irreducible of `Q8 semidirect C3 congruent SL_2(F_3)` is
two-dimensional and its order-three complement has fixed-space dimension
at most one.  Hence every analytic packet-reducing source has at least half
its mass on the nontrivial spectrum of its **actual coefficient root**.
`canonical-bcs-root-detection-via-binary-tetrahedral-bridge` applies this to
the whole fixed menu and establishes the local root-overlap inequality.
However, `binary-tetrahedral-packet-hull-saturates-unprotected-seed-sign`
now rules out the first version of its carrier accounting.  One quaternion
element conjugates the independent Pauli seed sign to a free involution, so
the common reducing hull of the raw trace-`1/8` seed under the attached
packets is already the full `J=-1,ell=-1` sector of trace `1/4` in canonical
microstates.  The local detected fiber is valid, but the unprotected amalgam
has no remaining carrier budget.  In the perfect model all source roots,
`ell`, and the auxiliary packets still map to one, so the old marked word
survives.

The protected half of the direct endpoint is now closed by
`protected-adaptive-btb-wordization-preserves-canonical-budget`.  Add
`[q_sigma,B]=[d_(sigma,i),B]=0`, but deliberately do not centralize the
arrow letters.  For each source use the finite edge two-group
`K_i=<H_i,J,B>`; including `J` is necessary to preserve the marked central
sector through the amalgam.  Characteristic-three partial-bijection models
prove consistency and source nonvanishing, context absorption makes the
presentation finite, and coprimality makes
`K_i times <Z_(sigma,i)> times <ell>` an injected edge group.  All attached
packets then centralize `J,B`.  The initial common hull is exactly the
canonical `J=-1,B=+1,ell=-1` seed of trace `1/8`, while every later carrier
stays below the `J=-1,ell=-1` capacity of trace `1/4`; arrows may and must
switch `B`-sectors.  The perfect model kills each BTB component and retains
the old marked packet.  Thus `canonical-btb-finite-depth-escape-tree` now
has only one missing row: an oriented (or unoriented analytic) return must
move a fixed fraction of the conditioned `1/18` source fiber outside the
current carrier.  That row alone would restore the factor-two contradiction
recorded by `nonhyperlinear-via-canonical-btb-finite-tree`.

Property `(T)` and finite-packet stability do not by themselves close that
final row.  `hyperlinear-fiber-cannot-orient-btb-return` gives a local-carrier
obstruction.  After substituting the authenticated finite
BTB--E5 outer matrices, any finite actor/cross-edge system leaves a typed
presentation on the anonymous multiplicity factor.  If that presentation
has asymptotically exact matrix models, tensoring one with an identity
spectator produces a common invariant half and defeats estimates uniform over
all reducing carriers.  But that half is not automatically a carrier reached
from the canonical seed: `e_0` and every prescribed minimal hull amplify with
the full spectator identity.  Thus path-specific `(CBR3)` remains open.  Its
live exits are a typed multiplicity presentation with a dimension-uniform HS
floor, or a seed/minimal-hull coupling which prevents block-diagonal placement
on the actual reached carrier.  A Kazhdan estimate merely corrects into the
exact intertwiner algebra and does not supply either exit by itself.

That observation also yields a shorter endpoint.
`payload-conditioned-btb-active-fiber-floor` asks for ordinary relators whose
compression to the single positive root fiber pays
`kappa tau(F)`.  On the protected canonical seed, the maximal forbidden atom
has mass at least `beta/(8M)-o(1)`, and the BTB--E5 cell retains one
eighteenth, so the active fiber has mass at least
`beta/(144M)-o(1)`.  The route
`nonhyperlinear-via-one-btb-fiber-floor` then obtains a global defect floor
immediately.  This bypasses oriented return and all finite-depth growth.
Its remaining interface is exactly the same one exposed by the no-go:
compile the non-CE projection-algebra gap into a payload-conditioned typed
ordinary-word floor.  A fiberwise hyperlinear actor or cross-edge system
cannot do so.

The obvious static shortcut is now closed.  A literal order-three detected
character projection is a fixed group-algebra element, and
`canonical-btb-static-packing-has-capacity-ceiling` computes its exact
canonical mass using the coprime formula: the nontrivial root cut retains
`2/3`, not merely the representation-uniform `1/2`, of the literal source.
Under the common `J=-1,ell=-1` capacity, separate packing is bounded by
`3M/beta` conjugates and simultaneous packing by `3/beta`.  These ceilings
already exclude the strict counts that the static trace contradiction would
need.  Finitely many extra binary-tetrahedral or Heisenberg refinements do
not improve the ratio: orthogonal atoms partition source trace, while
overlapping atoms cannot be counted.  The analytic projection
`Q_sigma P_iS_(Z_i)` from the actual bridge is different: `Q_sigma` is a
representation-dependent reducing-hull projection, not a word or finite
Fourier idempotent.  Making a word transport respond to it is exactly the
open carrier-return row `(CBR3)`.  Thus static HNN packing does not bypass
the oriented-return gate.

The finite-tree version of that shortcut is closed at its exact boundary.
`btb-three-line-tree-retains-multiplicity-return-gauge` decomposes the
protected BTB--E5 conditioned fiber on every packet type.  The outer finite
coordinates retain the `1/18` mass, but an edgewise three-line return is
still `C_lambda tensor U_lambda` on multiplicity space.  With no relation
containing two adaptive-edge intertwiners, these gauges can be aligned
recursively so every returned fiber remains inside its reached carrier,
without changing fixed packet moments.  An `S_3` root-controlled reflection
can force one outer-coordinate escape only; its finite orbit then saturates,
while fresh palettes pay the independent-address capacity.  The repaired
route therefore needs one genuinely mixed cross-edge or payload two-cell
with nonzero multiplicity charge.  More protected signs or separate Morita
swaps do not prove `(CBR3)`.

There is now a sharp analytic candidate for that two-cell.
`compressed-antiphase-menu-implies-btb-escape` fixes a finite branch menu
`u_1,...,u_L`, with `L beta/(18M)>=4`, and asks for pairwise opposite phases
only on the compressed contractions `T_k=Q u_k F`.  The existing antiphase
cross-Gram estimate and contraction-capacity inequality then force one branch
to move at least `tau(A)/36-O(sqrt(E))` outside `Q`; hence `(CBR3)` follows
with `eta=1/36`.  This condition is automatically vacuous in the perfect
marked model, where the forbidden fiber `F` vanishes.  The companion firewall
`literal-antiphase-branches-recreate-regular-character-packing` proves that
ordinary full-source conjugacy cannot authenticate the condition: opposite
characters make the entire Reynolds translates orthogonal, so canonical trace
restores the finite-character packing ceiling in every tracial model, and an
oversized palette collapses the source already in the regular representation.
Thus the remaining groupification problem has an exact form: a finite
payload-sensitive cross-edge cell must control the phases of `Q u_k F`
without controlling the whole literal translate `u_k e_chi`.
The reached-hull localization itself has also been audited.
`cyclic-hull-antiphase-has-propagation-or-radius-firewall` proves that
centralizing the finite reducer makes a phase preserve the analytic cyclic
hull, but a seed phase then propagates to the entire cyclic component and
loses the proper contextual cut.  Conversely, no fixed support polynomial or
tight frame names that hull dimension-uniformly: explicit dihedral cycle
models have full cyclic hull and arbitrarily small fixed-radius orbit support.
The surviving cell must therefore be a genuinely mixed Reynolds/reducer
corner loop or an equivalent finite-dimensional matrix-coordinate identity.
The additive version of that loop has now been fenced as well.
`btb-balanced-loops-stop-at-same-object-reflection` tensors
the exact finite Morita rectangular model with an inverse Weyl gauge: all
fixed exponent-balanced Steinberg triangle pastings and one fixed projective
phase remain exact while the detected source returns inside the same carrier.
The first row outside this countermodel is the same-object support reflection
`(1-2f)W(1-2e)W^*=1`.  Current Clifford completion leaves an arbitrary
multiplicity involution on `1-2f`, exactly where this row needs it removed.
So the constructive target is no longer an unspecified holonomy: it is a
literal same-object reflection or a matrix-only support-leakage theorem with
the same consequence.
The residual twist cannot be removed by merely coupling more finite
reflections.  `coupled-reflections-reduce-to-the-active-gauge-profile`
exactifies the packet and writes every normalizer as `C_j tensor V_j`; all
finite covariance, determinant, parity, projective, and mixed reducer rows
then become one typed presentation on the multiplicity gauges.  The required
controlled/identity-outer cancellation is precisely `VA=1`.  Any matrix model
of that active presentation with `VA` separated tensors back to a local
countermodel, while a uniform estimate forcing `VA` is already the missing
nonhyperlinear HS profile in the gauge presentation.  Thus a successful
path-specific construction must force this equation through actual reached-
carrier incidence, not through another finite packet invariant.
There is now a uniform exact countermodel for the whole affine residual
subclass, not only the original two-bit example.
`affine-reflection-normalizers-have-quarter-overlap`
collects every finitely named commuting support sign into a Boolean vector
space `V` and every finite connector action into `K<=GL(V)`.  The regular
representation of `V rtimes K` satisfies all reflection-product and
normalizer rows exactly.  Distinct support halves nevertheless have overlap
and two-sided mismatch `1/4`; after tensoring with the selected payload fiber
the unpaid corner is `tau(F)/4`.  Extra finite XOR levels, affine normalizers,
and finite Clifford phases only enlarge this same stationary affine model.
Thus the same-object route must use a genuinely non-semisimple global
coefficient occurrence or solve the separated active gauge HS profile; no
finite affine reflection presentation can be the missing row.
There is nevertheless a regular-safe positive alternative to literal
reflection.  `balanced-hnn-conditional-gap-forces-carrier-escape` shows that
an equal-global-trace HNN transport `p_s -> p_t` moves at least
`tau(Qp_s)-tau(Qp_t)` outside an analytic carrier reducing both atoms.  This
gives CBR3 immediately from a payload-conditioned character imbalance and
has the correct `O(sqrt(E))` robustness.  For the native controlled-Clifford
pair the imbalance is `(tau(Qz_+)-tau(Qz_-))/4`; canonical orientation balance
makes it zero.  The remaining one-edge target is therefore sharply scalar:
couple forbidden payload mass to a nonstationary orientation profile, rather
than authenticate a globally unequal literal corner.
`finite-packet-flow-keeps-payload-orientation-balanced` now fences the finite
packet realization of that scalar target.  Every finite diagram of packet
restrictions, selector cuts, conjugacies and balanced HNN edges has a common
regular stationary multiplicity profile.  On its full protected carrier each
balanced source/target pair has equal conditional trace.  Tensoring with a
structural shared BCS tuple can keep a forbidden Reynolds atom positive, so
payload detection alone does not disturb this equality.  Orientation doubles,
finite orientation permutations and the odd selector do not remove the
countermodel.  The surviving construction must therefore force a genuinely
nonstationary payload/orientation coordinate on the canonical reached hull,
or implement a proper-corner return; enlarging the finite packet atlas cannot
do it.
The infinite address side is now separated just as sharply.  In
`baumslag-binomial-prefix-centralizer`, the
Baumslag relation `a^c=a^b a` gives a binomial basis for the negative lamp
ray.  Two centralizer relators therefore authenticate every earlier-lamp
commutator of every translated transporter, with polynomial HS cost.  So a
finite presentation really can name and preserve the whole first-hit prefix.
However, `baumslag-address-geometric-stationary-profile` gives
unbounded finite-field affine quotients in which the first `m` lamps are
independent and the regular prefix carrier has mass `2^(-n)`.  A positive
structural forbidden atom tensors into this exact model but decays down the
same geometric prefix.  Summability survives and carrier persistence fails.
The selector phase does not repair this.  In
`selector-baumslag-orbits-overlap-or-prepay`, the Pauli selector product has
square `-1` on the positive forbidden atom in those same exact finite-field
models.  Raw orbit halves keep mass `tau(A)/2` but have pairwise overlap
`tau(A)/4`; the first-hit refinement makes them orthogonal only with mass
`2^(-(n+1))tau(A)`.  More generally `N` orthogonal conjugate supports force
`N tau(A)<=1`.  Hence even the genuine payload-corner square-root cannot
turn infinite orbit naming into unprepaid capacity.
Thus the remaining row must be payload-dependent and supercritical: it must
install a full active child or proper-corner return on the actual reached
carrier, not merely authenticate an infinite first-hit address tail.
The most economical two-edge version has now been audited explicitly.
`two-orientation-hnn-packet-prepays-escape` adjoins one letter conjugating
`Z_1` to `s=t` and another conjugating it to `Js`.  On a carrier contained in
the matching primitive type, the source Pauli half has twice the target
overlap, so half of the selected source really leaves that primitive carrier.
The global HNN balance stores the missing corner as the rank-three complement
in the sibling orientation.  Exact balanced spin modules can route the whole
apparent exit there.  Keeping fresh future packets in a primitive type costs
one factor two in seed trace per level, and each later packet hull only
releases that prepaid factor.  Thus the construction is a valid one-use
conditional actuator but not a first-hit ladder; a cross-orientation
payload-conditioned row is still necessary.

Two qualifications are now explicit.  First,
`coprime-root-reynolds-prefix-overlap` proves the sharp local estimate

```text
tau(E(1-P_(Z,1)))=(1-p^(-1))tau(E)+o(1)
```

whenever `E` is a literal character idempotent of a finite two-group and
`Z` has exact odd prime order.  Hence root detection is already closed at
the initial Pauli/BCS Reynolds seed and along literal commuting-sign prefix
atoms.  Once a packet-reducing carrier is available, the
binary-tetrahedral extension also closes the local overlap estimate for an
analytic reducing hull in canonical microstates; the unprotected packet
hull itself saturates the capacity as above.  Literal prefixes alone still
have exponentially shrinking canonical capacity.  Second, the adaptive
ring compiler is currently stated in characteristic zero, while the E5
Fourier/Stone--von Neumann step requires characteristic `p`.
`odd-characteristic-adaptive-tree-wordization` now supplies the required
finite base change, exact order of every named root, and extension of the
perfect marked model.  Thus root order is closed; the order-`p` packet still
has to be imported through that explicit base-change node rather than
silently applied to the characteristic-zero statement.

Compatible finite Heisenberg densities do not supply that reflection by
themselves.  `finite-tags-do-not-atomize-heisenberg-schrodinger-tower` gives
an exact nested Schrödinger family with full nontrivial central-root mass and
perfectly compatible restriction densities, while every polarized
rank-`N` character atom has trace `p^(-N)`.  Tensoring any fixed selector,
tag, or `S3` packet leaves this decay unchanged, and the finite-window
commutant retains a full `U(p^(M-N))` holonomy gauge at level `M`.  Therefore
a positive-density decoder must aggregate exponentially many fine
characters with coherent coefficient maps, or use a genuinely growing
matrix-only return.  The common central spectral projection already exists;
what is missing is exponential-width cross-character coherence inside it.
This remains true after adding the obvious infinite self-copy skeleton.
`orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates` builds two
even/odd coordinate embeddings whose images commute modulo their common
center, generate the parent, and are implemented by two reused HNN letters.
Every finite relation window nevertheless has an exact Schrödinger model
with the marked center scalar and nontrivial: finite coordinate permutations
implement both branch maps on that window.  The missing relation must
therefore be a same-reservoir coefficient return which defeats this escaping
permutation boundary, not another fixed-window Heisenberg compatibility row.
The loss is now quantitative.  In a source window on `L` coordinates and its
joint even/odd child window on `2L` coordinates,
`heisenberg-self-copy-relators-do-not-pay-reservoir-loss` computes the adjoint
commutant densities as `p^(-2L)` and `p^(-4L)`.  Their positive difference is
literal multiplicity-reservoir loss while every Heisenberg, transverse-shear,
and reused-HNN-letter defect is zero; fixed finite tags do not change it.
Thus the paired boundary lemma cannot be proved from the self-copy skeleton
plus scalar branching data.  A full proof must charge that difference to a
mixed affine-Leavitt coefficient-return/Steinberg row not realized by the
Schrödinger calibration.

Even literal payload occurrence reuse does not make a finite positive-root
row load bearing.  `finite-positive-root-fragments-have-marked-regular-models`
observes that every finitely generated subgroup of `U_n^+(R)` over the
characteristic-`p` Leavitt coefficient ring is finite: the strictly
upper-triangular parts generate a finite-dimensional nilpotent `F_p`-algebra.
The finite subgroup's regular representation satisfies an arbitrary finite
positive-root diagram exactly—including all shared coefficient occurrences
and the range-sum fold—while a chosen nonzero root stays at HS distance
`sqrt(2)` with nontrivial spectral mass `(p-1)/p`.  Hence the earlier
independent-`UT_4` factor was not the essential escape.  The decisive
same-reservoir relation must leave the positive unipotent radical, through an
opposite-root, Weyl/Whitehead, or genuinely global return in the full
presentation.

The first mixed-root enlargement is now fenced as well.
`scalar-active-mixed-shell-has-marked-regular-model` embeds
the complete positive-and-negative elementary shell over the literal scalar
active corner `kA` into the finite group `E_n(k)`.  Its regular representation
keeps the active root at HS distance `sqrt(2)` while satisfying every
rank-one braid, Weyl/Whitehead conjugacy, and same-object return internal to
that shell exactly.  Hence an opposite root or active Weyl word is not yet
the missing relation.  The first potentially load-bearing row must contain
a genuinely non-scalar Leavitt coefficient and simultaneously forbid the
rectangular change of coefficient object.  The full signed Whitehead
occurrence table does eliminate exact marked matrix models, but its uniform
HS version remains precisely the unresolved same-reservoir payment.

The first non-scalar Whitehead cell is now fenced too.
`partial-whitehead-cell-has-marked-finite-model` observes that its complete
local coefficient table admits the finite-field specialization
`e=f=x=y=1`.  The active root remains nontrivial, the signed Whitehead word
has order four, and the finite controlled-packet cyclic amalgam is virtually
free and residually finite, with finite quotients faithful on both vertex
packets.  Thus one prefix partial equivalence cannot be the missing row.
The first possible payment must use both binary branches to destroy this
collapse specialization and must couple that collapse-killing occurrence
table to the same Reynolds/multiplicity payload.  The scalar range-sum fold
alone has an independent nilpotent-factor countermodel, so this is exactly
the still-open payload-coupled range-sum return.

The post-decoding endpoint is correspondingly smaller.
`two-inverses-one-cross-have-quadratic-hs-floor` shows that, on one decoded
matrix corner, the two diagonal inverse rows and a single crossed-zero row
already imply
`sqrt(tau(P))<=2epsilon_0+2epsilon_1+eta`.  This three-row package is
support-minimal for killing a marked finite coefficient algebra.  It remains
exact in the typed rectangular Morita model, so it does not solve the group
problem; it removes the range-sum arithmetic from the endpoint and isolates
the sole missing operation as same-object, payload-coupled coefficient
decoding.

The newest rectangular estimate weakens that last phrase.
`rectangular-three-row-cell-forces-double-target-capacity` proves that if the
same three rows are decoded between one source `E` and one target `F`, then
they force `tau(F)>=2tau(E)` with an explicit robust HS error.  Therefore
literal same-object decoding is unnecessary: it is enough to couple the
occurrences to a target whose conditional capacity is at most
`(2-kappa)tau(E)` for one fixed `kappa>0`.  The typed Morita model saturates
the threshold exactly at `tau(F)=2tau(E)`.  The remaining finite-presentation
task is consequently a strict payload-conditioned target-capacity deficit,
not full recovery of an identical reservoir.

The nonlinear BCS front end supplies exactly the scalar deficit once its
maximal atom is made into a forbidden target channel.
`bcs-deficit-plus-three-row-cell-kills-source` puts the shared BCS on a
target `T` of capacity at most `2tau(E)`, selects a forbidden atom `A` with
mass at least `(beta/M)tau(T)-O(sqrt(E_B))`, and takes `F=T-A`.  The BCS
upper bound on `tau(F)` and the rectangular three-row lower bound differ by
`2(beta/M)tau(E)`, yielding a dimension-independent carrier collapse.  In
the perfect infinite model `A=0`, so the sharp doubled Morita target remains
exact.  The remaining groupification interface is therefore one explicit
row: authenticate the three selected coefficient maps through the complement
of the maximal forbidden Reynolds atom.  Simultaneous transport of all
forbidden types and literal same-object recovery are both unnecessary.

The scalar capacity part of that task is now solved with arbitrary slack.
`dyadic-pauli-payload-flags-supply-strict-target-capacity` adjoins `n`
independent Pauli signs to a maximal forbidden atom, takes its first half as
the source `E`, and removes one depth-`n` dyadic atom from the target.  The
result is literal finite-packet data satisfying

```text
tau(F_n)=(2-2^(1-n))tau(E),
```

and both projections vanish in the perfect BCS model.  Thus any fixed
positive dyadic `kappa=2^(1-n)`, however small, is available.  The same
theorem proves the sharp regular-trace fence: the two inverse rows and crossed
row cannot be universal word consequences on this pair, since the left
regular factor would violate the factor-two capacity law.  The remaining
breakthrough is only a finite-coordinate occurrence-synchronization theorem
placing the native Leavitt maps through these named payload flags.

The most direct finite orientation pin for that mixed row also fails.
`packet-controller-orbit-products-have-orientation-dichotomy` considers a
product of packet conjugates of the rank-one controlled phase and compares
it with a literal Weyl/Pauli word.  If the total controller exponent is zero
modulo the packet characteristic, the multiplicity gauge cancels and the
row cannot see its orientation.  If the exponent is nonzero, the label
determinant is a nontrivial root of unity while every packet word has
determinant one, so the row is incompatible with the intended pure exact
model.  This covers both the two-qubit reflection and the odd-prime Weyl
analogue.  Consequently the needed coupling must genuinely cross Leavitt
scale (or be extracted from finite matrix coordinates); a finite controller
orbit cannot supply it.

The finite orientation ambiguity itself can be removed without solving the
return.  `primitive-clifford-type-fixes-orientation-not-return` selects the
positive primitive spin extension of the order-`64` controlled Pauli group.
That central block has canonical trace `1/4`, and on it the controller is
literally the desired rank-one reflection with no multiplicity involution.
But the coarse and fine atoms on this same block have relative traces `1/2`
and `1/4`, so every unitary coarse-to-fine return pays a quarter-block HS
floor.  A Whitehead scale change can avoid the floor only by moving mass out
of the primitive block.  Thus the remaining theorem is unambiguously a
mixed **type-return/leakage payment**, not local Clifford orientation.

That payment now has a smaller exact endpoint.
`odd-row-unoriented-fine-return-has-quarter-floor` shows that the Whitehead
word need not preserve the positive primitive type.  It is enough to place
the positive coarse half atom inside the **union** of the positive and
negative fine quarter atoms.  This union has the same canonical trace
`1/8` as the source, so it is compatible with rectangular finite geometry.
The odd relation `t=W r W^*` then charges the negative-orientation fine
piece, and an exact projection decomposition gives a `1/16-o(1)` ambient HS
floor.  The sole live estimate is the unoriented typed-support incidence.

The corresponding finite-group audit is exact.
`primitive-clifford-balanced-atoms-have-hnn-obstruction` identifies the
source and target as signed Reynolds projections of two explicit isomorphic
`C_2^3` subgroups, each of trace `1/8`; a separate regular-safe HNN letter
can transport them.  It cannot be the odd Whitehead transporter: the target
contains a trace-`1/16` negative-orientation block on which the required
controller eigenvalue is wrong.  Thus abstract subgroup matching is solved,
while identifying that HNN transport with the native coefficient word is
precisely the remaining matrix-only theorem.

Keeping the HNN letter separate and comparing it to the native word by a
polar/Gram construction gives no intermediate gain.
`separate-balanced-hnn-cross-gram-is-typed-overlap` proves that, if `h`
transports the signed source atom `p_s` to the balanced target atom `p_t`,
then

```text
G=p_s h^*W p_s,
tau(p_s)-tau(G^*G)=||(1-p_t)Wp_s||_2^2.
```

Thus source saturation of the cross-Gram is exactly the still-open typed
support estimate, before taking its polar part.  The equality is sharp: the
balanced eight-dimensional controlled packet extends by the full
character-preserving HNN edge and an exact odd-row unitary while making
`p_tWp_s=0`.  After four scalar twists this unitary has regular `C_4` type,
so it can be amalgamated with the order-four signed Whitehead word in the
finite typed rectangular coefficient chart.  Hence even literal reuse of the
native word and all relations in that isolated chart retains zero overlap.
Only additional relations from the **full** affine-Leavitt occurrence system
can possibly supply the missing incidence; a freely adjoined balanced
transporter cannot authenticate them.

The full-occurrence audit now has a sharp exact conclusion.
`full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark` lists the
entire coefficient table used by the signed three-root word, adds the one
harmless fourth-power relation needed to make its Steinberg lift an honest
`C_4` edge, and amalgamates it with the explicit controlled-Pauli monomial
packet.  Bass--Serre normal form keeps the packet mark nontrivial.  In every
exact finite-dimensional representation, however, the affine active
kernel-ideal argument kills the three Whitehead factors; the odd row then
forces `t=Z_1`, and two Clifford covariance rows force `J=1`.  Thus the full
relations genuinely eliminate the isolated `UT_4`/rectangular marked
countermodel.  What they do **not** provide is the normalized-HS promotion:
intersecting exact root kernels creates a finite coefficient quotient, while
an arbitrarily small HS error can have full rank.  Consequently the remaining
typed-support row is exactly a dimension-uniform kernel-ideal/MF-radical
theorem, not an omitted finite occurrence identity.

Nor does the full packet graft make that theorem weaker.
`whitehead-clifford-graft-hyperlinear-iff-base` proves

```text
Gamma_FWA hyperlinear  iff  Gamma_A' hyperlinear.
```

One direction is subgroup permanence and the other is hyperlinearity
permanence for the finite `C_4` amalgam.  In the left regular representation
of `Gamma_FWA`, all full occurrence and odd rows are exact, the finite packet
has its canonical regular type weights, and the established odd-row
decomposition gives

```text
||(1-p_t)W p_s||_2^2 >= 1/16.
```

This rules out property `(T)` spectral gap, fixed-root exactification, and
any other finite-tracial Gram/SOS promotion as sources of the missing
support estimate.  LLP, weak ucp stability, or flexible HS stability would
close it, but each is already a nonhyperlinearity-strength assertion for
this non-residually-finite Kazhdan base.  The robustness gate is therefore
the original MF-radical problem in a precise finite-edge disguise.

More sharply, the canonical asymptotic form of the typed-support estimate is
equivalent to nonhyperlinearity of this graft, hence—by finite-edge
permanence—to nonhyperlinearity of the affine-Leavitt base.  If canonical
microstates exist, their fixed leakage polynomial converges to the regular
value at least `1/16`; if they do not exist, the universally quantified
asymptotic estimate is vacuous.  Therefore the full `(OUF8)` endpoint cannot
be treated as an intermediate robustness lemma without extra quantitative
content: in its present canonical-sequence form it simply restates the main
open branch.

The active-gauge obstruction persists through a proper ordinary-Leavitt
quotient.  `ordinary-leavitt-quotient-fences-whitehead-active-floor` shows
that one coefficient coordinate sends the Whitehead edge to an element of
exact order four in `Q=EL_5(M_3(L_2(k)))`, and hence gives a quotient graft
`D *_(C_4) Q`.  If `Q` is hyperlinear, canonical microstates of this quotient
pull back to asymptotically exact models of every full affine occurrence row
while keeping the Clifford mark separated; tensoring an exact positive outer
payload fiber defeats any compressed active-floor estimate.  Thus using the
full signed occurrence system to prove BAF3 would already prove this explicit
ordinary Leavitt quotient nonhyperlinear.  This is stronger than an omitted
affine-root stability lemma and explains why neither exact finite-dimensional
collapse nor current character rigidity closes the gauge profile.

A finite noncommuting control action does not repair this defect.
`finite-packet-actions-have-positive-fiber-microstates` explicitly induces
each canonical actor microstate over the regular orbit of a finite packet
`P`: on the block `p`, the actor tuple is precomposed by the automorphism
`alpha_(p^(-1))`, while `P` permutes the blocks.  Every crossed covariance
row is then asymptotically exact, and every nonzero packet Reynolds fiber has
its fixed positive regular trace.  Tensoring the outer forbidden atom gives
zero compressed energy on a positive active fiber.  Hence the load-bearing
relation cannot be a finite automorphism coupling or finite projective
occurrence chart; it must leave the finite-extension class through a genuine
global/noninvertible coefficient incidence, or already force the actor to be
nonhyperlinear.

There is now also a clean regular-lamp consequence of the same simple
Leavitt actor.  `leavitt-regular-a5-wreath-is-minimally-almost-periodic`
proves that

```text
Q=EL_4(L_(F_2)(1,2)),
W=(directSum_Q A5) semidirect Q
```

are both finitely generated, nonsofic and minimally almost periodic.  The
proof for `W` is exact: every finite-dimensional actor image is trivial by
simplicity plus Malcev, covariance identifies all coordinate-lamp images,
and commutation of distinct coordinates makes that common `A5` image
abelian, hence trivial.  This removes finite-dimensional actor gauges from
the simple-lamp route for this specific actor.  It does not yet classicalize
normalized-HS microstates: on the branch where `Q` is hyperlinear, its
canonical asymptotic representations can occupy the lamp multiplicity
commutant even though no nontrivial exact representation can.  The remaining
upgrade is therefore precisely dimension-uniform asymptotic multiplicity
classicalization, not an exact representation-theoretic issue.

Using the entire multiplication shear rather than one root does recover a
genuine coefficient invariant, but it still does not cross this interface.
`steinberg-shear-fixed-labels-recover-ideal-dimension` computes the common
row-root Fourier table for a finite-dimensional coefficient algebra `A`:
the proportion of character labels fixed pointwise by multiplication with
`r` is exactly `p^(-dim(Ar))`.  Thus orthogonal idempotent ideals have
additive dimensions, but their fixed-label projections intersect and their
ordinary traces multiply; additivity appears only after `-log_p`.  This
closes the algebraic-rank-blindness question for full shear tables and shows
precisely why it is not the required Morita trace.  The remaining datum is
still linear physical mass on the representation-dependent BCS carrier,
not coefficient dimension in a fixed Plancherel window.

An independent finite role register does not bypass this interface.
`role-multiplexing-is-minimax-max-selection` proves
that role atoms do turn the arbitrary noncommuting forbidden family into one
literal orthogonal projection, but the optimal worst-case retained trace is
exactly `M^(-1)` of the total forbidden mass.  This equals the guarantee from
selecting one maximal type and cannot be improved because the role weights
sum to at most one.  Hence arbitrary-list SELECT is unnecessary for
orthogonal bookkeeping, but the proposed replacement produces neither a
mass gain nor a payload-conditioned exit.  The live theorem remains the
mixed BCS-to-root/first-hit placement rather than a larger finite role
packet.

The same calculation nevertheless removes the finite branching coherence
from the coefficient-ring route.  `role-packed-bcs-gap-is-one-idempotent`
uses a unique-spin role packet to form

```text
B_f=sum_i R_iP_i,
tau(QB_f)>=(beta/m)tau(Q)-O(sqrt(E)),
```

on every packet-and-BCS reducing carrier.  The summands are orthogonal even
across noncommuting contexts, and `B_f=0` in the perfect tracial model.  One
may therefore run the finite coefficient compiler as a unary ladder with
`a_n=q_nB_f`; a depth satisfying `(1+beta/m)^N>2` is enough.  This trades the
representation-dependent maximal-type tree for one fixed aggregate source
and eliminates incompatible outgoing orientations at a parent.  It does
not solve normalized-HS group decoding: the remaining statement must still
place `q_nB_f` on its E5 root carrier and carry the resulting oriented
physical carrier consistently to level `n+1`.

That reduced coefficient-ring statement is isolated as
`hs-unary-role-packed-ring-decoder`, with the complete implication recorded
by `nonhyperlinear-via-unary-role-packed-decoder`.  There is now a strictly
smaller direct endpoint.  `reducing-hull-carry-forward-after-aggregate-escape`
proves that once `U_n(Q_nB_f)U_n^*` loses a fixed fraction of overlap with
`Q_n`, the reducing hull of their join automatically is the next valid
shared-variable carrier and has the required trace gain.  No prescribed
coefficient projection has to decode as that hull.

Accordingly `finite-depth-role-packed-aggregate-escape` is the current
one-row target: for finitely many reached carriers, force

```text
tau(Q_n U_n(Q_nB_f)U_n^* Q_n)
 <=(1-eta)tau(Q_nB_f)+O(sqrt(E)).
```

The route `nonhyperlinear-via-role-packed-aggregate-escape` then gives
`tau(Q_(n+1))>=(1+eta beta/m)tau(Q_n)-O(sqrt(E))` and closes the marked-sector
capacity contradiction at any fixed depth with
`(1+eta beta/m)^N>2`.  Thus successive-carrier compatibility is no longer a
separate open gate.  The sole remaining operation on this lane is the
payload-sensitive overlap loss itself.

The first completely explicit escape row is now understood, including why
it cannot renew.  `agent-aggregate-escape-forbidden-support-saturation`
proves that `Q B_f` has full reducing support in every corrected shared-BCS
carrier `Q`: any reducing complement avoiding it has zero forbidden mass and
is therefore killed by the robust BCS gap.  Conjugating by the Pauli seed
flip consequently moves `Q_+B_f` exactly to the orthogonal projection
`Q_-B_f`, but its shared-algebra hull is all of `Q_-`.  Thus after one perfect
escape the next carrier is already the full marked sector and no second
fixed-fraction escape is possible.  The general form
`agent-aggregate-escape-normalizer-erases-payload` shows that this is not a
defect of the Pauli choice: every word normalizing the shared algebra carries
full reducing support to full reducing support, so its successor is merely
the orbit of the whole old carrier.  A successful row must therefore be a
genuinely non-normalizing representation-type correspondence whose payload
occupies only a proper set of target multiplicity slots.

Using two full structural edges does not create that correspondence.
`two-edge-holonomy-erases-role-packed-payload` composes two parallel
shared-algebra intertwiners and obtains a normalizer automatically.  If the
edge maps agree and the holonomy preserves the reached carrier, it fixes
`Q_nB_f` exactly, so the overlap loss is zero.  If the maps differ, the
returned forbidden aggregate has full reducing hull `WQ_nW^*`, and the
quantitative payload density is replaced by payload-independent whole-carrier
orbit growth.  Thus the minimal cross-edge loop is fenced as well: one edge
must be genuinely partial on the shared algebra and its ordinary relators
must authenticate that partial incidence specifically on the role-packed
corner.

Listing the forbidden Reynolds atoms under one stable letter does not create
such partiality.  `one-letter-reynolds-rows-globalize-structurally` observes
that all assignment atoms of a context are characters of the same finite
context subgroup.  One conjugation map must agree on all shared-variable
overlaps, so the listed rows extend automatically to the subgroup generated
by every context and the common role diagonal.  Adding the transverse role
covariance makes the letter a full structural intertwiner and returns the
whole translated carrier; omitting it leaves the spin multiplicity gauge
uncontrolled.  Thus the surviving unary arrow cannot be one common
finite-subgroup HNN transporter.  It needs a multi-piece coefficient
recombination or a non-conjugacy incidence visible only on `Q_nB_f`.

The shortest literal-word implementation of that loss is excluded.
Although `central-marked-two-cycle-zero-compression-cell` groupifies a source
named by literal grading involutions, the aggregate reflection is not such a
word.  `role-packed-forbidden-reflection-is-not-a-group-word` computes

```text
0<tau_G(B_f)<=1/4,
```

whereas the negative projection of a nonidentity literal involution has
canonical trace `1/2`.  Thus adjoining a generator and declaring it equal to
`1-2B_f` cannot preserve the embedded packet group algebra.  The surviving
aggregate escape must be a multi-piece Hecke corner or a genuinely
matrix-only compressed authentication, not a disguised third grading bit.

One tempting proof of its first clause is now excluded.
`root-scaling-covariance-does-not-detect-bcs-atom` gives an exact marked
one-dimensional model in which all coefficient-eigenvalue conjugation rows
hold, the desired BCS joint character survives, and the corresponding E5
root is trivial.  The transverse Heisenberg packet also collapses in that
model.  Thus the required aggregate payload-to-root transfer must prevent
the root-kernel quotient by a genuinely mixed corner relation; assignment
sign covariance alone is insufficient.

Independently, `tracial-superoperator-self-copy-has-no-macroscopic-excess`
proves the qualitative adjoint projection theorem with no property `(T)`:
parent and compressed-child zero-energy projections agree in every adjoint
tracial ultraproduct.  This reduces the generic finite-memory route to the
single open amplifier `marked-self-copy-forces-macroscopic-adjoint-excess`.
It does not replace the Kazhdan quantitative theorem or detect microscopic
`o(d^2)` excess sectors.

The abstract quotient orientation of that amplifier is no longer open.
`finite-inclusion-is-free-self-compressor-quotient` constructs, for every
finite packet inclusion `A<B`, a proper injective endomorphism of a
finite-rank free group whose parent quotient image is `B` and whose child
image is `A`.  The route
`macroscopic-self-copy-via-localized-free-quotient` therefore isolates the
remaining payload seam exactly: on the BCS forbidden carrier, force the free
compressor kernel to vanish with a dimension-independent HS bound, while it
remains unconstrained in the perfect infinite model.  If that
carrier-localized factorization is supplied, the established predicate
Reynolds rank jump gives the positive-density child-only sector and the
tracial self-copy theorem closes the route.

There is now a minimal signed-Reynolds calibration of that seam.
`finite-reynolds-carriers-have-only-finite-pointwise-stabilizer` takes
`H=F(x,y)`, the proper square embedding `x->x^2,y->y^2`, and a `C_2^2`
packet on which `x` swaps two orthogonal character atoms while the child
centralizes the packet.  Multiplying one atom by the forbidden selector
projection makes the motion vacuous in the perfect trace and gives squared
displacement `2tau(F)` on an active packet.  This supplies exactly the
finitely generated self-copy and finite parent/child shadow one might want.
It does not supply the fixed sector: a nonzero finite-support Reynolds
coefficient has only a finite pointwise stabilizer.  Child normalizer rows
make the resulting positive-rank left ideal invariant, not pointwise fixed,
and the multiplicity action can have vanishing commutant density.  Thus a
signed Reynolds atom cannot replace conditional kernel annihilation; the
needed relation remains the additive payload row `(alpha(s)-1)F=0` (or a
genuinely equivalent matrix-only decoder).

At the coefficient-ring level this localization can be written down, but a
later algebraic audit shows that the **complete** localization is too strong.
If `r_1,...,r_s` normally generate the free quotient kernel and `P_f` is the
forbidden packet idempotent, the finite rows `[P_f,F]=[P_f,t]=0`,
`(r_j-1)P_f=0`, and the named identifications
`(u_i-b_i)P_f=0` do put the parent `B_f` and child `A_f` actions on one
corner.  They do more than exclude finite coefficient modules.
`agent-free-compressor-bcl-root-is-abstractly-zero` proves that they force
`P_f=0` in the presented coefficient ring itself.  Indeed, if a primitive
forbidden block survived, conjugation by the invertible stable letter would
inject

```text
P_f k[B_f] = M_(2D)(k)
```

into the strictly smaller algebra

```text
P_f k[A_f] = M_D(k) tensor I_2,
```

which is impossible.  Hence every Steinberg word `x_ij(P_f)` is already the
identity in the abstract group.  This is not a metric-decoding theorem and
cannot furnish a marked cyclic amalgam edge.

The free-compressor endpoint can in fact stop before decoding either finite
packet.  `agent-free-compressor-payload-kernel-fixed-sector` asks only for a
positive-density adjoint carrier which is almost fixed by the finite normal
generators of the infinite kernel `ker(theta)` and almost reduces the free
basis.  Telescoping then makes every fixed kernel element act trivially on
that carrier, while
`canonical-infinite-subgroup-has-zero-adjoint-fixed-density` makes such a
macroscopic carrier impossible in canonical microstates.  The corresponding
terminal implication is established by
`agent-free-compressor-kernel-carrier-is-terminal`.

Finite root tables and quotient covariance do not create this carrier.
`agent-free-compressor-kernel-multiplicity-firewall` tensors an arbitrary
finite representation of the free kernel onto every exact quotient-packet
model and makes the fixed fraction of any chosen nontrivial kernel word as
small as desired without changing the packet carrier density.  The surviving
minimal statement is therefore the mixed one-row reflection
`agent-free-compressor-one-row-kernel-reflection`: wordize only
`[P,x_i]=0` and `(r_j-1)P=0`, and reflect those fixed coefficient rows to one
Hilbert projection of mass comparable to the forbidden BCS mass.  Squaring
that Hilbert corner would give the required adjoint sector, but the proposed
reflection is false from those rows alone.
`agent-free-compressor-one-row-product-ring-no-go` uses
`F_p times F_p[F]`: the payload root has fixed positive spectral density in
exact finite regular representations while a kernel diagonal lives in the
independent product factor and has vanishing near-identity density.  All
rank-five root identities and `(r_j-1)P=0` still hold exactly.  Thus the
remaining free-compressor route again needs full module/corner
authentication, or a non-retractive relation coupling the diagonal action
to the payload spectral carrier; the single mixed coefficient row is not a
valid shortcut.

Adding the actual ascending-HNN letter without that identification still
does not help.  `agent-free-compressor-hnn-letter-preserves-product-split`
extends the same product-ring model through `[P,t]=0` and the complete table
`t x_i t^{-1}=alpha(x_i)`: the stable letter acts entirely in the mapping-
torus factor while the payload root remains in the other factor.  The finite
coefficient-module obstruction is minimal and explicit in
`agent-free-compressor-minimal-nonretractive-corner`.  Besides stable-corner
invariance and the HNN table, imposing the named packet-identification rows
`[P,u_(x_i)]=0` and `P(u_(x_i)-b_i)=0`.  On `PH` these three row families
identify the parent free action with the prescribed `B` packet and conjugate
its `B`-fixed space onto the `A`-fixed space.  Their ranks are equal, whereas
the selected predicate packet has a fixed positive `A/B` Reynolds rank gap;
hence every exact finite coefficient module has `P=0`.  The stronger
abstract-collapse audit above shows why this cannot be promoted as a marked
root construction: putting all three rows into one coefficient quotient has
already erased the root before any representation is chosen.  It remains a
valid endpoint after a physical corner has been independently authenticated,
but it is not a source of such a corner.

The earlier exact ordinary-group endpoint is therefore true but vacuous as a
nontriviality witness.
`agent-free-compressor-full-corner-root-is-fd-invisible` proves that every
exact finite-dimensional unitary representation of this rank-five Steinberg
group kills every payload root `x_ij(P_f)`.  Its common root kernel is a
two-sided coefficient ideal, and the additive root image is a finite
elementary abelian `p`-group, so the coefficient quotient is a finite ring.
If `P_f` survived, that finite ring's left regular module would satisfy the
three named corner rows with nonzero `P_f`, contradicting the Reynolds rank
gap above.  Thus all exact finite quotient, stationary-type, and product-ring
countermodels are exhausted.  But `P_f=0` already in the coefficient ring,
so vanishing normalized-HS relator defect forces
`||rho(x_ij(P_f))-1||_2` to vanish by fixed-word telescoping.  The old
question `(FCI3)` is automatic, not the frontier.  Known
2-Kazhdan/Frobenius-stability theorems would not have supplied a nontrivial
version of this implication:
they use the unnormalized Frobenius norm.  Since
`||X||_F=sqrt(d)||X||_(2,d)`, a normalized-HS defect tending to zero may lie
arbitrarily far outside their correction basin, and block amplification
preserves the normalized defect while multiplying the Frobenius defect by
the square root of the amplification.  What would finish this route is a
native normalized-HS marked-root correction estimate, or a replica-
homogeneous global Frobenius inequality strong enough to divide by
`sqrt(d)`; neither follows from qualitative 2-Kazhdan stability.  That
normalization warning remains relevant for any replacement using an
abstractly nontrivial finite-dimensionally invisible root, such as the
Toeplitz candidate, but it is no longer load-bearing for the collapsed BCL
root.

The Toeplitz candidate now has an exact one-edge terminal compiler.
Choose characteristic three, so the nonzero defect root
`w_f=x_12(P_f)` in `schur-toeplitz-root-mark-is-fd-invisible` generates an
injected `C_3`, and form

```text
G_ATC = A4 *_(<z>=<w_f>) H_f,
A4=<b,z | b^2=z^3=(bz)^3=1>.
```

`agent-free-compressor-a4-toeplitz-root-compiler` proves by Bass--Serre
normal form that both factors embed, so the marked involution `b` is
nontrivial.  If every normalized-HS asymptotic representation of `H_f`
kills `w_f`, then every such representation of `G_ATC` kills `z`; the two
triangle relations then give `b^2=b^3=1`, hence `b=1`.  The same argument is
dimension-uniform at the presentation level:

```text
||rho(b)-1||_2
 <= C (||rho(w_f)-1||_2 + sqrt(E_pres)).
```

Thus `hs-schur-toeplitz-root-defect-collapse` alone would produce a
nonhyperlinear recursively presented group, and Higman embedding would put
it in a finitely presented nonhyperlinear overgroup.  No BCS selector,
carrier ladder, or additional groupification is needed on this branch.
The entire analytic content is the native normalized-HS collapse of the
abstractly nontrivial Toeplitz root.

The `A4` edge is analytically conservative.  Every exact `C_3`
representation extends through the abelianization `A4->C_3` by taking
`b=1`, and the canonical uniform `C_3` type extends after a fixed
amplification because `Reg(A4)|C_3=4 Reg(C_3)`.  Thus the triangle cannot
improve the Toeplitz root estimate; it only converts that estimate, once
proved, into collapse of a visibly nontrivial involution.

There is a sharp firewall against solving the Toeplitz root theorem by
finite-von-Neumann direct finiteness alone.
`finite-vn-toeplitz-coefficient-reconstruction-fails` takes the faithful
left regular representation

```text
H_f -> U(L(H_f)).
```

It satisfies every rank-five root, Heisenberg, and stable-letter relation in
a finite tracial von Neumann algebra, but its common root kernel is zero.
The corresponding coefficient quotient is therefore `R_f` itself, with
`yx=1` and `xy=1-P_f!=1`.  Hence neither stable finiteness, a faithful
Sylvester rank, nor a faithful coefficient representation into the ambient
finite algebra follows from the exact group relations.  The remaining proof
must use specifically matricial/Connes-embeddable lift data and a quantitative
decoder which has no analogue for the regular representation; limiting
finite trace by itself cannot close the argument.

The binary child refinement does not strengthen that exact-tracial input.
`binary-toeplitz-root-refinement-has-a-bernoulli-haar-fixed-point` computes
the complete joint law in the faithful regular model.  The roots
`w_j=x_12(x^jP_fy^j)` form iid commuting Haar `C_p` variables, yet the binary
stable letter satisfies

```text
t^n w_0 t^-n=product_(j<2^n)w_j.
```

Thus even an exact identification of one parent with the product of two
independent, transverse children yields only the idempotent spectral equation
`mu=mu star mu`.  Besides the trivial solution it has the uniform Haar
solution, realized here with `||w_0-1||_2^2=2`.  Consequently no trace or
spectral functional equation extracted from binary covariance can choose the
trivial root.  The live Schur--Toeplitz endpoint is still specifically a
matrix-lift/direct-finiteness decoder or an oriented payment for one child.

The concrete finite-head quotient does, however, remove the ascending HNN
letter from the approximation question.  In
`toeplitz-finite-head-hnn-approximation-is-base-equivalent`, if
`G=EL_5(T)` and `K` is its finite-head mapping torus, the symbol computation
gives

```text
1 -> N_infinity -> K -> EL_5(k[z,z^(-1)]) x Z -> 1,
```

with `N_infinity` locally finite, and the compressor acts trivially on the
Laurent symbol.  Subgroup heredity, directed-union closure, and permanence
under the amenable quotient `Z` therefore give the exact equivalences

```text
K hyperlinear iff G hyperlinear,       K sofic iff G sofic.
```

The root is nontrivial but lies in the finite residual of `K`.  Every model
obtained from a coefficient map into a finite or directly finite ring kills
it, since `YX=1` then forces `XY=1` and hence `P=0`.  Thus cyclic ring
periodization and any restricted-wreath construction factoring through it
cannot be the countermodel.  A root-preserving approximation would have to
be genuinely group-theoretic.  The sharp falsification target is now the
single explicit base question `EL_5(T)` hyperlinear?; neither the stable
letter nor general amenable-normal permanence supplies an answer.

The physical-corner proof still cannot be split into “authenticate the
corner” and then “pay the HNN mismatch.”
`agent-free-compressor-authenticated-corner-pays-hs` proves the second step
completely: on any physical projection where the named free generators agree
approximately with the `B_f` packet and the stable letter preserves the
carrier, telescoping the fixed Reynolds averages gives
`gamma tau(e)<=C(delta+epsilon)` dimension-independently.  But
`agent-free-compressor-named-row-retains-complement-gauge` gives exact
rank-`N` product-ring models for every `N>=3` satisfying the full selected
packet block and `P(u_i-b_i)=0`, with macroscopic `x_13(P)` spectrum while
every near-agreement projection for `u_i,b_i` has vanishing trace.  Raising
Steinberg rank leaves this countermodel intact.  Therefore any reusable
corner theorem must use the named row, `[P,t]=0`, the HNN conjugacy, and the
`B_f/A_f` rank gap simultaneously; neither root decoding nor HNN payment is
valid as an independent first stage.  The complete coefficient quotient is
not that theorem, because it simply sets the named corner to zero.

There is now a finite ordinary-group front end for the missing payload
coupling.  For each forbidden Reynolds atom `E=e_H Q_-`, attach an `A4`
triangle with order-three generators `z_1,z_2` and
`z_1z_2=hJ`, where `h in H`.  On `E` the product is `-1`, and hence

```text
||(z_1-1)z_2E||_2^2+||(z_2-1)E||_2^2 >= 2 tau(E).
```

Splitting the two order-three letters into their nontrivial Fourier
projections shows that one of four fixed overlaps has trace at least
`tau(E)/6`.  This is a genuine finite-menu scalar selection theorem.  It
does **not** yet produce a fixed packet projection: the support of the
compressed overlap `RAR` depends on the representation, and the ambient
Bass--Serre bridge algebra is generally infinite dimensional.  The corrected
`agent-aggregate-escape-a4-bridge-lands-at-bcl-root-gate` therefore stops at
the four overlap numbers.  Turning one of them into one presentation-level
coefficient idempotent is precisely the remaining payload compiler; taking
central support inside a model is not such a compiler.

Literal identification of an `A4` order-three letter with the complete BCL
payload root is impossible more basically: that root is abstractly trivial,
so the cyclic amalgam map is not injective and the quotient forces extra
relations back onto the `A4`/BCS factor.  Conditional Fourier support avoids
that literal collapse but lands at the same metric interface.
Accordingly the surviving front-to-back statement is no longer an
arbitrary Boolean router or a multi-type transport theorem.  It is the one
local implication

```text
positive physical A4/BCS Fourier overlap
    -> positive spectral mass of one fixed named coefficient root,
```

with a dimension-independent normalized-HS modulus.  This is the local
claim `bcs-atom-detects-its-e5-central-root`.

Nor can one first kill a root algebraically and then recover conditional
meaning by adding mixed relators through it.
`agent-aggregate-escape-trivial-root-erases-mixed-rows`
proves a quantitative Tietze substitution theorem: if a word `w=1` has a
fixed derivation from the base relators, every finite mixed row
`r(S,Y,w)` is both algebraically and normalized-HS equivalent to
`r(S,Y,1)`, with a dimension-independent telescoping constant.  Therefore
the collapsed BCL root contributes nothing to a future coupling.  Either the
root-free residue already excludes the forbidden physical character—in
which case it alone is the desired compiler—or it admits an exact
positive-payload countermodel.  A successful root route must start with an
abstractly nontrivial payload word.

Finite overgroups cannot supply that word conditionally.
`agent-packet-root-finite-detectors-are-normal-quotient-selectors` gives the
exact classification.  For a finite packet `H<=K`, an odd-order element
`z in K`, and a packet idempotent `q in C[H]`, put
`N=H intersect normal_closure_K(z)`.  A dimension-uniform inequality

```text
tr(rho(q)) <= C ||rho(z)-1||_2^2
```

for all finite-dimensional `K`-representations exists exactly when `q`
already maps to zero in `C[H/N]`.  Necessity is witnessed by the regular
representation of `K/normal_closure(z)` restricted to `H/N`; sufficiency is
finite character theory.  Thus induction, a finite overgroup, or a finite
Schur phase detects only an algebraic normal-quotient selector, never a
trace-specific forbidden corner.  In an infinite replacement the quotient
by the root must itself be quantitatively non-RFD relative to `H`; that is
the same hard groupification input in a sharper form.

The perfect-completeness version is now an equivalence, not just a barrier.
`agent-packet-root-bridge-is-perfect-kernel-separation` proves that a finite
extension with an abstractly nontrivial order-three root `z`, an extension of
the perfect representation with `z=1`, and `q=0` after quotienting by
`normal_closure(z)` exists exactly when there is already a normal subgroup
`M normal H`, contained in the perfect-model kernel, with
`q=0 in C[H/M]`.  The converse compiler is explicit, using a finite
wreath-product packet with an alternating-group base.  For binary contexts
this criterion says precisely that the forbidden assignment lies outside
the affine hull of the perfect local support.

Consequently neither Slofstra's wagon-wheel embedding nor a faithful
Bass--Serre enlargement can manufacture the missing separator.
`agent-aggregate-escape-faithful-extension-keeps-affine-ghosts` observes
that any perfect representation extending across an injective groupification
has exactly the same kernel on every original context group.  If it extends,
all affine ghosts remain; if it does not, perfect completeness has been lost.
The remaining task on this branch is therefore exactly a non-CE perfect
trace with locally affine support, which
`locally-affine-support-bcs-is-exactly-the-lcs-boundary` proves equivalent to
the perfect non-CE LCS endpoint and hence to the desired group theorem.

The obvious ways of changing the supplied trace cannot create that support.
`affine-ghosts-survive-recoverable-tracial-dilations` observes that affine
hull commutes with every affine decoder back to the old assignments.  Matrix
amplification, central/direct sums, classical polarization, and tagged tensor
products all retain such a decoder, so every old forbidden affine ghost
survives.  Untagged tensoring evades the invariant only by losing the
recoverable copy of the non-CE source algebra.  A support-pruning compression
is tracial only on a central summand.  Thus the precise surviving choice is a
non-CE central/factor component already having locally affine-safe support,
or a genuinely global nonrecoverable compiler whose non-CE output is proved
from scratch.

There is nevertheless no quantitative loss hidden in the **restriction**
direction of Slofstra's embedding.  The strengthened
`marked-approximate-radical-survives-solution-group-embedding` gives explicit,
dimension-independent constants `A,B` with

```text
kappa_Gamma(delta) <= kappa_G(A delta)+B delta.
```

They are read from the finite wagon-wheel pictures: a collegial relator of
length `l` has an explicit `3l`-vertex filling.  Thus any marked approximate
radical already constructed in the source transfers robustly to the solution
group.  What the embedding does not do is create that source radical, extend
arbitrary source microstates to the wagon wheel, or remove the locally affine
ghosts identified above.  A quantitative constellation-stability theorem is
therefore unnecessary for the one implication that would be useful here, and
would not solve the missing source gate.

Ordinary property `(T)` cannot upgrade exact root invisibility to this
metric statement.  `agent-aggregate-escape-kazhdan-root-no-upgrade` records
Thom's property-`(T)` LEF root construction: exact finite-dimensional
representations kill the marked root while finite regular LEF models form a
normalized-HS asymptotic representation keeping it at fixed distance from
the identity.  Thus any successful estimate must use the actual mixed
payload relations, not exact invisibility plus a generic Kazhdan wrapper.

The stability literature audit now identifies the maximal unconditional
positive result for the full Whitehead construction.
`affine-whitehead-hyperfinite-stability-misses-canonical-mark` proves that
every **hyperfinite** asymptotic representation of `Gamma_A'` kills `W`, and
every hyperfinite asymptotic representation of `Gamma_FWA` consequently
kills `J`.  This uses property `(T)`, the fact that amenable factorial
representations of Kazhdan groups are finite-dimensional, and
Dogon--Vigdorovich's exact hyperfinite-HS character criterion.  But a
canonical approximation of either group, if it exists, converges to its
nonamenable regular von Neumann algebra, so it is excluded by the definition
of that theorem.  Strict or flexible normalized-HS stability would close the
mark but is itself branch-selecting; cohomological stability is in
unnormalized Frobenius norm; higher-rank character rigidity assumes a
commutative Noetherian coefficient ring; and Slofstra supplies an embedding,
but no retract or approximate-extension functor.  Thus the exact remaining
hypothesis mismatch is **nonhyperfinite marked correction on the affine
vertex**.  No currently established stability theorem turns the exact
kernel-ideal collapse into that statement.

The character-rigidity audit is now sharper than this hypothesis mismatch.
`affine-whitehead-has-leavitt-quotient-character-face` centralizes the active
head and projects its two Wedderburn blocks to obtain

```text
Gamma_A' -> Q times Q,       Q=EL_5(M_3(L_2(k))).
```

The map survives the `W^4` quotient.  Each coordinate kernel is infinite,
and `Q/Z(Q)` is infinite simple and ICC.  Pulling back its regular character
therefore gives an extremal character of `Gamma_A'` which is neither regular
nor finite dimensional.  Hence the standard character dichotomy and the
Margulis normal-subgroup property are not merely unavailable: they are false
for this base, even after discarding the finite inactive direct factor.  A
CE-only character collapse would already prove the ordinary Leavitt quotient
nonhyperlinear.  The faithful canonical character remains in the regular
branch, and relative `(T)` cannot make its diffuse root algebra finite.  The
broader induced-character classification does not help either: this quotient
character is already induced from the trivial representation of its
infinite-index kernel.  The smallest live input is still the nonhyperfinite
canonical lifting/kernel-ideal estimate.

The projective-kernel compiler has also been reduced to its exact source
gate.  `agent-projective-kernel-factor-face-is-playerwise` proves that for a
factorial left--right game representation the full two-player scalar kernel
is the product of the two one-player scalar kernels, and its CE trace face is
nonempty exactly when both one-player faces are nonempty.
`agent-projective-kernel-arbitrary-phase-face-compiler` then removes the
finite-phase hypothesis: compactness reduces any CE-empty circle-valued
one-player face to finitely many scalar equations, and Thom's central-corner
criterion turns them into a finitely presented nonhyperlinear central
extension.  What remains is not formal extraction from the known BCS trace.
`agent-pk-affine-ghost-survives-quotient` computes that a context's full
projective kernel cuts out precisely the affine hull of its perfect support;
every forbidden affine-hull ghost reappears with equal positive mass in the
canonical twisted-regular quotient trace.  Hence the fixed non-CE BCS gap
does not prove the one-player face empty.  Establishing
`agent-projective-kernel-one-player-monomial-face-gap` would itself be the
new global group-factor theorem that closes this branch.

The one-row central-support alternative has a corresponding exact firewall.
`agent-aggregate-escape-central-support-orientation-terminal` shows that it
would suffice to adjoin a central involution `K`, put `T=(1-K)/2`, and prove
`||T B_f||_2^2=O(sqrt(E))`; the robust role-packed gap would then force the
whole `K=-1` carrier to vanish.  But
`agent-aggregate-escape-rfd-support-orientation-firewall` proves that the
zero-defect case places every corner `T R_iP_i` in the finite-dimensional
radical of the output group C-star algebra.  Any residually finite extension
preserving the local finite packet, any finite Bass--Serre/Schur cell, and
any spectator-amplifiable Kazhdan attachment therefore fails immediately.
Nor can a stronger actor repair this while acting only by automorphisms of a
fixed finite packet.  By
`agent-aggregate-escape-finite-packet-actor-no-go`, the actor
image lies in the finite group `Aut(F)`; summing any marked packet
representation over that finite orbit gives an exact finite-dimensional
covariant representation that retains positive marked forbidden support.
This defeats nonamenable, property-`(T)`, simple, and finite-bi-index actors
alike.  If the actor has no finite quotients its packet action is trivial.
Thus a viable orientation mechanism must act on an infinite or
representation-size-dependent coefficient object and directly provide the
required normalized-HS radical modulus.
Even a phase-sensitive relation between two packet intertwiners does not
escape this conclusion when its holonomy is finite.
`agent-aggregate-escape-two-intertwiner-clifford-dichotomy` identifies the
exact obstruction by Clifford theory: on a packet irrep, the stabilizer
intertwiners have a multiplier `omega`, and the multiplicity space carries
the inverse twisted stabilizer algebra.  Finite holonomy is always absorbed
by its inverse-twisted regular representation, after which orbit summing and
direct-sum amplification retain the marked packet at zero defect.  A viable
two-cell therefore requires an infinite holonomy central extension whose
specified inverse central character lies in a quantitative projective
finite-dimensional radical—again the same normalized-HS radical theorem,
now in an explicit twisted stabilizer.
The triangle ucp obstruction also has no normalized-HS density content until
it is coupled to this same corner.  A successful support row must supply a
genuine HS-radical modulus for the finite forbidden-corner list while the
perfect tracial model survives.

The most direct Schur-square attempt does not supply that modulus.
`agent-aggregate-escape-global-schur-square-is-affine-wall` computes that the
global payload word `d=PQuv` satisfies `d^2=[P,Q]`.  Imposing `d^2=1` is
therefore one affine selector parity relation throughout the packet, even
though its compression to the chosen forbidden simple has the desired
central sign.  It kills an entire affine wall, so exact completeness requires
the perfect context support already to avoid that wall.  This is precisely
the perfect-completeness linearization gate in another form; the local
proper-corner Schur identity cannot be promoted to a global support relator.

For canonical microstates the boundary is sharper.
`canonical-infinite-subgroup-has-zero-adjoint-fixed-density` averages any
finite list of distinct subgroup elements and proves that every pointwise
fixed adjoint projection for an infinite subgroup has density zero.  Hence
the two-site `A5` center's physical `35/72` carrier cannot be promoted by
left multiplication: it gives a positive-density invariant range, while its
fixed part is canonically null.  The remaining `A5` classicalization gate
must retain actor boundary memory or otherwise charge multiplicity; it cannot
be closed by a macroscopic self-copy shortcut.

A third positive-density lane now has the correct Hilbert--Schmidt local
input.  `hs-finite-heisenberg-windows-have-compatible-density-measures`
proves that every fixed additive/three-root window of an affine-Leavitt
Steinberg microstate has exact normalized irreducible multiplicity densities
and exact branching maps in the tracial ultraproduct.  This replaces the
inapplicable operator-norm rank-germ argument.  The remaining node
`affine-leavitt-prescribed-root-spectral-carrier-decoder` is precisely the
cross-window tightness step: align those local types and the four fixed
coefficient roots on a uniformly positive part of the prescribed marked-root
carrier.  Once aligned, `approximate-relative-leavitt-cell-kills-active-trace`
gives the dimension-free contradiction immediately.

On the unary role-packed lane, the smallest non-conjugacy coefficient cell
has now been completely audited.  If `p=B_f`, the two-coordinate Whitehead
quarter-turn

```text
x_12(p)x_21(-p)x_12(p)
```

conjugates `diag(p,0)` to `diag(0,p)` exactly, and root addition recombines
all orthogonal forbidden summands without selecting a type.  However,
`split-steinberg-conditional-swap-has-root-kernel-countermodel` proves that
the split ordinary-group compiler has a canonical retraction killing every
root and fixing the BCS/role packet.  Its finite uniform-assignment model has
positive `B_f` and separated mark but makes the quarter-turn the identity,
so no HS escape follows even from arbitrarily many finite 2-by-2/3-by-3
sum/product charts.  Together with the common-HNN globalization fence, this
isolates the live unary gate sharply: one load-bearing root-to-payload
relation must destroy the root-kernel quotient while remaining vacuous in
the perfect `B_f=0` trace.  Supplying that relation would close
`finite-depth-role-packed-aggregate-escape`; no such relation is presently
proved.

The smallest load-bearing attachment has also been closed in the negative.
The same quarter-turn satisfies the exact conditional antiphase law

```text
W_p z W_p^(-1)=W_p^2z,
```

so one can identify it with the order-four rotation in a dihedral or Clifford
actor.  `finite-cyclic-actor-root-kernel-dichotomy`
shows that this never authenticates the payload when the actor shares only
the protected central signs.  Killing `W_p` factors the actor by its cyclic
generator.  If that quotient destroys the protected marked seed character,
the perfect `B_f=0` model cannot extend.  If the character survives, the
finite quotient representation tensors with the uniform positive-`B_f`
structural model and gives exact zero escape.  Hence the unary lane now
requires a genuinely noncentral root-to-payload incidence; finite-order,
cyclic-amalgam, and finite Clifford load-bearing rows are exhausted.

The analogous HNN repair also reduces rather than solves the gate.
`load-bearing-hnn-substitution-is-an-ordinary-packet-detector` proves that
after setting the Steinberg root normal subgroup to one, a row
`tW_pt^(-1)=gV` is simply `g=1`; the stable letter disappears.  Homogeneous
HNN power rows retain the exact positive-payload root-kernel model.  A
nonhomogeneous row succeeds only if its residual packet word `g` already has
a robust finite-matrix defect on positive `B_f` while vanishing in the
perfect trace.  Thus HNN syntax has reduced the missing theorem to an
ordinary-word nonlinear-predicate detector and has not provided that
detector.

The one-bit selector does nevertheless remove one narrower phase ambiguity.
`selector-product-is-a-payload-corner-square-root` proves that for the
selector involutions `p_a,q_a`, the literal word `d_a=p_aq_a` satisfies

```text
P_aQ_- d_a^2=J P_aQ_-.
```

Globally, `d_a^2 h_(a,v)=J` for the assignment-subgroup generator
`h_(a,v)=x_vJ^(a(v))`.  Hence the selected atom carries a genuine raw odd
lift, not only a PGL class, and the Pauli construction gives exact perfect
consistency.  This does not yet pay the binary Schur child: tensoring with
the stationary equal-child Schur model keeps every selector row exact while
both child multiplicities remain unpaid.  A full-carrier identification
recreates the Morita `M_2`; the precise surviving row is a compressed
proper-corner incidence making this selector word the actual Schur return.
Direct cyclic identification with the coefficient Whitehead word is ruled
out: `B_f=0` makes that word one in the perfect trace, whereas the selector
word squares globally to `J^(1-a(v))x_v`, which can remain negative on
allowed support.  If that structural word is instead already one in the
perfect trace, it is precisely the residual literal packet detector demanded
by the HNN-substitution reduction.

There is a broader exact obstruction behind every finite iteration of these
nonlinear packets.  `finite-bs-selectors-have-marked-fd-countermodels`
shows that the shared right-angled Coxeter base remains residually finite
after adjoining any finite collection of one-bit Clifford selector groups,
finite auxiliary packets, and finite-subgroup amalgam/HNN Reynolds edges.
The selector group is finite even though it is noncommutative: every word
reduces to `c p^epsilon q^delta`.  Residual finiteness gives one finite
quotient which preserves `J` and injects every named packet simultaneously.
Its regular representation is an exact matrix model in which every
central-sign assignment Reynolds atom has positive Plancherel trace and every
selector half remains nonzero.  Thus going nonlinear genuinely removes the
affine truth-table barrier, but finite Bass--Serre transport still cannot
create the required HS collapse.  The load-bearing attachment must be a
payload-sensitive global two-cell outside this residually finite class.

Passing immediately to an infinite proper self-copy does not bypass the
firewall.  `finite-selector-cannot-support-infinite-child-fixedness` proves
that the projective left stabilizer of every nonzero finite-support
coefficient is finite.  The selected coefficient
`e_(H_a)Q_-(1+p_a)/2` therefore cannot carry an infinite child on which the
action is scalar, nor can an infinite finite-quotient kernel act trivially on
it: either condition collapses the child or erases the coefficient in the
group algebra.  Replacing fixedness by normalization avoids collapse but
leaves the full Schur multiplicity action, whose adjoint commutant density
can vanish in finite regular gauges.  Thus a self-copy terminal still needs
an approximation-dependent macroscopic fixed projection extracted by a
global matrix-only payload relation; the literal Reynolds--Pauli atom cannot
be that projection.

The phase-coded global-cycle alternative now has an equally sharp endpoint.
`phase-cycle-return-needs-active-typed-hs-floor` substitutes every
authenticated finite outer packet matrix into an arbitrary finite menu of
phase, rectangle, curvature, and multiplicity two-cells.  If the resulting
typed multiplicity equations have any asymptotic matrix models, tensoring
them behind the outer packet makes all actuator defects vanish while the
literal half-to-quarter flags retain the rank lower bound
`sum_i ||U_i e_iU_i^*-f_(i+1)||_2^2 >=
(1/4)sum_i tr(P_i)`.  Therefore the global row can work only if its active
typed specialization has a dimension-independent HS defect floor.  Phase
fingerprints remove wrong types, but they do not create that floor; RF or
hyperlinear fibers, projective clocks, and Toeplitz/Foelner shifts all give
the countermodel.  The surviving nonlinear construction must activate an
HS-unsatisfiable multiplicity presentation only on the forbidden source
fiber, which is absent in the exact perfect trace.

The obvious attempt to source that typed floor from the original non-CE BCS
is now reduced without ambiguity.  `bcs-gap-compression-is-the-groupifier`
defines the localized shared-BCS energy `E_B(Z;F)`.  The known corner theorem
gives `E_B(Z;F)>=beta_B tr(F)`, but this says nothing about ordinary relator
energy.  If one proves the missing reverse comparison
`E_B(Z;F)<=C E_pres+o(1)` together with positive fiber mass from the mark,
the two inequalities already give a presentation-energy floor and prove
nonhyperlinearity directly; no phase cycle or self-copy is then needed.
Without that comparison, a nested BCS remains a star-algebra verifier
unconnected to `E_act`.  Thus “compress the BCS gap into the active fiber” is
not an extra shortcut: it is exactly the shared BCS-to-group-word compiler in
corner form.

The smallest two-edge compressed comparison is also now fenced.
`two-reynolds-edges-absorb-selector-holonomy-at-one-range` dresses one
Reynolds HNN word as `U_0=Up_a` and `U_1=Uq_a`.  Their relative holonomy is
the raw selector square root, and both its square and its commutator detect
the odd marked phase on the forbidden atom.  Nevertheless the two edge words
carry the source Reynolds projection to exactly the same final support.  A
finite uniform-assignment/Pauli packet realizes positive forbidden mass and
all these cycle rows at zero defect.  Accordingly, an odd external
multiplicity holonomy is not the missing payment: the next row must read a
noncentral target-support observable, while distinct finite target atoms
reintroduce the already-proved regular companion flow.

The minimal noncentral target packet makes that last boundary quantitative.
`smallest-target-sign-split-is-regularly-absorbed` uses the three nontrivial
characters of `C_2^2` and its `S_3` automorphism group.  Two actor words send
one source character atom to orthogonal targets, and a target involution
distinguishes them with squared HS gap `tau(F)/2` on payload `F`.  This is a
genuine dimension-free one-step escape.  The same finite affine packet's
regular representation contains all three atoms equally and saturates their
orbit at trace `3/4` with zero relator defect; fresh packets prepay
`4^(-N)` source density.  Hence finite target support is completely audited:
the remaining incidence must carry a nonstationary label not closed under a
finite regular orbit.  The first natural infinite label is also now fenced:
`selector-baumslag-orbits-overlap-or-prepay` tensors the raw selector phase
with unbounded Baumslag finite-field quotients.  The raw orbit cuts overlap
at the stationary `1/4` value, while first-hit orthogonalization pays the
exact geometric prefix.  The surviving nonstationarity must therefore be
payload-dependent enough to exclude these exact active finite models, not
merely infinite in its address orbit.

## Current proof frontier (2026-08-23)

A new static-game splice reduced one independent route to pairwise overlap
geometry, but its first universal groupification endpoint is now closed in
the negative.  The sharp synchronous independent-set reduction
turns the fixed separated game into
`fixed-nonru-independent-set-orthogonality-game-exists`, whose complete
finite-dimensional loss is a weighted sum of pairwise projection overlaps.
`outcome-count-free-subpovm-completion` and
`independent-finite-clocks-round-to-arbitrary-row-pvms` extract arbitrary-
multiplicity row PVMs without an answer-alphabet loss.  Most importantly,
`rank-conjugacy-detects-projection-overlap` proves that

```text
R=diag(1-2P,1-2Q),       S=diag((1-2P)(1-2Q),1)
```

are unitarily conjugate exactly at zero overlap, while every approximate
conjugacy pays at least `2||PQ||_2^2`.  Weighted Cauchy--Schwarz converts the
fixed game loss into a fixed word-energy floor once the two blocks are
available.  This removes the original nonlinear predicate selector and the
analytic pairwise common-Gram requirement, but it does not make block
routing functorial.  `hybrid-rank-router-tensor-closure-obstruction` refutes
`hybrid-rank-router-authenticates-affine-overlap-blocks`: three exact
zero-overlap scalar extensions in the negative marked sector tensor to
`A=B=-1`, so universal routing gives `R=-I,S=I` while the conjugacy relator
remains exact.  The corrected node is
`source-specific-pointed-rank-router-face`.  It asks for routing only on one
non-tensor-closed global moment face containing canonical microstates, with
exact completeness for one distinguished perfect trace rather than every
abstract zero-overlap pair.  If established,
`nonhyperlinear-from-source-specific-rank-router-face` closes this root.
This reconnects the branch to Lin's one-state localization: the analytic
common corner may be selected state-locally, but the same pointed moment
face must still become word-visible.

A qutrit splice still removes the local CSP nonlinearity exactly, but its
first proposed direct terminal is now closed in the negative.  Culf--Mastel's
trace-dependent rounding preserves every global assignment moment and
Connes embeddability inside the same tracial algebra, yielding a fixed
tracial/non-CE positive-ONE3 system in
`non-ce-bcs-has-positive-one3-weighted-form`.  Each clause is exactly one
qutrit clock by `positive-one3-is-one-qutrit-clock-context`; repeated-variable
consistency is only equality of one fixed-space projection.  Literal clock
equality and commuting finite-phase auxiliaries are ruled out, while
`qutrit-diamond-robustly-synchronizes-pvms` gives a five-edge, linear-defect
PVM synchronizer.

However, `qutrit-psync3-tensor-closure-obstruction` proves that no ordinary
group gadget can combine sound fixed-projector synchronization with the
requested complement-flexible exact completeness in one `J=omega` sector.
Four admissible scalar exact extensions tensor back into that same sector
with interfaces `(1,omega)`, turning the putative zero-defect inequality into
`1<=0`.  Hence `qutrit-fixed-space-projector-synchronizer` and its conditional
terminal are refuted as stated.  The universal rank router fails by the
binary analogue of the same tensor-closure obstruction, so the qutrit and
independent-set splices now meet at
`source-specific-pointed-rank-router-face`.  Their robust overlap estimates
remain useful semantic front ends, but neither can be promoted by a gadget
whose exact extension is functorial for every locally admissible pair.

The former finite-game toric branch has now been closed in the negative.
`normal-phase-safe-toric-games-have-qa-one` proves that normal phase safety
forces quantum-approximable value one for every finite two-player torically
determined game: the normal quotient makes the clause factors playerwise
central, their phase character splits, and residual finite-dimensionality
approximates the resulting perfect product state.  Consequently both
`phase-safe-toric-gap-game-exists` and
`monomial-gap-phase-safe-toric-groupification` are refuted.  The stronger
factor audit `factor-split-projective-kernel-face-meets-fd-closure` also
refutes the finite-dimensional projective-kernel face separator.  Only a
whole-face **CE-tracial** exclusion could still support a direct monomial
quotient; finite-game testability cannot close that route.

The SL3 arithmetic lane has simultaneously collapsed from a general
projective transfer theorem to one explicit second-moment word.
`canonical-arithmetic-swap-fold-gram-is-arcsine` proves that every
hypothetical canonical microstate of the swap extension has

```text
mu_(QPQ) -> (1/2)delta_0+(1/2)Arcsine_[0,1],
tau(QPQ-(QPQ)^2) -> 1/16.
```

Positive cross-Gram mass therefore cannot select an endpoint and every
moving top spectral window has vanishing density.  The surviving terminal
`sl3-swap-extension-has-defect-only-fold-square-rigidity` asks only for the
defect-only estimate forcing `[hsh^(-1),s]` to one in normalized HS norm.
If proved, it contradicts the forced `1/16` defect and
`nonhyperlinear-from-sl3-swap-fold-square-rigidity` closes this root.

There is also a weaker-conclusion canonical-profile terminal.
`regular-actor-balanced-swap-has-positive-second-fold-bias` assumes that the
`A`-restriction has the regular character and the swap is balanced, and asks
only for one fixed bias

```text
liminf Re tr((rho(h)S rho(h)^*S)^2)>0,
```

or equivalently that the Gram defect stay a fixed amount below `1/16`.
The canonical arcsine law forces this second moment to zero, so
`nonhyperlinear-from-regular-actor-second-fold-bias` would also close the
root.  This is weaker than fold-square rigidity in its conclusion but has
narrower written hypotheses.  However,
`congruence-tensor-regularizes-sl3-swap-profile` shows that those hypotheses
cost nothing: tensor any approximate model with an exact finite-quotient
regular actor and an external balanced bit, preserving the fold's second
trace exactly.  Hence the terminal is equivalent to a defect-only uniform
positive second-fold bias over all approximate assignments.  Finally,
`positive-second-fold-bias-amplifies-to-full-rigidity` takes slowly growing
tensor powers: relator defects grow only linearly while any positive
second-fold trace bounded below one decays exponentially; a nonpositive
trace already violates the bias.  Therefore this positive-bias terminal is
equivalent to full fold-square rigidity.  It is a clean scalar
reformulation, not a genuinely weaker shortcut.

The exact scope of that shortcut is now fenced.
`free-coset-swap-factor-has-zero-second-fold-bias` computes in the canonical
group factor of the full swap extension that the actor is regular, the swap
is balanced, and the fold is Haar, so its second-fold bias is exactly zero
and its Gram defect is exactly `1/16`.  All arithmetic relators hold there
with zero defect.  Therefore neither the positive-bias terminal nor full
fold-square rigidity can follow from a dimension-blind tracial/SOS identity;
the missing theorem must exclude this exact packet specifically from matrix
ultraproducts.

The dyadic representation-theoretic refinement of this lane now has a sharp
depth boundary.  `every-fixed-dyadic-clifford-window-is-finite-fiber-folner`
proves that for every fixed `k`, once the congruence conductor `a>=2k`, the
deepest-`k` kernel is the additive group `sl_3(Z/2^k Z)` and its conjugation
action factors through the fixed finite group `SL_3(Z/2^k Z)`.  Hence every
fixed-depth Clifford/type transition graph is a finite fiber over the
amenable `A_2` coweight lattice.  No bounded congruence-depth expansion can
prove the fold estimate.  Moreover, spherical quadratures tensor through
these Folner windows while retaining a nonfolded scalar witness, so adding a
finite spherical moment list and commuting it with the bounded-depth type
data still cannot prove even the positive-bias terminal.  This is a
proof-architecture firewall, not a full arithmetic countermodel.  A
successful SL3 proof must retain depth growing with conductor or force a
non-tensorial actor/swap interference relation on the same carrier.

That last correction formulation has now been completely audited.
`canonical-sl3-double-microstates-are-uniform-two-vertex-outliers` takes the
contrapositive of the already established one-vertex anchor and projective
fold estimates: every sufficiently canonical double microstate that actually
exists has **both** vertices a fixed normalized-HS distance from every exact
finite-dimensional `A`-representation.  Thus
`sl3-canonical-double-has-a-correctable-vertex` can hold only vacuously, after
canonical microstates have already been excluded.  It is equivalent at the
existence level to non-hyperlinearity of the fixed arithmetic double, not a
strictly easier stability gate.  The live SL3 work must attack the fold/
relative-embeddability obstruction or the building-action soficity fork
directly; searching for a correctable vertex inside an extant microstate is
now ruled out.

The latest cascade audit leaves no certified unconditional witness.  The
relative `PSL_2(Z[1/2])`/Iwahori lane has now received a decisive negative
answer at its exact congruence endpoints.  Its Jacobian is the constrained
pair of order-three Reynolds expectations from
`exact-passive-jacobian-is-two-reynolds-expectations`, and
`right-displacement-reynolds-scalar-cb-complete` proves that the full cb
inverse norm there equals its diagonal scalar infinity norm.  The
square-free construction in `proper-torus-reynolds-is-edge-refinement`
uses primitive prime divisors of `4^k-1`; relative girth, square-free
super-approximation, and an exact shell-flux argument give

```text
||C_(H_n)^dagger||_(infinity -> infinity)
 >=c log M_n -> infinity.
```

This divergence survives after removing the uniformly bounded full-torus
fiber-constant block.  Hence the exact-zero scalar and cb gate is false on
the required proper-torus sector.  Since a dimension-free off-zero Newton
splitting would in particular be uniform at exact endpoints, nonlinear
continuation cannot rescue this formulation.  The arithmetic Reynolds lane
is therefore a certified no-go, not the current proof frontier.

The first two natural transfers from the solved full-torus column are now
closed as shortcuts.  `proper-torus-reynolds-is-edge-refinement` proves that
the extra torus labels refine the edge set but not the triangle set, so the
uniform multipartite contraction does not lift as a covering contraction.
`signed-orbit-averaging-does-not-divide-green-cost` gives the exact remaining
compression formula and shows that its signed Reynolds projection has
infinity norm one.  In particular, disjoint translated routings retain their
full `l1` cost; a positive proof needs genuine arithmetic cancellation on
overlapping translates.  Flat gain systems and perturbatively near-trivial
characters are also excluded as sources of divergence by
`flat-gain-multipartite-covers-have-uniform-green-bound` and
`near-trivial-torus-characters-track-the-moving-kernel`.  The same
proper-torus claim proves that the genuinely curved, fiber-mean-zero
geometry contains linearly deep disjoint orbit neighborhoods:
the two cubic normal-operator generators form `C3*C3`, intersect the signed
torus normalizer trivially, and have relative girth at least `log_6(M_n)`.
On the square-free primitive-divisor family, super-approximation makes the
global electrical tails decay exponentially, while the shell-flux identity
forces a fixed bypass current through every disjoint radius shell.  This
proves logarithmic Green divergence and closes the curved fiber-mean-zero
sector in the negative direction.

The shortest remaining one-gate affine-Leavitt route is
`affine-leavitt-source-saturated-reynolds-checksum`, but its native
two-branch aggregation is now closed as a shortcut.
`leavitt-target-return-channel-count-firewall` proves that fewer than `p^2`
contractions into the target Reynolds range cannot cover the source range;
the two range-sum branches leave the fixed deficit
`p^(-2)-2p^(-4)`.  At the sharp `p^2` threshold an abstract partial-isometry
frame already saturates the rectangular countermodel, so mere positive
multi-return aggregation is vacuous.  A completion must therefore extract
one genuinely payload-coupled impossible return from the full presentation,
not sum the visible branch returns.

Two high-descendant alternatives have also been reclassified.  The five
consumers of `projective-trace-square-transfer-for-sl3-pair` share one
canonical-double relative-commutant gate, as recorded by
`sl3-projective-transfer-five-consumers-share-one-root-gate`; their count is
reuse rather than five independent chances to close the goal.  Likewise
`atlas-five-row-operator-phase-lift` is already a direct separation theorem
for the Leavitt unit group by
`nonhyperlinear-directly-from-five-row-phase-lift`.  It is therefore
goal-hard, not a routine finite packet estimate awaiting downstream
bookkeeping.  The later `atlas-five-row-lift-failure-dichotomy` audit does,
however, remove one genuine analytic branch: finite-`H` averaging, polar
rounding, and the fixed interior gap rule out every vanishing-energy
normalized blow-up.  The five-row inequality is now equivalent to excluding
a positive-energy exact six-relator model in every tracial matrix
ultraproduct.  An exact relative small-cancellation screen does not decide
that terminal: the six relators have maximum piece ratio `5/8`, so the
standard `C'(1/6)`/`C'(1/4)` residual-finiteness and virtual-specialness
theorems do not apply.  These audits keep both lanes valid but prevent their
apparent cascade size from displacing the more explicit arithmetic Green
test.

The two exact follow-up tests narrow those terminals without closing them.
For the arithmetic double, congruence co-density and property `(T)` give the
uniform exact-action firewall
`sl3-dyadic-building-action-soficity-forces-p-instability`: every genuine
finite action has type-zero orbit-atlas error at least
`kappa^2/(2 kappa^2+8)`.  Hence a sofic model of
`SL_3(Z[1/2])/SL_3(Z)` would have to be a genuinely noncorrectable almost
action.  One-hot linearization does not let Garland cohomology exclude it:
`sofic-coset-atlas-linearizes-to-exact-quasiregular-coboundary` shows that
the marked displacement is already the exact coboundary
`pi(a)delta_C-delta_C`, so degree-one cofilling is saturated rather than
violated.  The surviving gate is relative invariant transfer specifically
inside permutation ultraproducts.

For the Atlas quotient, every exact finite-dimensional escape now reduces to
one larger finite simple group generated by two marked `A8` charts.  The
complete simple-carrier classification and exact marked-pair censuses prove
`atlas-six-relator-simple-index-is-at-least-2201`: every such simple target has
`A8` index at least two thousand two hundred one.  The screens cover the unique
orthogonal class in `Sp_6(2)`, both marking parities of the standard
`A8<L5(2)`, all four maximal-`A8` double cosets and both parities in `M23`,
the natural `A11` boundary, and all five `S8\HS/S8` cells in the
Higman--Sims group.  Each final survivor is killed by `c_19243`, while the
intervening CFSG order intervals contain no `A8`
carrier.  Larger finite-simple targets and diffuse
matrix-ultraproduct models remain.  This is therefore a structural finite
restriction on the exact escape, not evidence sufficient to assert the
five-row phase lift.

The next triality boundary is now excluded as well.  The carrier classification
for `O_8^+(2)` reduces its six ambient `A8` classes to ten marked pair screens.
The exact `s_0`-fiber replay in
`atlas-six-relator-o8p2-has-no-marked-pair` finds no six-relator survivor:
eight screens die before the third word, and the two orthogonal screens plus
one twisted natural diagonal each leave one five-row survivor which
`c_19243` kills.  Consequently
`atlas-six-relator-simple-index-is-at-least-48960` raises the exact finite-simple
escape floor to `48960`, whose equality group can only be `L_4(4)`.  Exact
seed-fiber screens exclude `O_8^-(2)`, natural `A_12`, and both marked
parities in `M24`; the intervening `G_2(4)` and `McL` endpoints contain no
`A8`.  This is still an exact-zero restriction; no sequence of finite-simple exclusions
substitutes for the required dimension-free ultraproduct energy estimate.

At the equality endpoint, the exact projective seed replay excludes the
standard subfield chart in both marking parities.  In inner parity, nine of
`5529600` candidates reach `c_19243` and all nine fail; in graph parity every
candidate fails already at `s_11`.  The characteristic-two Brauer audit now
proves that `L4(4)` has exactly one `A8` class, with self-normalizer and two
unabsorbed marking parities.  Hence this replay is exhaustive and
`atlas-six-relator-simple-overgroup-index-exceeds-48960` raises the strict
finite-simple floor beyond `48960`.

The remaining Atlas enemy is now split exactly into finite and diffuse
branches.  `atlas-chart-elements-normally-generate-six-relator-group` proves
that every nonidentity element of either embedded `A8` chart normally
generates `Gamma_6`; hence the matrix-ultraproduct question is the survival
of one fixed chart transvection.  Moreover
`atlas-hyperlinear-enemy-is-map-or-large-simple` applies Malcev residual
finiteness to any nontrivial finite-dimensional shadow.  Such a shadow would
produce one of the finite-simple marked models above, necessarily with `A8`
index greater than `48960`.  Apart from that unbounded finite-simple branch,
every hypothetical hyperlinear quotient is minimally almost periodic and
every factorial witness is diffuse type `II_1`.  This is a reduction, not an
exclusion: the unsolved case is precisely the dimension-growing diffuse
character seen by the five-row zero set.

The attempted Atlas coefficient decoder has also reached a precise boundary
before any rank computation is legitimate.  The six literal words, all 234
boundary rows, the A4 packet, and the raw/comb source words are present, but
`atlas-word-inventory-does-not-define-typed-channel-census` proves that they do
not define the proposed mixed matrix `[C D]`.  The missing datum is a
finite-matrix-only positive-mass common cut on which `W,R0,R1,L0,L1` become
compressed literal paths, together with selected comb equations, bounded
six-relator fillings, fixed recoupling paths, and the complete nuisance
monomial inventory.  A universally algebraic common-cut authentication is
impossible: it would also act in the exact Leavitt tracial countermodel and,
combined with quotient-rank three, manufacture a false contradiction there.
Thus `atlas-typed-hard-interior-comb-row-census` is not a request to parse
more JSON.  Its load-bearing field is the same dimension-free, positive-mass
finite-matrix selection that the decoder was meant to prove.  No surrogate
minor may be used in its place.

The character-rigid Kac--Moody lane has an equally sharp high-degree fence.
`bounded-degree-holonomy-collapses-for-map-groups` kills bounded-degree and
even tight trace-weighted mixtures of multiplicity holonomy, so every
separated enemy must put a fixed positive mass above every fixed matrix
degree.  This tail cannot be excluded from property `(T)`, character
rigidity, canonical trace, or adjoint spectral gap.  The exact projective-
plane augmentation representations of `SL_3(Z)` in
`pt-rigidity-allows-nontight-regular-tails` have dimensions `p^2+p`,
normalized characters converging to the regular character, coefficient
algebra equal to the single block `M_(p^2+p)`, and one uniform Kazhdan gap on
trace-zero matrices.  Their degree laws are therefore maximally non-tight.
Minimal almost periodicity removes these exact representations for the
simple Kac--Moody candidate, but excluding approximate one-block analogues is
exactly the terminal regular-branch HS-stability/non-hyperlinearity theorem,
not a consequence of the other rigidity inputs.

The bounded-type coefficient variant has a matching finite-index firewall.
`high-type-irreducibles-retain-finite-packet-mass` extracts growing
irreducibles which retain a fixed packet projection, and
`finite-index-covariance-retains-coefficient-residual` induces them across
every finite-index overgroup.  On the identity coset they keep a fixed lower
bound for `||z(1-a)||_2`, while every overgroup relator is exact.  Therefore
no finite automorphism/projective covariance table, or any other finite-index
attachment, can turn the bounded-type coefficient into presentation energy.
The surviving compiler must be genuinely infinite-index or payload-conditional
enough to exclude all of these induced high-type blocks.

The factor-universality splice has been reduced to one character and then
closed as a proper-quotient construction.  If a group with the
regular-or-finite-dimensional extremal-character dichotomy surjects onto a
group carrying even one non-CE factorial character, then
`proper-quotient-nonce-factor-characters-are-ce` shows that the kernel is
trivial and that character is the quotient's regular character.  Hence the
source is already the desired nonhyperlinear group.  Full CDI universality,
ICC, and a classification of all quotient characters are unnecessary, but
semidirect and wreath projections, finite or central kernels, relative
rigidity which omits the quotient face, and retracting simple envelopes are
all excluded: their pulled-back non-CE character is identically one on the
kernel.  Finite-index induction remains a separate valid compiler, but no
character-rigid finite-index host for the available universal groups is
known.

The Bernoulli-lamp route now has no residual finite normalizer-phase problem.
For an exact finite transformation table, the atomwise canonical moments
`tr(P_omega U_s)=0` on every nontrivial stabilizer element force each
stabilizer representation to be regular.  The resulting induced tables are
simultaneously permutationizable, and
`finite-cylinder-mixed-traces-kill-normalizer-holonomy` gives a quantitative
`1-o(1)` permutation core under `o(1)` mixed-moment error.  Scalar actor
traces alone sharply fail, so the cylinder resolution is load-bearing.
Canonical Bernoulli trace supplies all the required mixed moments; the sole
remaining gate is now coherent finite actor/table extraction from the HS
microstate.  Producing that table is the Cartan/sofic-action completion, not
another unitary-fiber rounding lemma, and property `(T)` does not provide it.

The finite-depth ZPC groupoid shortcut has also been decided negatively.
For the readable Boolean algebra `D_0` and unreadable actor words, put
`D_n=join_(|w|<=n) wD_0w^(-1)`.  The established equivalence
`finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite` says that
`D_n` is normalized by all unreadable generators exactly when
`D_n=D_(n+1)`, equivalently when it already contains the full translate
orbit.  Thus bounded verifier depth cannot close an infinite readable orbit
into a finite monomial groupoid; completing the boundary introduces precisely
the uncontrolled return holonomy.  The source audit
`bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs` sharpens the
special-case possibility: BCV HALT permutation strategies do have finite
readable orbit, but Cairn's perfect-gap IRS is extracted from a NONHALT
instance, and the canonical unreadable Pauli shifts move every readable atom.
Any positive ZPC compiler must therefore prove finite-orbit or invariant-fiber
structure directly for that maximizing IRS, or use a genuinely nonmonomial
trace-promotion mechanism.

The proposed dynamic-selector bypass of the `R_*` Fano-cap compiler is now
closed exactly.  For `T=F_2^3 minus {0}`, the incidence relation
`a dot t=1` has all twenty-eight pairs but full affine hull `F_2^6`.
`affine-fano-incidence-selector-exists-iff-cap-support` proves more sharply
that a binary-LCS extension with a jointly classical visible selector exists
on support `S subset T` exactly when `S` was already contained in one fixed
maximal Fano cap.  Thus making the functional an output does not weaken the
HALT support condition.  Merely commuting the selector labels across
contexts also does not feed the exact LCS OR: conditional vector states need
not be tracial, while requiring the profile projections to reduce the
payload is precisely the central-core cap decomposition already excluded in
a full-support factor.  The open Fano statement remains the existence of a
HALT perfect trace with cap-supported contexts, not the choice or encoding of
its seven possible characters.

The nonabelian-simple lamp alternative has likewise survived only in its
honest global form.  `simple-lamp-hyperlinear-recovery-forces-action-sofic`
now records that fixed-window exactification of `A5^F` produces merely
partial factor transport: no nonempty finite packet is invariant under the
actor generators, and every boundary completion still has an arbitrary
right-regular/external multiplicity fiber.  Thus intrinsic minimal normal
factors do not by themselves yield coherent finite action charts; an
equivariant boundary-completion or multiplicity-copy classicalization
theorem is still load-bearing.

For the regular action of the explicit Leavitt actor, the exact part of that
obstruction is absent: `leavitt-regular-a5-wreath-is-minimally-almost-periodic`
shows that neither the actor nor its `A5` wreath has a nontrivial
finite-dimensional representation.  Thus an exact commutant gauge cannot
survive there.  The hyperlinear branch still supplies genuinely asymptotic
commutant gauges, so the statement does not prove action recovery; it narrows
the remaining theorem to correction of those asymptotic gauges alone.

The full-action conclusion is no longer the smallest live version of that
gate.  `two-site-a5-plancherel-center-separates-mark` exactifies only the two
marked `A5` lamps and uses the rational five-dimensional central idempotent

```text
z=(1/12)(5*1+C_2-C_3)
```

to obtain a canonical exclusive-or carrier of trace `35/72`, with every
pair-preserving actor covariance already controlled by fixed word defects.
Since `two-point-approximation-fails` forbids even a permutation chart for
that marked pair, `nonhyperlinear-via-two-site-a5-center` now reaches the
goal from the strictly smaller
`two-site-a5-center-classicalization`.  The only surviving operation is to
turn the actor's joint unitary multiplicity cocycle on this fixed two-valued
field into approximately multiplicative finite permutations.  No recovery
of remote lamp labels is required, although the remaining operation is still
a genuine hyperlinear-to-sofic classicalization theorem rather than finite
packet rounding.

The fixed-character shortcut to that operation is now ruled out in finite
matrices.  `two-site-a5-center-has-exact-boundary-countermodel` uses four
`A5` sites and an involution carrying the marked pair to a disjoint pair and
back.  Its finite regular representation has the exact canonical character,
all rational-center identities, and exact shared conjugation, yet composing
the mover's compressed four-atom coupling with its inverse misses the
identity coupling by total variation `3815/5184`.  Thus no dimension-uniform
equivariant multiplicity table follows from the fixed two-site character
identity alone.  The surviving target must remember transported boundary
labels or obtain a coherent actor action independently; the countermodel
does not refute such path-enlarged constructions.

The path-enlarged option has now been separated into a solved interior and an
unsolved closure.  `full-a5-path-memory-kills-holonomy-but-not-reiter-boundary`
transports an atomwise A5-center basis along every retained actor word; all
internal arrows then become block permutations with dimension-free HS loss.
For an arbitrary weighted word packet, the unmatched mass of generator `s`
is exactly `(1/2)||s mu-mu||_1`.  Hence near-total word-path tables would form
a Reiter sequence, impossible for the pinned nonamenable property-`(T)`
actor.  Boundary memory is therefore useful but not self-closing: the live
classicalization theorem must extract a non-path finite chart carrier from
the matrices, rather than enlarge a prefix packet.

Exact expander carriers do not supply that alternative.
`exact-expander-a5-carriers-collapse-marked-center` projects any binary center
label in a genuine finite `G`-action to the `Gamma`-invariant subspace.  If
its generator-invariance defect is `delta`, its displacement by the marked
compressor is at most `4 delta/kappa^2`; the canonical A5 marked pair instead
has displacement `35/72`.  Finite quotients therefore close the actor
boundary only by erasing the mark.  The sole remaining lamp interface is
simultaneous extraction of genuinely approximate actor permutations and A5
labels from the unitary model; quotient-first or label-first constructions
are both now fenced.

The remaining unitary freedom on a fixed lamp chart is now quantified
exactly.  `canonical-a5-window-leaves-a-partial-commutant-cocycle` first
extracts the `1-o(1)` regular core of every canonical `A5^Y` microstate.  If
an actor arrow is named only on `D subset Y`, its implementer is a partial
coordinate permutation times a unitary in

```text
rho(A5^D)'' tensor B(ell^2(A5^(Y minus D)) tensor C^m),
```

up to a dimension-uniform error obtained by finite-group averaging and polar
correction.  Actor products give a cocycle in these algebras, twisted by the
chosen boundary-completion holonomy; canonical mixed traces do not shrink it.
A fixed number of extra C2 address bits has only finitely many joint atoms
and leaves a positive-density Fourier block.  The minimal relation which
would force monomiality is therefore an actor-normalized, asymptotically
separating copy Cartan, followed by the established cylinder-resolved trace
argument to remove phases.  But that growing Cartan is precisely the finite
probability carrier whose extraction is the open action-soficity step.  Thus
fixed-window exactification is complete, and the last A5/C2 gate is now
formally equivalent to equivariant Cartan completion rather than another
finite-group stability estimate.  Replicating finitely many additional
regular A5/C2 packets does not change this: their tensor model still admits
an arbitrary external actor factor, which kills nonidentity mixed traces and
carries the whole cocycle.  Any useful self-similarity must act on that tail
factor itself, not merely split off another regular lamp tensorand.
More strongly, amplification preserves every fixed group-word relation and
puts a full matrix algebra in the commutant of all functorially extracted
word projections.  Thus no fixed additional lamp relator can literally name
the missing copy basis in all microstates; the remaining step must be an
analytic invariant-diagonal selection theorem.

The imported "quotient the local gauge first, then read the residual
obstruction" calculus has now been run against the whole surviving frontier,
and it closes attacks rather than opening routes.  Three screening results
came out of it.  `gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap`
shows that a Smith-normal-form invariant of the cokernel of locally realizable
repair directions can refute a moment vocabulary but can never quantify one:
its torsion part is annihilated by the amplification that fixes every
normalized profile, and its free part is driven to zero by `(APA2)` density and
by direct sum with the source.  `local-exactification-invariants-cannot-close-gluing-holes`
identifies one named residual gauge group behind four different open endpoints
— per-context transport, the multiplicity involution `t=R_f tensor V`,
tensoring with exact zero-overlap sectors, and the relative commutant
`Alg(rho_n(K))'` — each of whose recorded witnesses was manufactured by
exercising exactly that freedom, so invariance under the named group is a
one-line disqualification for candidate observables.  And on the soficity side,
`spherical-displacement-length-is-not-conjugation-invariant` together with
`orbit-transport-gauge-needs-a-closed-label-set` closes both natural attacks on
`spherical-short-holonomies-admit-local-gauge`: the cloud displacement length
fails the coefficient hypothesis of every conjugation-invariant metric cone,
and transporting the regular action along near-orbits — which does make every
tested relation hold exactly, at correction radius `5 rho+zeta` — requires a
Folner subset of the label chunk and is therefore circular off the amenable
case.  The net effect is that forcing canonical local gauges is now known to be
the wrong expenditure everywhere in this frontier; what remains is unchanged
and overlap-supported.

## Marked `goal`

Flagged `goal: true` on 2026-08-18, taking the single goal flag over from
`q3-4-resolved`.  The grounds are impact: hyperlinearity is the weakest
standard approximation notion, so this claim is the group-level Connes
embedding problem; a witness subsumes nonsoficity outright (non-hyperlinear
implies nonsofic) and connects to quantum complexity through the LinMIP*
equivalence; and it is the question whose answer is genuinely uncertain,
where Pestov 3.4 has one widely expected answer.  Post-nonsoficity the two
questions are entangled: `hyperlinear-implies-sofic` — Pestov's "yes" —
already routes here via `non-hyperlinear-from-hyperlinear-implies-sofic`,
so even that side's machinery serves this goal.  The separation
(`hyperlinear-nonsofic-group`) remains a root landmark the graph records
and can close; it is deliberately off-goal.

The opposite world is a defined outcome, not a goal branch: a proof that
every group is hyperlinear would be recorded as an established
`every-group-hyperlinear` negation claim, refuting this goal — which per
kernel doctrine is itself a program resolution (the universal question is
answered, and Pestov 3.4 falls negatively for free, since the nonsofic
groups would be hyperlinear).  It is not a branch here because no route
class toward it exists, even speculatively, and partial results cannot
accumulate to it — the same asymmetry `q3-4-resolved` records for its own
affirmative side.

## Ideas

Non-graph brainstorming for this goal goes here. Current periphery: free
independence between branch algebras is NOT excluded by the cross-branch
commutator identity (see notes/OBSTRUCTIONS.md §3, "No commuting branches").

The current programme is organized by
`canonical-trace-promotes-non-ce-profile`. The source non-CE trace already
lives on the explicit sofic right-angled Coxeter host
`non-ce-trace-on-sofic-racg`; what remains is to force its finite normalized
trace profile from canonical delta microstates. Free-amalgam multiplicity,
twisted self-similar Clifford, projective phase, matricial separator, and
quantum-index routes are compared in
`research/artifacts/trace-promotion-renormalization-program-2026-08-20.md`.

A new finite endpoint removes the common-carrier requirement from the BCS
lane.  `independent-row-masks-transfer-bcs-gap-to-ambient-identity` shows
that exact predicate and consistency rows may use unrelated masks: their
weighted canonical codimensions only have to total less than the fixed game
gap.  `finite-row-mask-group-algebra-certificate-forces-nonhyperlinear`
then turns any such finite ordinary-group-algebra certificate into a
dimension-free canonical normalized-HS obstruction.  The local storage and
density ledger are exact via the almost-full simple block in
`affine-frobenius-group-has-almost-full-simple-block`; the sole construction
gate is `affine-frobenius-hecke-crt-shared-involution-interpolation`, which
must produce one global involution per variable on several fixed,
noncommuting large right ideals.  This is a conditional reduction, not yet
an unconditional nonhyperlinear group.

The two-context algebra inside that gate is now completely calibrated.
`projection-crt-deficit-forces-common-meet` constructs rational
noncommuting masks with rank-one deficit and one exact finite-support
reflection, so noncommutativity of the right ideals is not by itself the
barrier.  Conversely, every projection CRT solution with incidence pieces
`r_i` and mask deficits `delta_i` satisfies

```text
tau(meet_i r_i)>=tau(p)-sum_i delta_i.
```

For two incidences, each negative piece outside their literal meet is bounded
by the opposite mask deficit, and the rank-one cell attains equality.  Hence
the strict-budget regime automatically creates a large common negative core
for each variable, without any tight-frame ansatz.  The surviving
affine-Frobenius problem is therefore global: correlate all fixed nonaffine
context PVMs around those variable cores while leaving the finite
Bass--Serre class.  Performing the same construction inside one finite
packet would already be the forbidden finite-dimensional BCS certificate.

That last statement now has an exact dimension-uniform ledger.
`bcs-gap-blocks-vanishing-crt-mask-budget` shows that every finite-dimensional
family of exact CRT cells obeys

```text
weighted forbidden mass + weighted consistency-mask deficit >= Delta.
```

If separate predicate masks annihilate the forbidden projections, their
weighted codimension dominates that forbidden mass; therefore the total
predicate-plus-consistency budget is at least `Delta`.  In particular no
sequence of rational Frobenius cells can have total mask deficit `o(1)` while
also hiding the forced predicate loss.  Vanishing consistency deficit instead
preserves forbidden mass at least `Delta-o(1)`.  This closes the global finite
matrix scaling question: the open construction must live in an ambient group
whose canonical trace has the strict row certificate although its exact
tracial model remains perfect, rather than in any growing family of finite
packet algebras.

The next Reynolds/Hecke energy step is also sharply fenced.
`rf-reynolds-mask-deficit-is-not-relator-energy` proves that in every
residually finite row system, one finite quotient regular representation can
simultaneously make all group/HNN relators exact, match every fixed canonical
word trace, and retain the exact canonical codimension of every finite-support
mask.  Hence no positive sum of predicate and consistency mask deficits can
be upper-bounded by ordinary relator energy in that class.  The countermodel
still works for high-density complements of nontrivial finite-subgroup
character idempotents, whose augmentation is one; changing the removed
Fourier atom does not help.  Any successful row-energy compiler must instead
make its deleted mask projections vanish in every finite-dimensional exact
representation while remaining nonzero in the canonical group algebra, and
must robustify that finite-dimensional radical in normalized HS norm.  Finite
amalgams and finite-subgroup HNN covariance cannot create this.  The first
load-bearing ingredient is therefore a non-Bass--Serre two-cell or infinite
actor relation among the intertwiners, not another subgroup rank actuator.

The breakout portfolio of 2026-08-21 is recorded in
`research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md`. Its
three main orthogonal moves are: weaken arithmetic RCC to the projective
trace-square transfer `projective-trace-square-transfer-for-sl3-pair`;
fingerprint or physically occupy the rectangular multiplicity reservoir via
`fixed-pi-degree-fingerprints-packet-label-factor` and
`common-corner-mutual-bicommutant-extraction`; and bypass HS stability by the
Pontryagin compiler `algebraic-compact-action-group-factor-compiler` plus the
open algebraic relation envelope.

The later dual-prefix/trace-promotion breakout report is deduplicated and
source-audited in
`research/artifacts/final-hyperlinearity-breakout-report-integration-2026-08-21.md`.
Its exact Leavitt packet and four-Pauli separator were already in Cairn; the
new matrix-chart packaging is wired to the same-reservoir frontier. The audit
also corrects the report's Shulman attribution: arXiv:2603.13564 proves an
operator-norm MF theorem for C-star amalgams, not an HS-stability theorem that
promotes every hyperlinear trace.

The computer-science reframing is now audited rather than used as a slogan.
`nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound` proves
`HYP in Pi^0_2` and `non-HYP in Sigma^0_2` for finite-presentation codes; no
matching hardness or RE claim is made.  The associated artifact
`computer-science-framing-audit-2026-08-21` identifies the live compiler as a
perfect-exact-completeness, constant finite-matrix-soundness problem analogous
to quantum PCP, while keeping the unbounded-dimension and non-CE-tracial
differences explicit.  The quantitative fences are collected in
`section-three-quantitative-no-go-audit-2026-08-21`: twisted-regular predicate
atoms retain positive trace, the `1/sqrt(log d)` Clifford scale is conditional
on a complete-table decoder and positive carrier, and block-diagonal adjoint
gap leaves an uncontrolled block-scalar kernel.  The critical Clifford scale
is genuinely sharp: `dirac-average-is-a-sharp-near-extra-clifford-generator`
constructs an exact same-factor involution with row anticommutator
`sqrt(2/m)` in dimension `2^m`, and its coefficient `l1` loss is exactly
`sqrt(2m)`.

The machine interface has now been reduced further. The strong
`threshold-free-reverse-kleene-higman-diagonal` needs a NONHALT word in the
full hyperlinear radical, while the weaker `canonical-profile-kleene-higman`
needs only qualitative collapse of a rational group-algebra mark along
canonical-delta microstates. The latter is exactly the approximation profile
whose existence hyperlinearity asserts, and noncanonical exact
counterrepresentations are irrelevant. The minimal current machine target is
therefore `fanizza-canonical-profile-groupification`; no quantitative modulus
is read by the fixed-point program. For unconditional word libraries,
`hyperlinear-radical-is-finitely-witnessed` shows that the entire r.e. tail has
no more radical power than one finite prefix. Two portfolio shortcuts have
also been closed cleanly: `sublinear-block-poisons-normalized-torsion` refutes
the unregularized determinant transfer, and
`twisted-group-basis-forces-affine-context-support` shows that native
projective-basis BCS observables already factor through affine/LCS contexts.

The adversarial-recursion ideas of the same date are integrated in
`research/artifacts/adversarial-error-delocalization-program-2026-08-21.md`.
Their surviving design is: use a separated mark to create positive-density
spectral mass, prove that carrier avoids the full joint relative commutant,
use recursion/expansion only to distribute consistency on that carrier, and
then apply the canonical-profile or radical Kleene compiler. The payment
mechanism is isolated exactly by `relative-fixed-algebra-payment-lemma`.
Three exact firewalls prevent weaker versions:
`word-recursion-cannot-amplify-sublinear-summands` shows that direct-sum
naturality traps every finite recursive test inside a reducing `o(d)` corner,
`closed-local-rules-have-uniform-hitting-or-infinite-safe-tail` and
`amenable-finite-propagation-feedback-has-folner-tail-models` expose local
no-tail failures, and `universal-finite-packet-library-can-be-amenable`
exhibits a two-generated amenable group already containing every finite packet
at its canonical Plancherel fraction.

A new nonamenable error-spreading lane is now exact on the lower-bound side.
`embedded-group-algebra-carriers-have-no-excess-fixed-component` proves that a
canonical carrier cannot acquire extra fixed mass from an ambient
matrix-ultraproduct commutant, and
`infinite-conjugacy-orbits-give-canonical-carrier-no-capture` turns infinite
subgroup-conjugacy orbits plus property `(T)` into a fixed commutator-energy
floor immune to amplification. The remaining open upper-bound construction is
`matrix-only-cyclic-carrier-invariance`: make that same Fourier carrier
asymptotically invariant in every finite matrix model by a genuinely
matrix-only capacity or holonomy recurrence. Canonical finite packets alone
cannot supply the required coordinates;
`canonical-finite-packet-data-stop-at-scalar-overlaps` proves that they fix
Plancherel masses and scalar overlap checks but leave the multiplicity gauge
arbitrary.

The second-pass adversarial synthesis is recorded in
`research/artifacts/adversarial-error-delocalization-second-pass-2026-08-21.md`.
It identifies the useful version of the heavy-tail metaphor as a nonamenable
distribution on challenge **addresses**, not an unbounded operator statistic;
proposes a streaming Gram-rank overflow detector as a potentially smaller
same-model alternative to the supercritical Clifford table; and isolates the
exact role of a finite cyclic verifier as a holonomy return on an already
positive-density no-capture carrier.  The shortest bypass remains an exact
unital realization of the fixed non-CE BCS algebra in a signed group-algebra
corner.  None of these refinements is presently a proof; each has explicit
dimension-, runtime-, direct-sum-, and amenable-tail falsification tests.
The raw version is now fenced by
`raw-gram-rank-overflow-has-no-constant-local-gap`: regular simplices are
globally rank-deficient while every bounded Gram window becomes orthonormal,
so rank overflow supplies no constant local HS gap without the same kind of
global PCP machinery the proposal hoped to avoid.

The dual-prefix Leavitt lane now has a one-scalar endpoint. The exact
three-root prefix swap and the coarse/fine rank calculation reduce the whole
same-reservoir problem to controlling

```text
||(1-f)Je||_2^2
```

for one coarse `M_2` selector `e`, one fine `M_4` selector `f`, and one named
unitary word `J`. Equivalently,
`coarse-fine-selector-covariance-has-quarter-trace-floor` gives the fixed
payment `||JeJ^*-f||_2^2>=tau(P)/4`. The current Clifford compiler leaves an
arbitrary multiplicity involution in the fine atom reflection, and
`pure-prefix-swap-invariants-are-selector-blind` proves that no pure spectrum,
determinant, index, or power-trace test can remove it. The surviving attack
must pin this **mixed** selector moment by finite multiplicity or make the
multiplicity twist recur contractively; universal algebraic frames are ruled
out by `algebraic-selector-mixing-frame-collapses-forbidden-sector`.

The Atlas hard-prefix audit closes one finite-carrier hole without closing
the goal.  `actual-hard-prefix-generates-s4-over-raw-s3` proves that every
actual class-11/class-30 cross-chart prefix, not merely its classical fold,
generates an honest `S4` with the raw `S3`; adjoining the separate
Leavitt-star word gives an order-168 packet.  Hence the multiplicity-free
`S4 downarrow S3` carrier decomposition may be exactified.  The remaining
obstruction is purely mixed and matrix-specific:
`separated-channel-identities-retain-rectangular-escape` proves
that carrier determinants and Leavitt coefficient equivariance cannot force
same-scale closure while they live in separate tensor factors.  The open
`atlas-hard-packet-s3-channel-decoder` must extract from actual quotient
relators one fixed invertible operator system on the same three multiplicity
path-products (or prove the equivalent full-packet bicommutant estimate).
The delta and exact replay are summarized in
`research/artifacts/leavitt-atlas-final-audit-2026-08-22.md`.

The first error-spreading version of this endpoint is now exact:
`cyclic-coarse-fine-selector-rows-spread-carrier-error` allows a different
carrier mass and an arbitrary multiplicity-twisted unitary at every vertex,
yet charges one quarter of the **total** carrier mass after a cyclic return.
Thus local defects cannot be hidden by moving them through ever larger or
unrelated reservoirs.  The only remaining gate is matrix-only authentication
of the mixed selector rows themselves; neither common-reservoir alignment nor
twist cancellation remains necessary once a cyclic decoder supplies them.

The global BCS endpoint is now
`global-marked-type-cycle-selector-decoder`: permute all marked
context-types, pack the cyclic row floors by isotypic orthogonality, and use
the shared non-CE forbidden mass only after summing over the entire menu. Its
two open inputs are a finite-matrix domination of the summed compressed rows
and global forbidden-mass coverage. This avoids both universal-row collapse
and the circular demand that one context already carry positive mass.

The phase-coded refinement now separates the row-domination input exactly.
`phase-covariance-words-exactly-measure-type-transport-leakage` charges every
wrong-type population block by two-sided ordinary covariance words, while
`finite-phase-codewords-weight-type-gram-leakage` charges off-type Gram
coherence.  The projection inequality in
`phase-tagged-row-defect-reduces-to-within-type-selector-mismatch` leaves only
the selector mismatch compressed inside the already matched type.  Thus the
live matrix-only gate is no longer generic type authentication: it is the
word authentication of the nonlinear cut `F_cQ_omega` within that type.

The self-referential gauge mechanism is also explicit.
`recursive-clifford-tail-supplies-anchor-but-not-contraction` realizes every
parent `CZ tensor V` with `V` equal to the product of its two child tail
gates; that child product is the exact same-gauge identity-outer anchor.
Finite-depth Clifford regular models prove the recursion is stationary, so
the remaining breakthrough must be a payload-dependent first-hit or
proper-corner exposure inequality with contraction factor below one.

One analytic coverage obligation has closed only relative to the marked
sector.  `forbidden-weighted-type-carrier-coverage-is-rank-rounding` covers
`E_forbid^mark` with coefficient one and loss `3|Omega|/d`; comparison with
the entire original shared BCS mass would require an additional marked-menu
concentration estimate.  Thus the stronger full-space global criterion
retains both marked-type concentration and summed-row domination.
For the central-sign endpoint,
`marked-corner-cycle-needs-no-full-mass-concentration` removes the comparison:
the robust BCS gap is applied directly on the common negative sign corner,
whose forbidden mass is exactly `E_forbid^mark`.  Consequently the
phase-coded central-sign route has only the summed-row/authentication gate;
marked-menu concentration remains a stronger full-space variant, not a
load-bearing prerequisite for that route.
Separately,
`tail-wordized-child-surplus-collision-supplies-rct7` converts forbidden BCS
surplus into the strict recursion

```text
(1+beta)a_n<=a_(n+1)+errors,
```

and one reflection-conjugacy word controls the only leakage term. Thus the
recursive lane's remaining obligation is not supplied by the tail cancellation:
`aggregate-child-wordization-three-route-no-go`
shows that a new finite-matrix-only selected-sector/orthogonalization step is
needed to turn the aggregate corrected child into one word while retaining
the shared BCS tuple. A single ordinary Hecke holonomy
cannot provide the alternative global row domination:
`one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum` closes it by a
last-edge multiplicity-gauge countermodel.

The aggregate reflection is no longer the minimal collision gate.
`partitioned-child-surplus-collision-supplies-contraction` proves that a
fixed finite family of genuine child pieces, returned into pairwise
orthogonal pieces of the next carrier, supplies the same strict contraction
after summing support leakage.  This removes the need to multiply
noncommuting context cuts or to encode their nonlinear sum as one word.  The
new last interface on that lane is
`typewise-schur-tail-partition-compiler`: install the already groupified
corrected-child type menu as an orthogonal recursive-tail partition while
retaining the robust gap on the original shared BCS tuple.

The purely local portion of that interface is now explicit.
`index-two-reynolds-atoms-have-orthogonal-hnn-transports`
shows that an HNN conjugacy of both levels of an index-two finite-subgroup
flag transports its Reynolds difference exactly, and that distinct
characters of one elementary-abelian packet give orthogonal target atoms.
Accordingly neither nonlinear atom reflection wordization nor local target
orthogonality remains open.  Cairn's
`canonical-types-extend-every-finite-bass-serre-actor` prevents overclaiming:
the unresolved step is the shared-BCS, finite-matrix-only selection of a
supercritical active family, not more finite subgroup covariance.

Cairn now records that residue directly as
`shared-bcs-matrix-only-supercritical-atom-selection`.  It must consume a
cross-context operator observable of the original non-CE BCS tuple; scalar
forbidden mass and every pure finite Bass--Serre actor are already ruled out.
If it is established, the new pair-HNN router closes
`typewise-schur-tail-partition-compiler`, and the existing dependency chain
continues through fixed-scale holonomy and the multiplicity-return
transducer to this root claim.

The stability interface was consolidated and corrected on 2026-08-26.  For
hyperlinear Kazhdan groups, Dogon's weak ucp-stability coincides with full
flexible HS-stability on every asymptotic representation
(`kazhdan-weak-ucp-stability-is-flexible-stability`: tensor-regularize by
one exact regular packet, then Kazhdan-average the Stinespring corner to an
exactly invariant finite corner; reusable form
`kazhdan-almost-invariant-corner-near-invariant-projection`), so the
weakest usable stability hypothesis for the plain lattice is
`sl3-z-weakly-ucp-stable`, consumed through the thin co-dense pair by
`non-hyperlinear-from-sl3-z-weak-ucp-stability`.  Two new hypothesis TYPES
entered the graph.  A C*-lifting route:
`non-hyperlinear-from-llp-non-rf-kazhdan` — a non-residually-finite
Kazhdan group whose full C*-algebra has Kirchberg's LLP is itself the
witness, sharpening Fournier-Facio--Willett's Question 1.9 (no `H_2`
condition, no central extension).  And a forced-witness family:
`kac-moody-lattice-is-non-hyperlinear-or-llp-failure` — every simple
Kazhdan Kac--Moody lattice of Caprace--Remy (explicit `(2,4,6)` Cartan
matrix instance) is either the goal's finitely presented simple witness or
a new kind of LLP failure, so the class settles a published question
either way.  Recorded cautions: host-side weak ucp-stability cannot be
consumed (the `l^2(A/C)` leak survives infinite-dimensional dilation), the
subgroup-side version only confines enemies to the `Lambda`-exact face
(`kazhdan-subgroup-weak-ucp-exactifies-microstates`), and Kac--Moody
building completions lack Howe--Moore, so the arithmetic Hecke far-defect
lane does not transfer to those pairs.

Later the same day the lifting square closed into a lattice of routes.
`twin-lattices-exclude-known-llp-fences` proves that twin building
lattices contain no known LLP-failure group (flat-torus rigidity for the
cohomological fences, property A for the expander fences), confining the
live candidacy to compact hyperbolic Kac--Moody types with no published
mechanism pointing either way; and `non-hyperlinear-from-e3-fibre-llp`
routes the goal through the Deligne triple cover, whose full algebra is
the direct sum of three mod-three fibres
(`sp4-mod3-twisted-fibres-have-llp` is the twisted-fibre hole, the
sharpest live instance of Fournier-Facio--Willett Question 1.12), so the
lifting lane and the Deligne Maslov lane
(`deligne-sector-gap-is-exactly-nonhyperlinearity`) now certify each
other's endpoint.

**Partition of the routes (2026-08-21 evening).**  Every route into this
goal either (i) transfers the MIP*=RE non-Connes-embeddable object — the
tracially satisfiable, non-`R^U` constraint system `B_*`
(`mipstar-bcs-tracial-nonru-exists`), equivalently the non-CE character of
the sofic Coxeter host (`non-ce-trace-on-sofic-racg`), or the
non-co-hyperlinear IRS relation — into a group factor, or (ii) produces a
non-Connes-embeddable II_1 factor by hand (relative-commutant collapse,
stability, atlas, Kervaire--Laudenbach), which no published argument has
done without MIP*=RE.  The minimal statement of type (i) is
`non-ru-bcs-is-satisfiable-in-a-group-factor`: any countable host, any
model, state-space form in `character-group-realizability-parseval-criterion`;
embedding universality of group factors is open (Chifan--Drimbe--Ioana
Remark 1.1), and the IRS relation is not even treeable
(`non-ce-relation-is-not-treeable`).  The minimal statement of type (ii)
for the HNN family is `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`:
one Haar unitary in `L(C)' cap R^omega` free from `L(A)` with amalgamation
over `L(C)`, strictly weaker than the collapse and than projective
transfer; its standard-model calibration is
`arithmetic-pair-group-factor-ultrapower-has-no-leak` (collapse holds in
`L(A)^omega`, so the matrix question lives in `L^2(M) (-) L^2(L(A))`).
Popa's relative free-independence theorem (arXiv:1308.3982) supplies
exactly such unitaries when the centralised subalgebra is amenable, so
type (ii) for `C = SL_n(Z)` asserts that Popa's theorem fails past
amenability — the Gao--Junge open problem in its first arithmetic
instance.

The independent Haar-tag/Diracization version of type (i) now has an exact
kernel audit.  `haar-tag-cancellation-retention-is-group-realizability`
shows that the diagonal group generated by payload unitaries with arbitrary
group-valued Haar tags has canonical trace precisely when the tag-zero kernel
already has regular payload character.  A faithful tag map therefore erases
the payload completely; a nonfaithful one either restores noncanonical
payload moments or puts the cancellation sector inside an already regular
kernel group factor.  Balanced tensor powers likewise have payload
expectation `pi(w)|tau(w)|^(2k)`, scalarizing every fixed finite-word decoder.
Thus a fixed-density recoverable non-CE corner would not be supplied by the
tags: it would already be the terminal group-factor realization in the kernel
identified by `fixed-density-polarization-retention-is-terminal`.

The measured/algebraic version of type (i) is now closed against the native
Manzoor actor.  `manzoor-native-haar-envelope-is-ce-after-corners` shows that
every compact-abelian Haar action of the source free group has crossed
product `L(A semidirect F)`, with `A semidirect F` sofic.  No non-CE Manzoor
GNS or relation factor can embed there, even after matrix amplification or a
nonzero finite corner; in a finite tracial algebra every trace-preserving
inclusion is automatically expected.  The stabilizer realization used by
Manzoor instead maps the free-action crossed product onto the relation
algebra only through a singular orbit-arrow quotient.  Thus the algebraic-
envelope compiler remains exact, but it must change the acting group.
Producing that different algebraic action would already exhibit the non-
hyperlinear dual semidirect product and is not hidden Bernoulli structure in
the published construction.

Changing the actor does not rescue the most literal Feldman--Moore
construction.  `fm-stone-lamp-corners-are-singular` starts from any countable
atomless Boolean generator of the Cartan and its symmetric-difference lamp
group.  If the source event signs are mapped to compressed literal lamps in
any nonzero corner, their unitarity forces that corner to reduce the entire
lamp algebra.  The corner spectral law is then Haar-absolutely-continuous,
whereas the source Stone law is concentrated on the Haar-null ultrafilter
locus.  This rules out the canonical Boolean-lamp compiler for every graphing
actor and every actor enlargement, including initially noncentral corners.
Only a genuinely non-Cartan embedding or nonlinear multi-grade images of the
Cartan signs remain.

**Frontier map after the 2026-08-21 evening RE pass.**  The three
independent standing routes each bottleneck at a core that is
equivalent-to-or-harder-than a recognized open problem, and the by-hand
routes now share ONE analytic residual:

- *Arithmetic RCC / relative-embeddability (type ii).*  The HNN group's
  minimal form is `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`;
  its host-only weakest form is `arithmetic-pair-is-not-relatively-embeddable`
  (`= D^+ = (A x Z) *_C A` non-hyperlinear, Gao Thm 7.1).  Under
  `sl3-z-weakly-ucp-stable` (confinement to the `Lambda`-exact face) this
  reduces, after `sl3-re-lambda-exact-coprime-face-is-unfaithful` (coprime
  levels) and `lambda-exact-face-of-the-collapse-closes` (regular-type
  2-power), to EXACTLY the `(RC3)` residual:
  `two-adic-tower-format-of-surviving-lambda-exact-enemy` — an
  `S_3`-interlocked depth-two solenoidal tower over `{SL_3(Z/2^a)}` with
  every marginal forced, being measured by the sioux tower probe (exact
  interlock floor `32/21` at `s = 1`).  The regular-trace-forces-regular-type
  shortcut is ruled out.  The other horn of the residual is the
  weak-ucp/outlier sector, i.e. flexible stability of `SL_3(Z)`
  (Dogon--Vigdorovich Q1.4 shape).
- *Atlas / binary Leavitt unit group (type ii, finite-combinatorial).*
  Reduces to finite certificates over `A8 = GL_4(F2)` and collision `19243`
  (`atlas-a4-holonomy-coherence-gap` family); several are being computed
  directly.
- *Binary-Leavitt singular-cover lift (state form).*  Full LLP is unnecessary
  but the weaker endpoint remains goal-hard:
  `fourier-local-sections-already-descend-amenable-trace` shows that ucp
  sections only on finite Fourier word systems already descend the amenable
  cover trace to the nonamenable regular quotient.  Infinite-cyclic systems
  lift by functional calculus; the first missing datum is a multiword
  positive lift which is collision-consistent for equal differences
  `g^{-1}h`.  The near Gram matrix is positive but has that consistency only
  modulo the trace-kernel ideal, so pure singularity supplies no section.
- *MIP*=RE transfer (type i).*  `non-ru-bcs-is-satisfiable-in-a-group-factor`
  (weakest form; any corner of any group factor modelling the fixed non-RU
  BCS), equivalent by `character-group-realizability-parseval-criterion` to
  a Parseval joint-state existence; blocked on embedding-universality of
  group factors (Chifan--Drimbe--Ioana Remark 1.1, open) or the
  Boolean-to-linear groupification (Paddock--Slofstra Prop 5.8, equivalent
  to the goal itself).

So every current route reaches the same class of frontier: a genuinely open
rigidity/stability question.  The RE pass's structural gain is that it
collapses the two by-hand routes onto one residual and states it as a
host-only, stable-letter-free question about microstates of `SL_3(Z[1/2])`.

**Capstone of the RE pass — the two ARITHMETIC routes collapse onto one
rank-one core.**  The Kostant computation
(`bounded-degree-two-primitives-for-higher-rank-lattices`, all `N >= 4`)
shows the operator-norm degree-2 primitive that the higher-rank
flexible-stability route needs is obstructed at the `(2,N-2)` Borel--Serre
cusp by a `GL_2`-block `SL_2(Z[1/p])`-Levi-fixed class, at EVERY rank.  So
raising the rank does not buy escape from rank one: the RCC/RE route
(through its weak-ucp/outlier horn) and the higher-rank flexible-stability
route both reduce to the SAME rank-one core,

```text
CORE A:  flexible HS-stability of the rank-one pair SL_2(Z) < SL_2(Z[1/2])
         (Dogon--Vigdorovich Question 1.4, the Iwahori / BS(1,4) lane).
```

The factorized form of CORE A has one less independent obstruction than it
first appears.  `projective-dihedral-factorization-has-explicit-hs-retraction`
shows that, after retaining one projective Weyl factor `A`, the relation
`C=AB` together with `A^(-1)CA=C^(-1)` admits an explicit same-dimensional
normalized-HS retraction: round `D=A^(-1)C` to the roots of
`D^2=epsilon I`, at cost at most the reflection defect divided by `sqrt(2)`.
Thus factor splitting itself is uniformly repairable.  The unresolved CORE A
gate is the simultaneous intersection with `CXC^(-1)=X^4` and the two modular
order-three rows.  Projecting a corrected BS pair back to the reflected locus
reintroduces these residuals with absolute linear constants, so a proof still
needs a dimension-uniform angle or flexible boundary reconciliation among the
three exact loci; the known slow regular modes and compressed Weil packets do
not supply that angle.

The strict-angle option is now completely excluded.
`iwahori-two-loci-have-zero-uniform-angle` puts the compressed even-Weil tuple
exactly on the reflected `BS(1,4)` locus and, by simultaneous triangle
rounding, finds an exact two-cubic tuple only `O(p^(-1/2))` away.  The
same-dimensional intersection remains a fixed positive distance away.
Therefore metric linear regularity, a globally uniform alternating-projection
contraction, and residual-only Newton basin capture all fail.  The surviving
CORE A endpoint is necessarily flexible: it must spend the rank-one boundary
mass across packets rather than improve the strict intersection angle.

For authenticated Weil mixtures, that flexible spending is now block-free.
`weil-reservoir-mixing-has-energy-paid-completion` permits heterogeneous
prime levels, arbitrary multiplicities, common basis changes, and arbitrary
unitary mixing inside the whole deleted fixed-line reservoir.  The positive
corner spectrum remains at most `1/sqrt(5)`, so the first cubic Frobenius
energy pays a universal constant times the entire deleted rank.  Restoring
that reservoir gives the exact endpoint with squared flexible displacement
of the same order as energy density.  Consequently CORE A's remaining gate
is no longer completion of arbitrary authenticated block sums; it is reverse
authentication of a positive boundary reservoir or global congruence atom
from the two residual carriers of a completely arbitrary near-solution.

That reverse statement now has a necessary asymmetry.  The active carriers
cannot authenticate the passive global endpoint type.
`active-residuals-do-not-name-passive-endpoint` attaches an arbitrary
growing `o(d)` sum of one fixed nonzero compressed Weil cell to each of two
macroscopically separated cuspidally
redistributed exact endpoints over the same literal BS core.  The resulting
near tuples have identical exact cores and literally identical two-cubic
residual operators, including all polar and principal-angle data, while the
passive involutions remain a fixed distance apart modulo the core commutant.
Both are completed by restoring the same energy-paid active boundary lines,
but they retain different passive endpoint types.  Hence the surviving
reverse theorem must restore a local energy-paid boundary cell and then use
the supplied passive involution in a separate adaptive correction.  No map
from “exact core plus active residual data” to one global congruence atom can
prove CORE A.

The surviving triangular statement is complete at every fixed coordinate.
`fixed-core-passive-fiber-has-positive-basin` minimizes the two-cubic loss
on the compact exact-inversion reflection locus over a fixed core `beta`.
Away from the finite simultaneous endpoint fiber it has a positive minimum
`delta_beta(eta)`, so a passive residual below that radius exactifies within
`eta`; direct-summing the restored active cell then gives the exact endpoint.
The unresolved uniform theorem is precisely that the moving passive
residuals beat their moving radii.  Sublinear active restoration cannot
force this, because it leaves the relative ultraproduct lifting class
unchanged.

A normalized tangent blow-up does not bypass this point.
`moving-basin-blowup-needs-displacement-charge` proves that if `X` remains
distance `eta` from every exact endpoint, then for every `tau<eta` the
operator-`>tau` part of `X-Y` has relative rank at least
`(eta^2-tau^2)/4`, for every endpoint `Y`.  The operator-small remainder
cannot carry a nonzero normalized tangent, while discarding the large part
costs positive-density padding.  Residual thresholding controls spectral
projections of the cubic errors, not these endpoint-displacement
projections.  Relating the two would itself be the missing global arithmetic
error bound.  A fixed-degree scalar family with uniform derivative at every
coordinate zero but a collapsing far-away residual shows that local tangent
coercivity and bounded derivatives alone cannot provide it.

The integer boundary bookkeeping is also complete at its first native face.
`three-way-parity-hole-has-one-cell-repair` shows that the minimal
determinant-two source/two-exit hole is repaired by one support-changing odd
margin triple.  At level five,
`a5-d10-restriction-keeps-parity-charge` computes the exact
`A_5 -> D_10` table: exact atoms preserve the parity of
`epsilon+rho_1+rho_2`, but one raw sign line gives

```text
epsilon+rho_1+rho_2+epsilon=res(3+3').
```

The line is energy-paid on that face
(`a5-d10-parity-blocks-have-energy-paid-repair`).  More generally,
`fixed-finite-core-face-has-energy-paid-completion` proves the same
compactness/completion dichotomy for every fixed finite quotient and core
type.  Thus the residual arithmetic obstruction is not fixed-level
integrality; it is uniformity across moving authenticated faces.  The one
remaining fourth case is a soft delocalized face with vanishing energy
density but neither a uniform same-core basin, an `O(E)` internal carrier,
nor an `O(E)` efficient native completion.  The known Weil packets have the
last completion, while the known cohomological soft modes fail the exact-BS
core hypothesis.

A dyadic decomposition does not remove this quantifier by itself.
`dyadic-face-repair-needs-cost-tail-tightness` proves that facewise bounds
`r_lambda<=C_lambda e_lambda` sum only to

```text
total repaired rank/d <= L E/d
  +mass{lambda:C_lambda>L}.
```

Thus pointwise finite-face compactness gives a qualitative global repair
only under uniform tightness of the occupied repair-cost tails.  The scalar
array supported on a type with `C_n->infinity` and energy density `1/C_n`
is the exact failed diagonal implication.  Canonical trace does not give
ordinary type tightness by conductor truncation: it sends every fixed
shallow-conductor mass to zero.  A native cost bound or a distinct
cost-tail theorem is still required.

The natural core-level coarea repair is quantitatively false.
`bs-core-coarea-cuts-have-full-legalization-cost` cuts an irreducible
length-`m` fourth-power BS packet along half of its base spectrum.  The cut
has unnormalized core boundary exactly two, but the joint core commutant is
scalar, so replacing it by any exact core-reducing projection changes
`Theta(m)` dimensions.  Property `(tau)` is available only after an
endpoint atom has been selected.  A nonlinear proof must therefore use the
two endpoint rows while authenticating that atom; it cannot first legalize
residual layers using the amenable core alone.

The endpoint rows themselves eliminate this particular hard-cut enemy once
a same-core endpoint is known.  By
`endpoint-triangle-charges-bs-sign-cut-volume`, multiplying an exact
endpoint reflection by a spectral sign `1-2P` forces square-plus-first-
cubic energy at least `2 rank(P)`; if the new reflection is still an
involution, the first cubic alone costs `4 rank(P)`.  Thus a half-cycle cut
has linear endpoint energy despite constant core boundary, and arbitrary
unions of cyclic intervals satisfy the same volume charge.  What remains is
authentication of the comparison endpoint, not cyclic isoperimetry inside
an authenticated basin.

A fixed comparison endpoint still cannot be used globally.
`core-expectation-misses-exact-endpoint-zero-modes` amplifies the mod-three
pair of exact same-core extenders whose relative gauge lies outside the
core commutant.  Conditional-expectation transverse norm is then positive
at exactly zero endpoint energy.  The `R`-commutant has no uniform gap on
long BS cycles, while the endpoint intertwiner expectation has a gap only
after a finite quotient type is known.  Thus the global objective is
adaptive distance to the nonlinear union of restriction-ring fibers; a
commutant-plus-transverse decomposition around one arbitrary baseline
cannot prove it.

After the endpoint types are known, this nonlinear union has an exact
stable metric.  `restriction-fiber-orbits-have-optimal-common-dilation`
splits two multiplicity vectors into their common and unmatched parts and
cross-pads the latter.  The endpoints become the same exact larger
representation with optimal added rank `mu d`; property `(tau)` identifies
`sqrt(mu)` with orbit distance.  Close exact fibers therefore merge at
quadratic padding cost.  They cannot have a relator-energy separation floor,
since every fiber is already zero energy.  Raw atom selection, rather than
inter-fiber geometry, remains the global gate.

After authentication, neither cross-packet mixing nor the first
cross-stratum substitution remains open.
`congruence-cross-type-mixing-has-uniform-polar-repair` applies property
`(tau)` to the mixed intertwiner, averages it to an exact intertwiner, cuts
its modulus at `1/2`, and polarizes.  The source and target complements have
rank at most a universal constant times the relator energy, and padding by
the opposite complements gives an exact support-changing completion.
`metacyclic-cross-stratum-energy-is-inverse-dimensional` checks the smallest
unauthenticated-looking substitution inside a regular endpoint: its three
coset branches are orthogonal and its endpoint energy is `Theta(1/D)`, exactly
the scale of the available same-space core correction, not `o(1/D)`.

Direct central-idempotent decoding does not supply the missing
authentication.  `raw-core-central-reynolds-authentication-is-circular`
records two independent obstructions.  The exact BS core alone cannot choose
the global central profile, because cuspidally redistributed exact endpoints
can have the same literal core.  Evaluating a finite-quotient central
idempotent on the raw tuple requires a word-section multiplication table;
the cyclic core-character family gives nonuniform logarithmic filling cost
for every frozen-core section.  Moving the core before evaluating that table
is precisely the gauge-optimized theorem still being sought.  Thus the sole
arithmetic gate is now accurately stated as **adaptive moving-core relative
liftability**, or equivalently the gauge-optimized two-dimensional section
energy estimate.  It is not conductor guessing, parity repair, packet
mixing, or passive-type selection from the active residuals.

The fixed index-three induction viewpoint gives a cleaner equivalent form,
but not a free rounding theorem.  By
`index-three-qsystem-rounding-is-relative-repair`, an extension of an exact
Iwahori fiber `sigma` is exactly a rank-`d` invariant projection in
`Ind_B^V(sigma)` on `3d` whose three coordinate compressions are `1/3`.
For merely close edge restrictions the canonical projections remain exactly
flat and have commutator defect bounded by a fixed constant times the edge
defect—there is no growing Schreier area.  However jointly rounding the two
flat projections over one optimized fiber is quantitatively reversible to
the original relative Iwahori repair.  Separate three-coset saturation is
already false on the mod-two packet.  Hence the Q-system may furnish an
alternative attack on adaptive liftability, but it neither proves the
stronger `G_N<=C E_end` functional nor turns finite-index permanence into
the missing joint projection angle.

The 2-adic tower residual is the `Lambda`-exact sub-case of CORE A; the
weak-ucp outlier residual is the non-exact sub-case; the cusp computation
shows both are rank-one at heart, so within the arithmetic family no route
escapes to a strictly easier object.  This does NOT reduce the WHOLE
program to CORE A: at least three further genuinely independent cores stand
outside the arithmetic family and are not touched by this pass ---

```text
CORE B:  a model of the fixed non-RU BCS in some group factor (MIP*=RE
         transfer; embedding-universality of group factors, CDI Rem. 1.1,
         or the Boolean-to-linear groupification, Paddock--Slofstra 5.8);
CORE C:  a non-residually-finite Kazhdan group, or Sp_4(Z), with LLP full
         C*-algebra (`non-hyperlinear-from-llp-non-rf-kazhdan`,
         `non-hyperlinear-from-sp2g-llp`; Fournier-Facio--Willett Q1.9/Q1.12);
CORE D:  the finite-combinatorial atlas certificates over A8 = GL_4(F2)
         (`atlas-a4-holonomy-coherence-gap`), self-contained and computational.
```

Net: the program is `CORE A or B or C or D` (plus the machine/reverse-Kleene
compilers, which feed CORE B via LCS perfect completeness).  This pass's
gain is specifically that the arithmetic RCC/RE and flexible-stability
routes are now proven to meet at CORE A --- one rank-one problem, not two
rank-dependent ones.

**Audit corrections to the frontier map and the four-core capstone
(2026-08-21, late).**  Three adversarial audits of the shortest paths
changed the following statements above.  (1) *Coprime face.*
`sl3-re-lambda-exact-coprime-face-is-unfaithful` is OPEN again: its step
`pi(h) in pi(Lambda)''` confuses the coordinatewise subgroup algebra with
the ultraproduct one (`congruence-slot-escapes-ultraproduct-lambda-algebra`);
the proved form needs the rate `eps_k log n_k -> 0`, so the `(RC3)`/RE
residual on the `Lambda`-exact face includes slow-rate coprime witnesses.
The sector collapse `odd-congruence-lambda-exact-sector-collapses` itself
stands.  (2) *Iwahori near sector.*  `iwahori-newton-closes-near-sector` is
OPEN again: the Newton step used a dimension-free second-derivative bound in
normalized HS, which does not exist
(`normalized-hs-taylor-remainder-is-not-dimension-free`); only an
operator-norm-proximity version holds.  The first-order theorem
`iwahori-uniform-infinitesimal-rigidity` stands, with its kernel statement's
"(T;FD)" justification unpacked (`SL_2(Z[1/2])` has (T;FD) though not (T);
CSP + Selberg give (T;FD), (T;FD) gives FAb, FAb gives `H^1 = 0`).  So
CORE A currently has NEITHER sector closed -- near (HS metric) nor far.
(3) *A fifth core.*  The type (i)/(ii) partition and the capstone
`CORE A or B or C or D` omit the Pestov lane: `hyperlinear-implies-sofic`
(Pestov Question 3.4, affirmative side) routes here by
`non-hyperlinear-from-hyperlinear-implies-sofic` through the nonsofic
Leavitt unit group, with twelve live holes across six sub-routes
(bounded-width compiler, cpsd face collapse, de Finetti rounding,
Markovization, traffic lifts, orbital rounding).  It is neither an
MIP*=RE transfer nor a by-hand non-CE factor, and it is independent of
A-D.  Likewise the Kun--Thom rigidity lane (`kt-centralizer-normalization-hs`
family), the Kervaire--Laudenbach lane, and the algebraic/Pontryagin
envelope lane (which reaches a group factor by duality and needs neither
embedding universality nor Paddock--Slofstra 5.8) are live and not
subsumed by the four named cores.  Honest count: the program is
`CORE A or B or C or D or E(Pestov)` plus three smaller independent lanes.
(4) *Tool note, withdrawn.*  An earlier draft of this note reported that
`bin/cairn frontier` listed `atlas-a4-rank-three-core-commutant-collapse`
as an open hole while `cairn why` called it refuted; on re-check the claim
was OPEN when that listing was taken and was refuted shortly afterwards by
`atlas-14-core-q19243-gl5-countermodel`, and the frontier view now agrees.
No tool defect.

**Kun--Thom/Kahl--Schneider compression audit (2026-08-24).**  The actor-only
route now has a complete countermodel.  For the actual residually finite
Kun--Thom pair, `kun-thom-compression-survives-amenable-near-model` assembles
the finite regular quotients of `G` into a faithful, essentially free,
amenable **genuine** representation with its Kahl--Schneider basis charge.
The strict inclusion `t Gamma t^(-1)<Gamma` survives faithfully in the direct
sum, but in every finite block the two subgroup images are conjugate finite
subgroups with one included in the other, hence equal.  Their fixed spaces
therefore coincide exactly, the compressor normalizes the common fixed
space, and its Reynolds projection has charge

```text
lim_n 1/|q_n(Gamma)|=0.
```

Thus neither amenability nor even exact multiplicativity turns the compression
into a positive-charge child-only sector.  Bekka--Valette only returns a
nonzero finite-dimensional subrepresentation, and every finite-rank projection
in this witness is charge-null.  The full wreath and double are not modeled by
this construction, so their hyperlinearity remains open.  What a successful
transfer must additionally prove is lamp-sensitive **invariant Cartan
completion**: recover a charge-visible abelian diagonal normalized by the
actor.  Kahl--Schneider's invariant state `mu_bullet` does not provide this,
because the near unitaries need not normalize the basis masa.  The compression
geometry alone is therefore exhausted; the lamp/Cartan classicalization is
the exact remaining interface.

There is nevertheless a weaker pinned stability endpoint than invariant
Cartan completion.  `kt-wreath-relative-canonical-actor-exactification` asks
only that the **actor restriction** of canonical microstates of the explicit
wreath be close, after negligible padding, to genuine finite-dimensional
actor representations.  Property `(T)` rounds the base lamp into the actor
commutant, and finite-dimensional commutant no-growth makes a strict
compressor unable to create the distinct transported lamp required by the
canonical trace.  Thus this actor-only, canonical-sequence exactification is
already sufficient for a non-hyperlinear group; full wreath stability, lamp
exactification, and monomialization are unnecessary.

The updated Kun--Thom group double behaves differently.
`kt-double-canonical-vertex-marginals-admit-large-amalgam-twists` uses the
actual residual finite quotients of the Theorem E actor.  Diagonal random
signs on left `q_n(Gamma)`-cosets commute with the amalgam exactly, while a
fixed element detected through the `SL_d(Z)` quotient moves them by squared
HS distance at least `2`.  Conjugating one finite regular vertex
representation by these signs gives two exact copies, agreeing on `Gamma`
and each converging to the regular actor character, yet uniformly unaligned.
So vertex HS stability or vertex character rigidity alone cannot make
hyperlinearity of the double imply residual finiteness.  The minimal surviving
double lemma must constrain mixed reduced alternating-word characters—an
amalgamated-freeness obstruction—not merely the two canonical marginals.

The first direct attack on the new actor-only wreath endpoint produces a
sharp firewall rather than a proof.  For every single positive Kun--Thom
compressor, `kt-single-compressor-canonical-lamps-do-not-exactify-actor`
uses the established soficity of the restricted coset action to build
canonical **permutation** microstates of its binary wreath.  These models
satisfy all Bernoulli cylinder and mixed lamp--actor traces, yet their actor
legs stay a uniform normalized-HS distance from every genuine
finite-dimensional representation after `o(d)` padding.  If they did not,
Kazhdan averaging and finite-dimensional commutant no-growth would identify
the lamps at `tGamma` and `gamma tGamma`, contradicting their canonical
distance `sqrt(2)`.  Thus canonical lamp moments do not repair generic actor
instability locally.  Any proof of the full
`kt-wreath-relative-canonical-actor-exactification` must consume relations
from at least two incompatible compressors—the same multi-compressor
compatibility where Kun--Thom nonsoficity first appears.

That lower bound has now been sharpened beyond “two.”  The natural pair
`u_13,u_32`, whose commutator is the strict compressor `u_12`, generates an
amenable Heisenberg compression monoid.
`amenable-multi-compressors-have-a-joint-hs-telescope` indexes arbitrary
coefficient representations by explicit Heisenberg Følner boxes and obtains
simultaneous `O(L^(-1/2))` HS covariance for both compressors, their
Steinberg commutator relation, and every fixed local lamp/Reynolds table.
Thus noncommutativity and a commutator compressor do not exactify the actor.
The surviving Kun--Thom seam is genuinely global: canonical mixed lamp
correlations for a nonamenable generating family, or an equivalent
lamp-algebra/Cartan recovery.  The telescope does not model those global
moments and therefore does not decide hyperlinearity of the full wreath.

Nonamenable cone expansion itself is now equally explicit.
`opposite-transvections-are-free-but-finite-lamp-windows-close` proves that
the two positive compressors `u_12,u_21` generate a free monoid, with total
right boundary at least `2|F|` for every finite word set.  A depth-uniform
lamp decoder on all wrong boundary matches would therefore give a constant
HS floor.  But every fixed-radius positive cone embeds in a finite
congruence quotient, whose finite Bernoulli wreath realizes all lamp moments
in that window exactly.  Such models break only on the compressed
`Gamma`-moved lamps, because every finite quotient makes the image of
`Gamma` normal.  Hence the expansion is certified, but turning it into KRE2
still requires a uniform stabilizer-sensitive decoder rather than bounded
cone tests.

The finite-depth stabilizer decoder itself is now explicit.
`free-compressor-tree-has-constant-first-hit-mover-mass` assigns one lamp bit
to every internal word of the opposite-transvection tree.  Its depth-`n`
dyadic cylinders are orthogonal, their leaf exits are fixed by the child
compression subgroup, and a parent-only stabilizer element moves them with
aggregate squared normalized-HS mass exactly `1/2`, independently of `n`.
This removes first-hit capacity as the local obstruction.  What remains is
an adjoint-rank conversion: the `2^n` exit projections span normalized
adjoint rank at most `2^n/d^2` at fixed depth, below the scope of the existing
property-`(T)` positive-density theorem.  A depth-uniform aggregate
Reynolds inequality `(FCT8)`, or equivalent lamp/Cartan recovery, is still
needed; finite congruence windows fail precisely the `Gamma`-moved leaf
correlation that carries the constant half-unit displacement.

The natural categorical amplifier has also been audited and does not supply
that inequality.  By `fct8-left-lift-and-rotated-defect-firewall`, the
left-multiplication projections `L_(X_w)` have total normalized
superoperator trace `1/2` and retain the mover norm exactly, but their ranges
are only invariant under the child adjoint action, not pointwise fixed.
Conversely, the pointwise-fixed rank-one lifts have total adjoint trace only
`2^n/d^2`.  Dimension-free passage of relator defects through one or two
adjoints does hold, so this is a categorical failure rather than a norm
loss.  An exact permutation-block example shows more sharply that a sparse
root defect can be rotated into all `2^n` orthogonal leaf blocks, forcing an
exponential constant in any summation based only on conjugation and
orthogonality.  The surviving FCT8 route must therefore recover genuinely
joint prefix-unitary/lamp structure; vectorwise Kazhdan summation alone is
insufficient.

The exact aggregate boundary is now explicit.
`aggregate-leaf-bessel-fails-after-prefix-transport` proves the perfect
fixed-error identity
`sum_w||E X_w||_2^2=tr(E^*E sum_w X_w)<=||E||_2^2`, but a prefix `v` rotates
that error to `vEv^(-1)` on its own leaf. Rank-one coordinate blocks show a
wall of squared mass `1/N` can thereby pay unit aggregate mass. The estimate
is recovered exactly under the additional transported-frame condition
`sum_w v^*X_wv<=C I`; no current relation supplies it. This is not merely an
abstract packet: canonical one-compressor Kun--Thom wreath microstates contain
a trace-`1/2` lamp projection asymptotically fixed by `t Gamma t^(-1)` but
moved by `Gamma` with squared distance `1/2`. Thus property `(T)` and every
fixed one-compressor relation fragment already fail to promote child
invariance to parent invariance. Only the simultaneous incompatible
compressor tables remain capable of enforcing the missing frame/common-Cartan
condition.

The global family can nevertheless be made minimal and completely explicit.
`kt-two-positive-compressors-generate-full-obstruction` takes the cyclic
coordinate permutation `C`, `B=I+E_12`, and `A=CB` in the `d=3` Theorem E
pair.  Both `A` and `B` are positive strict compressors, while
`C=AB^(-1)` and the cyclic conjugates of `B` generate all of `SL_3(Z)`;
their conjugates of the polynomial elementary group generate the Laurent
elementary group.  Hence `<Gamma,A,B>=G`.  Each one-compressor canonical
permutation model exists, but no common actor restriction can carry all
joint coset/lamp tables: such refinements would be a sofic approximation of
the known nonsofic full action/wreath.  Thus the full permutation obstruction
already lives on two named compressors.  What remains open is precisely the
unitary upgrade: recovering this joint permutation incompatibility from
canonical normalized-HS microstates.  Exact commutant indices do not supply
it, since both strict directions have infinite growth in the Clifford model
and that index is not HS-continuous.

The first direct cylinder-PVM attack on this pair gives another exact fence.
`kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath` observes that the
`<A,B>=SL_3(Z)` orbit of the base coset is regular, because the external
factor intersects `Gamma` trivially.  Its entire binary lamp semidirect
product is therefore the ordinary regular wreath `C_2 wr SL_3(Z)`, which is
residually finite.  Canonical permutation microstates already realize every
finite `A,B`-orbit cylinder, all joint `A,B` multiplication, and all mixed
traces with one invariant cylinder masa.  Thus an `A,B`-only normalizer
transfer, even if perfect, cannot reach the Kun--Thom defect.  The first
possibly decisive PVM must also encode how `Gamma` acts on transported
cylinders—mixed incidences `gamma w Gamma`—and classicalize that nonnormal
Kazhdan stabilizer table on the same masa.  This is a sharper target than
generic invariant-Cartan completion, but it remains the unitary-HS seam.

The first required mixed incidence is explicit and only two-site.
`kt-ab-marked-return-is-the-first-mixed-cylinder` chooses
`r=e_12(x_1) in Gamma` and an `A,B` word `L` with
`Le_1=-(1,1,1)`.  Its return
`h=LrL^(-1)=e_12((x_1x_2x_3)^(-1))` moves `Gamma` to the published marked
site `hGamma`.  Once a common diagonal actor table exists, the two binary
lamp projections have separation mass `1/2` (or `35/72` for the rational
A5 center), and the established failure of marked two-point approximation
is terminal.  So a positive proof needs no growing cylinder catalogue; it
must make this single mixed Gamma--A,B return kill the two-site boundary
multiplicity cocycle.  Separate covariance cannot do that, as the exact
finite A5 boundary countermodel already shows.

One visible root correlation is still too little.
`kt-single-root-mixed-return-has-exact-finite-countermodels` reduces the
Laurent exponent torus modulo `N`, takes the finite actor quotient, and
wreathes its cosets by the cyclic subgroup generated by the image of `r`.
These exact finite models satisfy every actor relation, `[a,r]=1`, and
`b=hah^(-1)`, while the two lamp projections retain squared normalized-HS
distance `1/2`.  Hence no single-correlation inequality attached only to
`r` and `h` can provide the missing classicalization.  The next legitimate
target must use a finite Gamma stabilizer packet jointly with the mixed lamp
table; merely naming the arithmetic return does not remove its multiplicity
cocycle.

The required full stabilizer packet is explicit.
`kt-elementary-kazhdan-packet-rounds-base-lamp` takes all constant elementary
roots and the roots `e_ij(+-x_l)`.  Steinberg commutators generate the whole
polynomial elementary group, so property `(T)` supplies a fixed Kazhdan
constant.  In any genuine actor representation, a lamp projection commuting
with this packet up to `delta` is within
`sqrt(2) delta/kappa_K` of an actual projection in the Gamma commutant; the
same estimate transports through the named word `h`.  This closes the
relative lamp-rounding sublemma.  It does not exactify the actor or control
the residual action of `h` on the commutant multiplicity, which remains the
unitary-HS obstruction.

The natural two-compressor irrep-flow refinement also has an exact firewall.
`kt-two-compressor-irrep-flow-has-profinite-stationary-points` observes that
in every finite quotient of the actor both strict compressor inclusions become
automorphisms of the finite image of `Gamma`.  Its regular Plancherel vector is
therefore stationary for both `A` and `B`, while finite quotient choice matches
the canonical actor trace on any fixed window.  Moreover compressor
precomposition can branch irreducible types, and the scalar type weights
forget the entire matrix action on the commutant multiplicities where the
lamp projection lives.  Thus no free-semigroup boundary inequality on irrep
weights can close the seam.  The live target is a projection-valued,
multiplicity-sensitive two-compressor inequality coupled to the marked-return
lamp trace.

**Free-compressor packet-covariance audit (2026-08-24).**  The strongest
natural named-packet covariance still leaves the decisive tensor gauge.
By `packet-covariant-kernel-gauge`, on every irreducible finite packet type a
free generator has Schur form
`X_i=pi(theta(x_i)) tensor W_i`; hence the finite packet factor cancels on
`ker(theta)`.  Residual finite regular choices of `W_i` preserve the canonical
actor moments and all outer BCS/Reynolds data while making the normalized
kernel-fixed adjoint density exactly `1/|q_k(ker theta)| -> 0`.  Therefore the
predicate-rank adjoint gap does not by itself reach the self-copy terminal.
The exact surviving gate is payload-conditional control of the multiplicity
representation: a uniform positive lower bound for its kernel commutant on
the selected forbidden type.  Any finite attachment whose specialized active
group remains residually finite with infinite kernel image has the explicit
regular countermodel; forcing a uniform no-microstate floor instead would
already supply the hard approximation obstruction.

**Slofstra wagon-wheel quantitative audit (2026-08-24).**  The picture method
is already normalized-HS quantitative in the only direction its algebraic
embedding needs.  A fixed source relator with a wagon-wheel filling of area
`A` has matrix defect at most `A` times the output relator defect, so an
approximate-radical marked source transfers dimension-uniformly to the
solution group.  `wagon-wheel-stops-before-bcs-groupification` shows why this
does not consume the known nonaffine tracial/non-CE BCS directly.  Picture
surgery begins with an exact van Kampen diagram and gives no decoder from
small forbidden projection mass to group words.  In fact every finite local
LCS/wagon fragment has an affine scalar boundary packet; if it preserves all
allowed assignments of a nonaffine context, its affine hull contains an exact
zero-defect forbidden assignment.  A trace-specific version avoids that
countermodel exactly when each local trace support has affine hull inside the
allowed set, the locally affine-support condition already equivalent to the
perfect-LCS/nonhyperlinear endpoint.  The finite sufficient lemma is therefore
a pre-wagon shared BCS-to-group decoder with forbidden mass bounded by group
defect; no extra quantitative constellation theorem is missing.

The exact finite-dimensional radical does not narrow that gate. The sharp
firewall `wagon-wheel-exact-radical-has-hs-wall` occurs in Slofstra's own
motivating solution group: its central sign is killed by every exact
finite-dimensional representation, but explicit permutation tuples satisfy
all defining relators asymptotically while keeping the sign at normalized-HS
distance `sqrt(2)`. A subsequence meets any prescribed vanishing defect
schedule. Thus the fixed `3l` wagon fillings give only the one-way modulus
transfer `kappa_Gamma(delta)<=kappa_G(A delta)+B delta`; they do not make exact
finite-dimensional invisibility continuous at zero across unbounded
dimensions. Any nonhyperlinearity proof through this compiler must establish
the approximate-radical modulus in the source before applying the wagon wheel.

**Infinite-address nonstationarity audit (2026-08-24).**  A new periodic
firewall closes the ordinary one-shift finite-state version.  By
`one-dimensional-address-rules-have-periodic-models`, every nonempty active
payload fiber defined by finitely many translation-invariant windows along a
lamplighter/HNN address line has a periodic point.  Diagonal packet PVMs on
that finite cyclic orbit, with the cyclic shift and `F=1`, satisfy every local
conditional row exactly.  All equivariantly defined target supports repeat,
so they can be neither infinitely pairwise orthogonal nor strictly expanding
with a fixed positive factor.  The compressed Baumslag prefix has the analogous
finite-field stationary models, and Baumslag--Solitar spectral clocks have
periodic cyclic models as well.  Thus an address generator plus finite local
memory cannot supply the missing matrix-only escape.  A live gadget must use
genuinely branching/strongly aperiodic noncommutative data, or prove that its
nonzero active fiber has a dimension-uniform matricial defect floor; the latter
is already the hard obstruction rather than mere address bookkeeping.

**Branching/aperiodic address audit (2026-08-24).**  Strong aperiodicity does
not repair the HS normalization on an amenable two-dimensional host.
`strong-aperiodic-z2-addresses-have-vanishing-hs-seams` copies any valid plane
configuration onto `N by N` tori.  Only an `O(1/N)` seam fraction violates the
fixed-radius rules, giving exact actor permutations, active payload `F=1`, and
local word/projection defects `O(N^(-1/2))`.  Thus “no periodic tiling” is not
a uniform finite-matrix obstruction.  The minimal expander successor has two
separate requirements: a robust classical finite-action loss gap for the
specific local rule, and a dimension-uniform active Cartan classicalization
turning arbitrary unitary-HS microstates into those labeled permutation
actions.  Property `(T)` can help only after the first relation has been made
an actual local-testability/cosystolic theorem; it does not supply either
requirement generically.  For the Kun--Thom action, permutation rigidity is
the candidate classical gap, while `invariant-cartan-completion` remains the
unitary bridge.  The actor compression by itself stays charge-null in exact
residual finite blocks.

**Pinned lamp active-Cartan audit (2026-08-24).**  The C2/A5 finite packet
has now been pushed to its exact dimension-uniform endpoint.  On every fixed
lamp window, canonical character exactification gives a `1-o(1)` regular
packet.  A partial actor arrow is then a coordinate permutation times an
arbitrary unitary in a right-regular/copy commutant; finitely many further
lamp packets or binary labels leave a positive-density matrix block, and
tensor amplification restores the whole cocycle.  Property `(T)` does not
remove this freedom because it is a statement inside an already chosen
actor representation, not an HS-stability theorem for the actor table.

There is a useful opposite fence.  If the actor restriction *is* exactified
on a positive-density reducing corner, finite-dimensional commutant
no-growth turns the one-sided compressor inclusion into equality of
commutants.  The transported marked lamp is then fixed by all of `Gamma`,
collapsing the canonical C2 mark and the A5 center separation `35/72`.  Thus
actor exactification is already a terminal contradiction
(`kt-wreath-relative-canonical-actor-exactification`), not a preparatory route
to monomialization.  The surviving Cartan route must instead extract
genuinely approximate permutations and lamp labels simultaneously.
Conditional on a coherent finite actor table on one common PVM,
`finite-cylinder-mixed-traces-kill-normalizer-holonomy` does give a
dimension-uniform `1-o(1)` permutation core.  Producing that table is exactly
the active invariant-Cartan/action-soficity gate; neither the finite lamp
algebra nor property `(T)` supplies it.

**Packed regular-block truncation audit (2026-08-25).**  The tempting repair
of the Iwahori moving-core basin by invariantizing every high-displacement
projection is now sharply false.  `packed-d-coset-flip-has-full-bs-hull`
works in one left-regular `PSL_2(F_p)` endpoint.  It selects one coordinate
`D=<r,x>`-coset from every `B=<r,s>`--`D` double coset and reflects on their
union.  The selected projection has density at most `2/p`, is exactly the
nonzero displacement support, preserves involution and inversion, and has
two-cubic energy at most `48/p`.  Nevertheless its `B`-reducing hull is the
entire regular block, because the chosen double-coset representatives have
`B`-orbit equal to all of `G_p`.  Thus no positive-power energy estimate can
pay the legal hull, even before possible parity cancellations.  Selberg
gap, binary cocycle rounding, and post-authentication polar repair do not
alter this support fact.  A surviving moving-core proof must use the special
geometry of its decoded source or perform support-changing endpoint repair
without taking the raw BS hull.

**Monotracial source audit (2026-08-25).**  The lack of a unique-trace MIP-star
BCS is not an abstract C-star obstruction.  By
`finitely-generated-monotracial-nonce-cstar-exists`, pass to the faithful GNS
image of a non-CE BCS trace, tensor with `C(T)`, and take its reduced free
product with `C*_r(F_2)`.  Avitzour averaging gives a finitely generated
simple algebra with unique trace, and restriction to the original factor
shows that trace is non-CE.  Therefore the character-rigid quotient route no
longer needs monotracialization at the level of abstract finitely generated
C-star algebras.  Its real missing operation is a generating representation
of a finitely presented character-rigid group into that algebra (or a finite
BCS replacement); the free-product construction itself supplies neither.

**Aperiodic covariance-bimodule audit (2026-08-25).**  The proposed exact
relative-Kazhdan correction is not merely circular; on the intended
augmentation module it is impossible.  If the Hilbert--Schmidt `M`-action

```text
X |-> rho(s m) X rho(m)^*
```

extends to a finite-dimensional representation of `M rtimes A`, its finite
character support must be `A`-invariant.  Aperiodicity leaves only the trivial
character, so evaluating at `X=1` gives `rho(s m)=rho(m)`.  Requiring this for
the actor generators forces the entire rounded module representation to be
trivial.  Thus `aperiodic-module-forbids-prescribed-hs-bimodule-extension`
refutes `lamp-coupled-relative-bimodule-correction` and invalidates the
relative-Kazhdan correction route.  Any surviving character-actor proof must
use an infinite dilation or a different positive-definite kernel, and still
must connect its displacement back to the original finite presentation.

**Double-swap route audit (2026-08-25, late).**  The day closed with a third
reduction, strictly weaker at the leaf than the two stability reductions.
`hnn-stable-letter-rounds-to-finite-order` rounds the Haar stable letter of
any hyperlinear co-dense HNN group to exact central letters of every finite
order, so the binary swap group `E_p = Gamma *_Lambda (Lambda x C_2)` is the
universal receiver of the lane.  `sl3-double-swap-involution-is-outlier-carried`
then proves UNCONDITIONALLY that at `p >= 11` the swap involution cannot ride
the `Lambda`-exact face -- the depth-free, robustness and odd-congruence
theorems force the fold mark to trace `1` there against its canonical `0` --
so every canonical `E_p`-model restricts to uniform lattice outliers.  The
route `non-hyperlinear-from-sl3-double-swap` therefore needs only
`sl3-outliers-carry-no-balanced-free-involution`: no repair of outliers, just
that one moment pattern (a trace-half `Lambda`-central projection whose
`h`-translate is trace-independent) cannot occur on them.  Two structural
constraints on any refuter are in place: the enemy involution maximally
anticommutes with its twist (`swap-involution-enemy-is-never-abelian-carried`),
so no abelian/Cartan carrier -- Bernoulli wreath and homogeneous quotient
included -- can feed it; and the naive regeneration of enemies one congruence
floor down is refuted by an exact Weyl identity
(`weyl-reverser-blocks-naive-swap-twist-descent`), the same rank-two rigidity
that closes the coprime sector.  The surviving descent is dihedral only.
