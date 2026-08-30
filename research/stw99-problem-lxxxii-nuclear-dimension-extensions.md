---
rg: 2
id: stw99-problem-lxxxii-nuclear-dimension-extensions
kind: claim
title: Nuclear dimension should be the maximum across an extension (STW Problem LXXXII)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw82-one-color-gluing-audit-2026-08-30.md
  - research/artifacts/stw82-projectional-cut-obstruction-audit-2026-08-30.md
  - research/artifacts/stw82-transition-band-colour-graph-audit-2026-08-30.md
  - research/artifacts/stw82-order-zero-spectral-subdivision-audit-2026-08-30.md
  - research/artifacts/stw82-tree-connected-support-covers-audit-2026-08-30.md
  - research/artifacts/stw82-stage-centre-split-audit-2026-08-30.md
  - research/artifacts/stw82-multiplier-projection-reduction-audit-2026-08-30.md
  - research/artifacts/stw82-quasicentral-support-thickening-audit-2026-08-30.md
  - research/artifacts/stw82-finite-spectrum-repair-no-go-audit-2026-08-30.md
  - research/artifacts/stw82-complemented-multiplier-support-audit-2026-08-30.md
---

**Problem LXXXII of Schafhauser--Tikuisis--White,
[arXiv:2506.10902v2](https://arxiv.org/abs/2506.10902).**  Given an arbitrary
extension

```text
0 -> I -> E -> D -> 0,
```

is

```text
dim_nuc(E) = max(dim_nuc(I), dim_nuc(D))?
```

The reverse inequality is automatic because nuclear dimension does not
increase on ideals or quotients.  Winter--Zacharias' general gluing argument
only gives

```text
dim_nuc(E) <= dim_nuc(I) + dim_nuc(D) + 1.
```

There is now an exact comparison invariant below nuclear dimension.
`stw81-continuous-trace-shadow-invariant` defines `ctdim` from the spectrum
dimensions of continuous-trace subquotients, and
`stw81-ctdim-extension-maximum` proves

```text
ctdim(E) = max(ctdim(I),ctdim(D)) <= dim_nuc(E).
```

Thus a counterexample to the formula in this problem cannot be caused by
topological dimension hidden across the extension; it must be a genuinely
noncommutative failure of approximation-color reuse.

As of 2026-08-30 this remains open in the stated generality.  The May 2026
version of the 99-problems paper still asks it.  A search of the primary arXiv
catalogue through that date found no later paper claiming the arbitrary
extension theorem; the latest directly targeted paper remains Evington--Ng--
Sims--White, [arXiv:2409.12872v2](https://arxiv.org/abs/2409.12872), which
proves the maximum formula for extensions with stable Kirchberg ideal and
commutative unital quotient.  Other established positive cases include
separable commutative extensions, AF-by-AF extensions, quasidiagonal
extensions, essential extensions of commutative algebras by the compacts
([Gardner--Tikuisis](https://arxiv.org/abs/2202.04695)), and the special
`O_infinity`-stable cases in
[Evington](https://arxiv.org/abs/2012.03650).

The repository now removes "separable" from the subhomogeneous case:
`stw82-subhomogeneous-maximum` proves
the formula whenever both endpoints are subhomogeneous, with no separability
hypothesis.  In particular, arbitrary commutative extensions obey the
maximum formula.

There is also an exact absorption class which includes nonnuclear middle
algebras.  `stw82-oinfinity-stable-extensions-obey-maximum` proves the
formula for every extension whose separable middle algebra is
`O_infinity`-stable.  Ideals and quotients retain the absorption.  Every
nonzero nuclear term then has nuclear dimension one, while every nonnuclear
term has infinite nuclear dimension; extension permanence of nuclearity
forces the middle term and the endpoint maximum into the same case.  No
fullness, essentiality, splitting, or quasidiagonality hypothesis occurs.

There is also a split class with no regularity assumption on the ideal.
`stw82-central-af-split-extensions-obey-maximum` proves the formula when the
quotient is commutative AF and a unital *-homomorphic section lands in the
centre of the middle algebra.  Finite clopen quotient stages cut the middle
algebra into a direct sum of unitizations of ideal corners, so the ideal's
colours are reused exactly.  Centrality is essential to this proof: a
merely split finite-dimensional quotient need not provide central corner
projections.

This now has a noncommutative strengthening.
`stw82-af-split-centralizer-extensions-obey-maximum` allows an arbitrary AF
quotient and assumes only that the section commutes with the ideal.  At each
finite-dimensional stage, a noncommutative simple matrix block must have
zero ideal corner, because that corner annihilates every commutator and
hence the whole matrix block.  Scalar blocks again give unitized ideal
corners.  Thus the middle algebra still has exactly the nuclear dimension
of the arbitrary ideal.  A merely split extension, with no commutation
between section and ideal, remains outside this argument.

The centralizer hypothesis can now be weakened sharply at
finite-dimensional quotient stages.
`stw82-af-split-stage-centres-obey-maximum` assumes only that the lifted
centres of one finite-dimensional AF exhaustion commute with the ideal.
Central block units first split the stage, while the noncentral lifted
matrix units identify each middle block with a matrix amplification of a
unitized ideal corner.  Hence every ideal colour is reused exactly.  In
particular, **every unital split extension with UHF quotient** obeys the
maximum formula, for an arbitrary ideal and with no commutation between the
matrix part of the section and the ideal.  For a general split AF quotient,
noncentral stage-block units and their off-diagonal ideal corners remain
outside this proof.

That remaining split-AF frontier now has an exact one-projection normal
form.  `stw82-split-af-is-one-multiplier-projection-problem` proves that the
maximum formula for all unital split AF quotients is equivalent to the
apparently smaller assertion

```text
dim_nuc(A+C p)=dim_nuc(A)
```

for every multiplier projection `p` of every C*-algebra `A`; equivalently,
it is enough to handle unital split extensions with quotient
`C direct_sum C`.  A full-corner matrix-unit compression removes all matrix
sizes, and the remaining coordinate projections are adjoined one at a time.
The stage-centre hypothesis is exactly the vanishing of every off-diagonal
Peirce corner.  A nonzero such corner contains a norm-one element whose
commutator with the corresponding block projection has norm one, so the
direct-sum proof cannot cross this boundary by an approximate-centrality
estimate.  Multiplier-projection invariance itself remains open here.
It is unconditional for sigma-unital ideals when the multiplier projection
is full: the adjoined algebra is Morita equivalent to the unitization of the
full hereditary corner.  Thus a split-AF counterexample would necessarily
encounter a nonfull projection and the proper residual quotient left outside
its generated ideal.

The nonfull frontier is now narrower.  The theorem
`stw82-complemented-support-preserves-dimension` proves
the same formula whenever the proper generated ideal
`L=closure(ApA)` is complemented in the sigma-unital algebra `A`.  Indeed,
the projection annihilates the complementary ideal, is full on `L`, and

```text
A+C p=(L+C p) direct_sum L^perp.
```

This permits multiplier projections that are simultaneously nonfull and
noncentral.  Consequently a counterexample to the split-AF formula must pass
through a nonfull projection whose generated ideal is noncomplemented; its
support cannot be a central projection of `M(A)`.

There is now a first theorem on that genuinely noncomplemented side.
`stw82-quasicentral-support-thickening-preserves-dimension` assumes the
generated ideal `L=closure(ApA)` has a projectional approximate unit
quasicentral in `A` and asymptotically commuting with `p`.  Spectral repair
makes those projections commute with `p`; adjoining `p` to each repaired
cut produces a quasicentral approximate unit of projections for `L+C p` in
`A+C p`.  The residual extension by `A/L` is therefore quasidiagonal, so
the quasidiagonal maximum theorem and the full-corner computation on `L`
give

```text
dim_nuc(A+C p)=dim_nuc(A).
```

This includes proper essential generated ideals, which can never be
complemented.  An explicit stabilized-unitization field over `[0,1]` gives
a noncentral, nonfull, noncomplemented example of nuclear dimension one.
The remaining multiplier-support frontier must lack such projectional
quasicentral cuts relative to `p`, so its residual gluing is genuinely
nonquasidiagonal.

The multiplier problem is exactly symmetric in the two complementary
projections.  `stw82-complement-symmetry-and-overlap-reduction` observes that

```text
(A+C p)~=A+C1+C p=A+C1+C(1-p)=(A+C(1-p))~,
```

so unitization invariance gives equal nuclear dimensions.  The full-support
corner theorem therefore applies when **either** `p` or `1-p` is full.  This
already crosses the nonquasidiagonal firewall: in the stabilized Toeplitz
example the support generated by `p` is proper, essential and
noncomplemented and its residual extension has nonzero index, but `1-p` is
full, so adjoining `p` is nevertheless dimension-neutral.

For the genuinely two-sided remainder, put
`L=closure(ApA)`, `R=closure(A(1-p)A)`, and `I=L intersect R`.  Then
`L+R=A`, both complementary projections are full on `I`, and

```text
(A+C p)/I isomorphic to (A/L) direct_sum (A/R)~.
```

Thus the quotient already has nuclear dimension at most `dim_nuc(A)`.  Any
counterexample must have both `L` and `R` proper and a nonzero overlap `I`;
all possible extra colour is localized to gluing across that common ideal,
not to either one-sided support quotient.

The overlap has an exact linking-algebra normal form
(`stw82-overlap-is-a-full-linking-core`).  With `q=1-p`, set

```text
P=pAp, Q=qAq, X=pAq, B=pIp, C=qIq.
```

Then `X` is a full `B`--`C` imprimitivity bimodule and

```text
I=[B X;X* C],       A=[P X;X* Q],       A+C p=[P~ X;X* Q].
```

The residual diagonals are `P/B=A/R` and `Q/C=A/L`.  This identifies the
remaining operation as partial unitization of one diagonal of a generalized
linking algebra.  It also blocks the naive stabilization argument: every
finite frame from `X` has left and right inner products in `B` and `C`, so
it transports colours only across the overlap and cannot norm-approximate a
nonzero class in either residual diagonal quotient.  A complete proof must
coordinate both residual diagonal approximations with those same core
colours; Morita invariance of the full overlap alone is insufficient.

There is nevertheless a relative positive theorem at exactly this core.
`stw82-projectional-overlap-cuts-preserve-dimension` assumes only that
`I=L intersect R` has an approximate unit of projections quasicentral in
`A` and asymptotically commuting with `p`.  These projections are then
quasicentral in `A+C p`, so the overlap extension is quasidiagonal.  Its
quotient is the already-computed direct sum

```text
(A/L) direct_sum (A/R)~,
```

and both quotient and overlap have nuclear dimension at most
`dim_nuc(A)`.  Quasidiagonal-extension permanence therefore gives
`dim_nuc(A+C p)=dim_nuc(A)`.  Unlike the earlier support-thickening theorem,
no projectional exhaustion of either larger one-sided support is required.
The unresolved two-sided frontier must now lack even projectional
quasicentral cuts on its common linking core, or else be genuinely
nonquasidiagonal there.

This relative condition is strictly weaker.  A concrete matrix-linking
example has common overlap `M_2(K)` with diagonal finite-rank quasicentral
cuts, while each one-sided support has quotient `C_0((0,1])` and hence no
approximate unit of projections.  Both supports are proper essential and
noncomplemented, both complementary multiplier projections are nonfull, and
the original and adjoined algebras both have nuclear dimension one.  Thus
overlap-level colour coupling reaches configurations excluded by every
previous full, complemented, and one-sided projectional theorem.

A separate exact colour-reuse mechanism now crosses a genuinely
nonquasidiagonal overlap.  `stw82-stabilized-coefficient-projections` proves
that for every unital `B` and projection `e in B`,

```text
dim_nuc((B tensor K)+C(e tensor 1))=dim_nuc(B tensor K)=dim_nuc(B).
```

Finite-rank coefficient corners leave the tail projection
`e tensor (1-P_n)` completely orthogonal, so every stage is exactly
`(B tensor M_n) direct_sum C`; their nested union is dense.  No
quasicentral cut or transition-band estimate occurs.  Taking `B` to be the
two-symbol Toeplitz algebra with diagonal symbols produces two proper
essential noncomplemented support ideals and a common compact overlap.  A
Toeplitz corner gives a nonzero boundary map for the overlap extension, so
it is not quasidiagonal and has no projectional quasicentral approximate
unit.  Both complementary multiplier projections are nonfull, yet the
adjoined algebra still has nuclear dimension one.  Thus nonquasidiagonality
of the common linking core is not itself an obstruction; stabilized
coefficient tails provide a second exact route across it.

That projectional hypothesis cannot be replaced formally by real rank zero
and arbitrary finite-spectrum positive cuts.
`stw82-finite-spectrum-cuts-do-not-force-repair` constructs a stabilized
Toeplitz multiplier-support example in which `L=closure(ApA)` is proper,
essential, stable AF, and has a finite-spectrum positive quasicentral
approximate unit commuting exactly with `p`.  Nevertheless every nonzero
literal spectral cut has commutator norm one with a fixed shift tensor, and
the residual extension by `A/L` has the nonzero Toeplitz index boundary.
Thus it is not quasidiagonal and no alternative projectional repair exists.
Stagewise spectral gaps alone are therefore insufficient: their size must
quantitatively dominate the incoming commutator error, or a new argument
must absorb the nonquasidiagonal transition band.

There is also a new unconditional middle-algebra class:
`stw82-one-dimensional-middle-forces-maximum` shows that every
ideal--quotient decomposition of an arbitrary algebra `E` with
`dim_nuc(E)<=1` satisfies the maximum formula.  The only possible low-end
failure would have both endpoints of dimension zero; AF extension closure
on the separable counterexample supplied by the reflection theorem rules
this out.  Consequently any counterexample has middle nuclear dimension at
least two.

There is now a concrete nonquasidiagonal coefficient class at that sharp
dimension-one boundary.  For every nonzero separable unital AF algebra `A`
and every `N>=1`, `stw82-af-coefficient-toeplitz-maximum` computes

```text
0 -> K tensor A -> C*(S^N,K) tensor A -> C(T) tensor A -> 0
```

as dimensions `0,1,1`.  The index boundary sends
`[z] tensor [1_A]` to `+-N[1_A]`, so these extensions are not quasidiagonal
and their raw complementary cuts cannot be orthogonalized.  The optimal
bound comes instead from writing `A` as an AF limit: every finite stage is a
finite direct sum of matrix amplifications of the scalar Toeplitz
two-colour construction.  Thus this class exhibits genuine transition-band
absorption beyond the projectional-cut regime.

The project reduction
`stw82-counterexamples-reflect-to-separable-extensions` shows that the word
"arbitrary" does not create a separate nonseparable frontier: every
counterexample would already have a separable subextension counterexample
with no larger endpoint dimensions.

The Busby-kernel reduction
`stw82-every-counterexample-essentializes` removes a second inessential
frontier.  For Busby map `tau`, enlarge the ideal from `I` to the preimage of
`ker(tau)`.  That new ideal is `I directSum ker(tau)`, is essential in the
same middle algebra, and has nuclear dimension no larger than the original
endpoint maximum.  Thus every failure already has a separable extension by
an essential ideal; the unresolved theorem may be attacked in that sharply
reduced setting.

Stabilization sharpens this once more:
`stw82-counterexamples-reduce-to-stable-essential-extensions` proves that a
failure exists if and only if there is a separable stable extension with
essential ideal that fails.  Exactness, all three nuclear dimensions, and
essentiality survive tensoring with the compact operators.  Hence the full
problem can be studied with an injective Busby map into the corona of a
separable stable ideal, without losing any possible counterexample.

There is a second localization from Problem LXXXI.
`stw81-finite-ideal-counterexample-forces-lxxxii-counterexample` shows that a
separable finite-ideal algebra of finite nuclear dimension at least two,
despite having only one-dimensional commutative hereditary shadows in all
quotients, would contain an extension counterexample here whose ideal and
quotient both have nuclear dimension at most one.

## Attempts

The established route
`stw82-separable-maximum-implies-arbitrary-maximum` removes nonseparability
from the problem.  What remains is the separable maximum theorem.  The
standard quasicentral-approximate-unit proof produces disjoint ideal and
quotient approximations but gives their colours separate labels, yielding
the sum-plus-one bound.  Known optimal proofs reuse colours only after
obtaining extra orthogonality from the extension (for example a
quasidiagonal projectional approximate unit, or the classification inputs in
the Kirchberg-ideal cases).  No mechanism currently supplies that
orthogonality for an arbitrary separable extension.

The exact local obstruction is now recorded in
`stw82-order-zero-direct-sum-support-criterion`: two order-zero maps merge by
the direct-sum construction precisely when their unit supports are
orthogonal.  For the complementary supports `h` and `1-h`,
`stw82-complementary-cutdowns-merge-iff-near-projections` proves, with
explicit estimates, that asymptotic orthogonalizability is equivalent to
`h` being asymptotically projectional.  This is not a consequence of
quasicentrality.  Indeed,
`stw82-commutative-max-formula-with-maximal-cutdown-overlap` shows that in
the interval endpoint extension every positive contractive quasicentral
approximate unit has overlap norm exactly `1/4`, although the maximum
formula holds.  Thus the unresolved gluing step must reorganize the colour
maps or absorb their transition region; perturbing the two raw cuts cannot
be a general proof.

The global form of this barrier is now exact.
`stw82-raw-two-cut-reuse-iff-quasidiagonal` proves that a separable
extension admits an asymptotically projectional quasicentral approximate
unit -- equivalently, its two raw complementary supports can be perturbed
to orthogonal supports -- if and only if the extension is quasidiagonal.
So raw-cut perturbation cannot enlarge the already known quasidiagonal
positive class.  After the separable/stable/essential reductions, the exact
remaining hinge is to redistribute the transition band among the endpoint
colours in a non-quasidiagonal extension, as the known optimal proofs do
using special classification input.

The transition-band obstruction has now been sharpened beyond one pair of
cuts.  `stw82-indivisible-order-zero-reuse-is-graph-colouring` proves that
for any finite family of fixed outgoing order-zero maps, the least number of
global colours obtainable by direct-sum relabelling is exactly the chromatic
number of the graph whose edges are nonorthogonal support pairs.  Thus a
fixed-map two-colour merger exists exactly when this support graph is
bipartite.  This is also an unconditional colour-reuse theorem: a family of
finite-dimensional approximations whose support graphs are uniformly
`(r+1)`-colourable compiles directly into nuclear dimension at most `r`,
with no additional colour.

Moreover, `stw82-two-by-two-colour-reuse-quantitative-obstruction` gives a
norm lower bound for perturbing two ideal and two quotient/transition
colours into any two-colour assignment.  It tests both internal support
overlaps and both possible cross matchings, and remains valid when the
assignment varies with the approximation stage.  Hence an odd-cycle or
positive matching obstruction cannot be removed by relabelling intact
colours.  The general quantitative form
`stw82-odd-support-cycle-stable-two-colour-obstruction` shows that an odd
cycle whose edge overlaps stay uniformly positive forces a fixed positive
perturbation error for every stage-dependent two-colour assignment.  This
still does not decide the problem: a universal proof may
split or replace the transition-band maps, as all known non-quasidiagonal
optimal proofs do under additional classification hypotheses.

There is nevertheless a genuinely nonprojectional positive colour-reuse
mechanism.  `stw82-spectral-interval-band-depth-reuses-colours` proves that
when the outgoing unit supports are functions of one positive contraction,
localized in spectral intervals of overlap depth `r+1`, the unchanged maps
regroup into `r+1` order-zero colours.  Thus any approximation scheme with
such band depth proves nuclear dimension at most `r`, exactly.  This moves
the universal hinge again: the missing theorem is a structure-free way to
subdivide arbitrary transition maps into common-cut spectral bands while
preserving their order-zero structure and approximation quality.

That local subdivision problem is now solved.
`stw82-quasicentral-cutdowns-repair-to-banded-order-zero` proves that a
finite-dimensional outgoing order-zero map can be cut by any finite
quasicentral multiplier partition of unity and perturbed, inside the
corresponding hereditary band algebras, to exact order-zero maps whose sum
approximates the original map.  The proof uses projectivity of the cone over
a finite-dimensional algebra, and requires no projectional cut or extension
regularity.

There is also an exact limitation.
`stw82-scalar-band-depth-floor` proves
that independently subdividing `N` original colours by scalar partitions of
unity produces band depth at least `N` at every spectral point.  Thus doing
this separately to all endpoint colours cannot improve the sum of their
colour counts to the desired maximum.  The remaining universal hinge is a
support-sensitive **coupled** subdivision: it must exploit operator
orthogonality or support vanishing across different endpoint colours, not
only scalar partitions of the common cut variable.

The local coupled construction is now exact.
`stw82-coupled-operator-partitions-merge-colours` allows every original
order-zero colour to use its own quasicentral operator-valued partition and
repairs all cutdowns inside their hereditary supports.  If pieces carrying
the same new label are orthogonal across original colours, they merge into
one global order-zero map.  This bypasses the scalar depth floor and reduces
the universal extension problem to constructing these coupled partitions
from ideal--quotient geometry.  However, a second obstruction shows that
partitioning the **whole multiplier unit** is still too strong:
`stw82-traces-block-unit-coupled-colour-reduction` proves by a tracial
double count that `d` such labels can cover at most `d` original colours.
Thus the full-unit version cannot reduce colours in a tracial middle
algebra.

The support-relative repair is now also exact.
`stw82-support-local-coupled-covers-merge-colours` replaces the full-unit
partition identity by the strictly weaker requirement that the sum of one
colour's cutters act as the identity only on its order-zero support.  The
same cone-projective repair and orthogonal-band merger work.  This removes
the tracial counting barrier and identifies the sharp remaining global
hinge: construct same-labelled orthogonal cutters which cover each outgoing
support, not the whole multiplier unit, from arbitrary extension geometry.

Two new capacity results delimit that hinge.  Exact norm coverage charges
the whole range projection of each outgoing support, not merely its tracial
amplitude: `stw82-spectral-support-hall-capacity` proves weighted Hall
inequalities for support projections and approximate inequalities for upper
spectral cuts.  Complementary scalar supports already show that total
amplitude at most `max(p,q)+1` is not sufficient.  Even all such support
trace inequalities are not sufficient.  By
`stw82-minimal-support-coupled-cover-number`, arbitrary operator-valued
subdivision of minimal supports has exact label capacity equal to the
chromatic number of their nonorthogonality graph.  Three rank-one supports
in `M_2` pass every two-label span-capacity inequality but form a triangle
and require three labels.  These are fixed-family local obstructions, not
extension counterexamples: a universal proof may still replace the outgoing
maps.  It must, however, control noncommutative support incidence in addition
to tracial capacity.

There is now a positive replacement theorem which can remove that incidence
obstruction.  `stw82-zero-dimensional-central-supports-recolour-pointwise`
shows that, when the outgoing supports lie in a common zero-dimensional
abelian multiplier algebra centralizing all outgoing ranges, their optimal
asymptotic coupled-cover number is the maximum number active at one spectral
point.  A clopen refinement permits the label matching to vary from block to
block, and central projection cutdowns preserve order zero exactly.  Thus
three supports whose global overlap graph is a triangle can split and
recombine into two colours when its three edges occur on different central
atoms.  Any nuclear approximation scheme with pointwise multiplicity at
most `r+1` therefore proves nuclear dimension at most `r`.  What remains
unknown for arbitrary extensions is whether their outgoing approximations
can always be replaced by ones with this central zero-dimensional geometry;
the tracial Hall bounds alone do not provide such a replacement.

Finite-dimensional support spectra now also have an explicit replacement
bound.  `stw82-finite-dimensional-central-spectrum-colour-bound` combines
Ostrand's discrete-family characterization of covering dimension with the
pointwise support matching above.  If the common compact metrizable support
spectrum has dimension at most `n` and at most `m` outgoing supports are
active at any point, the family splits, to arbitrary accuracy, into
`(n+1)m` order-zero colours.  The partition-of-unity omission error is still
the chosen tolerance, with no cover-cardinality loss, while discreteness
makes equal-labelled cutters exactly orthogonal.  Thus any nuclear
approximation scheme with this geometry gives
`dim_nuc(A)<=(n+1)m-1`.  This is a rigorous positive selection theorem, not
an assertion that arbitrary essential extensions admit the required common
support algebra or that the product bound is sharp for `n>0`.

The one-dimensional product loss can now be removed for a concrete support
geometry.  `stw82-tree-connected-supports-have-optimal-covers` proves that
outgoing supports in a common centralizing compact-R-tree algebra admit
asymptotically exact support-local coupled covers using only their maximum
pointwise multiplicity `m`, with no connectedness hypothesis.  At each
tolerance, only finitely many cozero components meet an upper spectral cut;
Urysohn cutters localize to those components, their subtree graph is
`m`-colourable, and the pieces are regrouped by colour.  This can reduce a
global `K_3` support-overlap graph to two colours, so it genuinely reorganizes
the outgoing maps rather than recolouring them intact.  Approximation schemes
of this kind with depth at most `r+1` prove nuclear dimension at most `r`,
improving the general one-dimensional central-spectrum bound from `2m` to
`m`.  For connected cozero supports the common-centralizer hypothesis remains
unnecessary, recovering the earlier theorem.  This is an identifiable
positive class, not a claim that arbitrary essential extensions have compact
R-tree support geometry.
