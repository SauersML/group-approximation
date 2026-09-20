# Hyperbolic residual finiteness: independent stability-path audit

2026-09-20. Written mathematical audit; no Lean certification. The GHB7
stability premise and existence of a non-residually-finite hyperbolic group
remain open. This artifact records two proved conditional statements and an
independent review of the simultaneous expanding-block reduction.

## 1. The advertised implication chain survives this audit

The chain under review is one-edge absorption for `G=G_HB2(7)`, flexible HS
stability of `G`, descent to the finite-index congruence kernel `H`, and the
production of a nonhyperlinear finite central extension of `H`.

The finite-index descent proof in
`flexible-hs-stability-descends-to-retracts-finite-index-proof` is valid with its
Kazhdan hypothesis. Induce a model of `H` to `G`; after rounding, the original
coset projection approximately commutes with the restricted genuine
representation. Property (T) of `H` gives a nearby invariant projection. Its
rank differs from the original by `o(d)`, and polar comparison plus a trivial
summand supplies a genuine representation in dimension `d+o(d)`. The property
(T) step is essential; the argument does not assert arbitrary finite-index
descent without it.

The congruence kernel's positive second rational Betti number supplies an
integral central extension with finite abelianization. More explicitly, select
a cohomology class with nonzero evaluation `H_2(H;Z)->Z`. The homology five-term
sequence makes the cover's abelianization finite. This does not require the
class to be primitive. Finiteness of presentation ensures the homology group
is finitely generated and that positive rational rank is an integral free
direction.

The source for the final analytic step must be version-pinned:
[Dogon--Vigdorovich v2](https://arxiv.org/html/2506.20843v2), dated 2026-06-23,
Theorem 1.3, concludes that some finite central quotient is nonhyperlinear.
Version 1, Theorem 1.5, concludes nonhyperlinearity of the infinite cyclic
cover instead. The distinction matters because the infinite cyclic cover
need not be hyperbolic. Version 2's Definition 1.2 uses the flexible metric,
so the graph's use of flexible stability is appropriate. This audit reread
the theorem and definition, not the complete proof of that published input.

For precision, the source's distance between `u in U(d)` and `v in U(D)` is
`||u direct-sum 0-v||_{2,D}`. It forces `D/d->1`: its square is at least
`(D-d)/D`. Conversely compression convergence together with `D/d->1` implies
source-metric convergence, since

```
||u direct-sum 0-v||_{2,D}^2
 <= (d/D)||u-PvP*||_{2,d}^2 + 2(D-d)/D.
```

Thus the two conventions agree; allowing arbitrary `D>=d` without the
source-metric condition would be a materially different statement.

The hyperbolicity and property-(T) candidate is imported from
[Caprace--Conder--Kaluba--Witzel](https://arxiv.org/abs/2011.09276), Theorem 1.3
and the generalized-triangle structure theorem, as explicitly recorded in
`cckw-ghb2-kms-group-structure`. The existence of the finite quotient is not
an assertion of residual finiteness. A finite-kernel surjection of finitely
generated groups is a quasi-isometry, which justifies hyperbolicity of the
finite central extension, not of an arbitrary infinite central cover.

## 2. A shorter route suffices for residual finiteness alone

The new conditional theorem
`hrf-audit-stability-forces-prime-central-finite-residuals` avoids the stronger
nonhyperlinearity target. Its complete proof is in the paired proof route.

Let a flexibly stable group `Gamma` have a Kazhdan central integral cover `E`.
If the central generator survives at orders `m_n->infinity` in finite
quotients, take the central eigenvalue `exp(2 pi i/m_n)` sector of each finite
regular representation. Section pullback gives asymptotic projective
representations of `Gamma`. Flexible rounding would make a rectangular
intertwiner an almost invariant unit vector for `E`, whereas the centre acts
on the entire intertwiner space by a nontrivial scalar. This contradicts
property (T) of `E`.

Hence there is `M>=1` such that every finite quotient of `E` kills `z^M`.
For every prime `p` not dividing `M`, all finite quotients of `E/<z^p>` kill its
entire nontrivial central `C_p`. The mod-p extension class cannot split over
any finite-index subgroup: such a splitting, followed by taking its normal
core, would yield a finite quotient detecting that centre.

This proves a stronger profinite conclusion than merely existence of one
bad finite central quotient, while making a weaker approximation claim: it
does not prove nonhyperlinearity. It works without assuming hyperlinearity or
residual finiteness of the base. If the base is also residually finite, its
prime quotients give instances of the existing persistent-class target.

The central-cover property-(T) criterion used to construct `E` is
Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Theorem 1.7.11, as
recorded in `bdhv-central-extension-property-t`. I also downloaded the
[authors' book PDF](https://perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf)
and checked Theorem 1.7.11 and its proof on printed page 72 directly. The
standard construction
from positive `b_2` was rederived above. The finite-dimensional obstruction
is the same mechanism already present in Cairn's visible-centre and
Kazhdan-cover nodes; no new-priority claim is made.

**What has not happened:** no bound `M` has been computed for GHB7 or its
kernel, no finite central quotient has been proved non-RF, and the stability
hypothesis remains open. The theorem shortens the implication chain; it
does not establish its missing premise.

Independent cross-review by the alternative-route lane returned **PASS** for
the rectangular-norm split, central scalar exclusion, Kazhdan contradiction,
lcm bound, every-prime persistence conclusion, and integral-cover construction.
The review also checked the equivalence of the flexible metric conventions.

## 3. Exact internal commutants and scalar expansion do not imply rounding

The new node `hrf-audit-projective-internality-does-not-round` identifies a
precise obstruction to overusing the newly accepted Liu theorem.

For any scalar-projective representation `alpha:Gamma->U(d)`, the adjoint
action `Ad alpha` is a genuine representation. If `Gamma` is Kazhdan, its
fixed Kazhdan pair gives

```
||X-E_{alpha(Gamma)'}(X)||_2
 <= kappa^{-1} max_{g in F} ||[alpha(g),X]||_2.
```

Consequently a sequence whose multipliers tend to one has an ultraproduct
commutant equal to the ultraproduct of its *original exact* coordinate
commutants. No use of Liu's theorem is needed for this special case.

Nonetheless the existing affine symplectic example
`Gamma=Z^{2g} semidirect Sp_{2g}(Z)`, `g>=2`, has nonroundable models of exactly
this form. Whole central eigenspaces give a regular limiting trace. Selecting
one irreducible constituent of each eigenspace gives a stronger gap example:
the exact coordinate commutant is scalar and the original generators have
one uniform scalar conjugation gap, yet the models still do not round.

The selected dimensions go to infinity without an extra compactness premise.
If `A` is the exponent of the finite abelianization of the Kazhdan cover,
and its central eigenvalue is `exp(2 pi i/n)` in dimension `r_n`, determinant
gives `n | A r_n`, hence `r_n>=n/A`. Regular trace is not asserted after this
arbitrary irreducible selection. The operator-norm relator defects still
tend to zero. The group contains `Z^2`, so this does not refute GHB7 stability.

This is a useful falsification test: neither internality, nor original-
coordinate adjoint gap, nor even scalar expansion can alone finish a
dimension-uniform rounding argument. GHB7-specific relator or cohomology
input must enter. This does not contradict localization to scalar expanders.

The alternative-route lane independently reviewed this deduction and returned
**PASS**, retaining the older affine-symplectic construction as an explicit
input. That review checked the adjoint cancellation, conditional-expectation
lifts, determinant dimension bound, scalar commutants and inherited
nonroundability. This audit separately reread the older construction's written
proof; neither review claims a new verification of all its literature inputs.

## 4. Independent review of the simultaneous Liu localization

Reviewed `research/artifacts/hyperbolic-rf-ghb7-2026-09-20.md`, Sections 1--4,
against the exact interface `quotient-gap-gives-large-scalar-expanding-blocks`.
**Conditional PASS**, with Liu's theorem retained as the named analytic
premise. The following points were checked independently:

- A fixed presentation turns small relator defects into asymptotic
  representations by word telescoping; the converse implication is direct.
- The proposed rounding cost includes both dimension inflation and generator
  compression error, so its uniform-modulus formulation really matches
  sequential flexible stability.
- For an alleged failure of size `eta`, the discarded fraction `epsilon`
  and the rounding tolerance are fixed before selecting the block gap `c`.
  No uniform lower bound as `epsilon->0` is used.
- Relator defects add in squared normalized HS norm with physical dimension
  weights. Markov therefore discards only a vanishing physical fraction of
  relator-bad retained blocks, independently of how many there are.
- Direct sums add dimension inflation linearly and squared errors by the
  same weights. Trivial representations on the discarded part cost at most
  twice the square root of its trace. These estimates contradict the fixed
  macroscopic failure bound.
- Both nearby copies of each generator remain in the scalar-gap condition.
  No stability of that gap under normalized-HS vertex rounding is assumed.
- Compactness at each fixed dimension rules out a bounded-dimensional
  failure sequence.

The projective example in Section 3 confirms the exact scope: localization
is a valid narrowing of the problem, not evidence that the remaining
scalar-expander rounding assertion holds for all Kazhdan groups.

The matching lane's subsequent Sections 7--8 were also independently checked
and **PASS**. The general Hopf-sequence proof is valid: scalar relators give
a character of `N/[F,N]`; finite `H_2` is eventually killed; a Smith basis
extends the resulting near-trivial character of a sublattice to a
near-trivial character of the free abelianization.

The more specific integral calculation checks out. In the equivariant
homology spectral sequence for the CCKW triangle, `E^2_(1,1)=0` because
the incident edge classes are a basis of each vertex abelianization;
`E^2_(2,0)=0` because the quotient is a filled triangle; and
`E^2_(0,2)` is the sum of vertex `H_2` groups, since the edge groups are
cyclic. The only potentially incoming higher differential is the `d^2`
from `(2,1)`, whose source vanishes because the face stabilizer is trivial.
Thus vertex inclusions identify `H_2(GHB7;Z)` with that vertex sum. Transfer
annihilates the summands by their orders, which divide 2401.

Each of the eight iterated-commutator relators has zero exponent-sum vector,
so its class in the Hopf sequence lies in this 2401-torsion subgroup. If
its exact scalar value is closer than `2 sin(pi/2401)` to 1, it must
already be 1. Correcting the three seventh-power phases then supplies
an honest representation in the same dimension, with operator-norm error
at most `(pi/14) delta`. The doubled-tuple estimate adds the copy mismatch
and is likewise correct.

This proved GHB7 subclass is compatible with Section 3: the affine example
does not have finite second homology. GHB7's congruence kernel has positive
second Betti number, and induced projective models can have block-scalar
rather than globally scalar relator values. The new theorem therefore does
not settle the remaining general scalar-expander rounding assertion.

The later **Section 10 exact-central-relator extension** and both canonical
nodes `hrf-ghb7-central-relator-models-round-strictly` and its proof route
were independently reread and **PASS**. Exact centrality makes the eleven
normal relator matrices commute with each other and makes their simultaneous
eigenspaces reduce every generator. The Hopf argument puts all commutator
phases on each eigenspace among the 2401st roots, with no smallness condition.
Writing `delta_0=2 sin(pi/2401)`, the physical mass of sectors with any
nontrivial commutator phase is at most

```
delta_0^-2 sum_(eight commutator relators r) ||r(U)-I||_2^2.
```

Scalar seventh-root correction on the remaining sectors and trivial
representations on those bad sectors preserve the total dimension. Squared
HS errors add over the invariant sectors. The resulting bound is exactly

```
||pi(s)-U_s||_2^2
 <= (pi/14)^2 ||U_s^7-I||_2^2
      + 4 delta_0^-2 sum_(eight commutator relators r) ||r(U)-I||_2^2.
```

The doubled asymptotic version follows once both plus-relator defects and
copy-equality defects tend to zero; copy defects need not be central.
No gap-preserving perturbation or claim about approximately central relators
is smuggled into this argument. If generators permute the apparent blocks,
block-scalar relator values need not be central, so that unhandled case stays
open.

## 5. Review of the alternative finite-detector lane

Independently read both `hrf-alt` proof routes. The Schur-multiplier detector
map is valid: vertex lifts exist by vanishing of vertex `H^2`, are unique
by perfectness, and their edge differences are central characters. Baer
addition gives linearity. A finite central detector gives exactly a finite
base quotient and such a discrepancy, and conversely the vertex maps produce
the detector. Perfectness of the quotient justifies removal of the Ext term
in universal coefficients. The refinement argument makes the union of images
a vector subspace.

The first-level restriction argument is also correct: `H^1(N;F_p)=0` makes a
splitting over `N` unique, hence normal under the whole extension. It descends
to the finite base quotient, and vanishing there forces global splitting.
One scope correction was sent to the author: the subsequent *moment-space*
corollary additionally needs a torsion-free kernel, or equivalently a
vertex-injective quotient in this triangle setting. That is a hypothesis of
the imported moment theorem; the abstract restriction-injectivity theorem
does not require it. The recorded finite-table applications already have
vertex injectivity. The author added this hypothesis to the claim and proof;
with that correction both alternative-route theorems pass this review.

The Sylow-detour proof is valid: pass to the normal core of a vanishing
subgroup, take a Sylow preimage in its finite quotient, and pull back a
composition series. Restriction through the prime-to-p first step is
injective by transfer. The `A_5` example correctly separates absence of
p-quotients at the original base from absence of p-towers after a detour.
Its double extension is nonsplit because `SL_2(F_5)` has only one
nonidentity involution, the central one. No infinite-group conclusion is
inferred from that finite calibration.

The cyclic-Sylow check for the listed `PSL_2(q)` first quotients is also
consistent: the indicated odd primes are nondefining characteristic,
their Sylow subgroup is cyclic in a torus, and the Weyl normalizer element
acts by inversion. The invariant part of `H^2(C_{p^a};F_p)` is zero, since
inversion acts by `-1`. Thus the first-level full moment rank is forced by
the two vanishing hypotheses; it is not independent evidence of persistence.

I additionally checked the composition-series argument in
`hrf-alt-psl2-detector-composition-obstruction-proof`: simultaneous vanishing
of `H^1(-;F_p)` and `H^2(-;F_p)` is closed under finite extensions. The
unique lift of the kernel in any central extension is normal, which reduces
splitting to the quotient. Subdirect product images of surjective maps onto
the listed simple groups have only those simple composition factors.

The written broadening to **all** `PSL_2(q)` at primes `p>=5` also passes
the algebraic check. In cross-characteristic a Sylow p-subgroup is cyclic
and its normalizer supplies inversion, annihilating invariant degree-one
and degree-two classes. In defining characteristic `q=p^f`, extend scalars
to an algebraic closure of `F_p`. The diagonal torus acts on degree-one
cohomology of the additive Sylow subgroup with characters `t^(-2p^i)`.
The degree-two Bockstein part has the same weights, and the exterior part
has weights `t^(-2(p^i+p^j))`, `i<j`. Their positive exponent magnitudes
are strictly between zero and `q-1` for `p>=5`; the exterior part is
empty if `f=1`. Hence there are no torus invariants, and restriction to
the Sylow subgroup is injective by transfer. If p does not divide the
group order, transfer already gives vanishing. The argument includes
the small q cases and needs no Schur-multiplier table.

The final alternative-route proof replaces the Bockstein decomposition by an
elementary argument that I also checked: a central extension of the additive
Sylow subgroup has a natural alternating commutator map `b` and a natural
additive pth-power map `h`. The pth-power map is additive because the extension
has class at most two and p divides `binom(p,2)`. When both vanish the total
group is elementary abelian, hence the extension splits as a vector-space
extension. Thus it suffices to exclude invariant `b,h`, with the same torus
weights. This establishes the stated vanishing without importing the full
cohomology-ring description. The final claim and full proof were reread and
the author received an independent **PASS**.

This allows excluding detector-base quotients assembled from any PSL2
simple factors and prime-to-p cyclic factors. It still leaves a possible
`C_p` composition factor in a solvable radical, and non-PSL2 simple
factors; perfectness of the full quotient does not eliminate its radical.

## 6. Validation boundary

The four new `hrf-audit` canonical nodes parsed with Cairn's actual loader;
all route-schema checks and owned artifact-path checks passed, with no parse
errors in the loaded graph. This is schema validation only. No numerical
experiment was needed for these finite-dimensional arguments, and no
computer search or Lean theorem is offered as evidence for the unresolved
GHB7 stability premise. Cairn `why --json` also derives both new audit claims
as ESTABLISHED through their explicit routes and named inputs; this checks
wiring, not mathematical truth. The whole graph still emitted unrelated
warnings during those queries.
