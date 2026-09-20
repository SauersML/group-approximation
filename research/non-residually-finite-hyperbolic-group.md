---
rg: 2
id: non-residually-finite-hyperbolic-group
kind: claim
title: A word-hyperbolic group that is not residually finite
root: true
distinct_from:
  oyakawa-graph-wreath-rf-iff-acting-group-rf: that is an established equivalence inside one construction, saying that a residual finiteness failure there is always inherited from the acting group; this is the open existence question that construction was hoped to settle, and the equivalence is precisely why it does not
  persistent-degree-two-class-on-hyperbolic-group: that is the cohomological input to one of the four live routes, a statement about classes and finite-index subgroups of a group already known to be residually finite; this is the counterexample target itself, which three other routes reach without any cohomology
  exact-stably-finite-non-mf-reduced-group-algebra: that is a proved C-star statement about the quotient witness W — exact, stably finite, not MF; this is an open group-theoretic existence question about hyperbolic groups and their finite quotients, and no operator algebra appears in it
  nonsofic-hyperbolic-group: that claim demands a hyperbolic group that is not sofic, which is strictly stronger — non-soficity implies failure of residual finiteness, but this claim is also satisfied by a group that is sofic and not residually finite, which is exactly the shape of this repository's own literal group E
artifacts:
  - research/artifacts/final-research-handoff-2026-09-20.md
  - research/artifacts/hyperbolic-rf-wave5-summary-2026-09-20.md
  - research/artifacts/hrf-stability-next-gap-rounding-2026-09-20.md
  - research/artifacts/hrf-stability-next-single-core-2026-09-20.md
  - notes/hrf-stability-next-iteration-audit-2026-09-20.md
  - research/artifacts/hyperbolic-rf-wave4-summary-2026-09-20.md
  - research/artifacts/hyperbolic-rf-wave3-summary-2026-09-20.md
  - research/artifacts/hyperbolic-rf-wave2-summary-2026-09-20.md
  - research/artifacts/hyperbolic-rf-campaign-2026-09-20.md
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
  - research/artifacts/high-impact-literature-roots-audit-2026-08-31.md
  - research/artifacts/periodic-higman-cofinite-spectrum-2026-09-04.md
  - research/artifacts/periodic-higman-all-primes-2026-09-05.md
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

Produce a word-hyperbolic group that is not residually finite, or prove that
none exists.

This is the long-standing question usually attributed to Gromov.  It remains
open in the primary sources rechecked on 2026-09-07: Cui--Wan,
arXiv:2604.04007 (5 April 2026), say in their
§1.2 that residual finiteness of every hyperbolic group is still an open
conjecture.  None of the constructions recorded below changes that status.

## Why it sits in this program

Two of this program's objects sit directly above and below it.

Above: `nonsofic-hyperbolic-group`.  A non-sofic group is never residually
finite, so a non-sofic hyperbolic group settles this claim as a corollary
(`non-rf-hyperbolic-from-nonsofic-hyperbolic`).  That is the *only* logical
traffic between the two, and it runs one way.  The graph carries the weaker
demand separately because three of the four live attacks below reach it
without saying anything about soficity, and because the converse fails —
this repository's own literal group `E` is sofic and not residually finite
(`literal-group-sofic`, `literal-mark-quotient-finite-residual`), so a
non-residually-finite hyperbolic group need not be a second non-soficity
mechanism.

Below: nothing.  A resolution in the *positive* direction — every hyperbolic
group is residually finite — would not close any hole in this graph either;
it would remove `nonsofic-hyperbolic-group` as a Q3.4 candidate, since
residually finite groups are sofic.

## Attempts

Four live routes, none of which this graph can yet walk:

- `non-rf-hyperbolic-from-nonsofic-hyperbolic` — inherit it from a non-sofic
  hyperbolic group.  Blocked exactly where `nonsofic-hyperbolic-group` is
  blocked, i.e. on the Chapman--Peled estimate.
- `non-rf-hyperbolic-via-relative-dehn-filling` — build the counterexample
  *relatively* hyperbolic with residually finite peripherals and fill.  The
  filling step is proved; the input claim
  `non-rf-relatively-hyperbolic-with-rf-peripherals` is open and, by that very
  reduction, is not easier than this one.
- `non-rf-hyperbolic-via-persistent-central-extension` — a finite central
  extension of a residually finite hyperbolic group whose class survives
  restriction to every finite-index subgroup.  The criterion is classical and
  established here (`finite-central-extension-rf-iff-virtually-splits`); the
  cohomological input `persistent-degree-two-class-on-hyperbolic-group` is
  open, and the nearest arithmetic sources push the other way.
- `non-rf-hyperbolic-via-rips-kernel` — a hyperbolic Rips extension of a
  non-residually-finite quotient whose kernel has no finite quotients.
  Belegradek--Osin supply everything except the kernel condition, and that
  condition is `rips-kernel-without-finite-quotients`, which is open and
  adjacent to circularity.

Four older attacks are recorded dead, each with its own route and its own
obstruction: transplanting this program's finite-residual compression witness
into a hyperbolic ambient group
(`non-rf-hyperbolic-via-compression-transplant`), its free-lamp repair
(`non-rf-hyperbolic-via-free-lamp-compression`), Oyakawa's hyperbolic
graph-wreath products (`non-rf-hyperbolic-via-oyakawa-graph-wreath`), and
routing a known non-residually-finite group through Hull's small-cancellation
theorem (`non-rf-hyperbolic-via-hull-routing`).

The periodic-Higman missing-period route is now dead as well.
`periodic-higman-spectrum-contains-every-prime`, proved on 2026-09-05,
puts every prime in the spectrum, refuting
`periodic-higman-large-prime-period-gap` and invalidating
`non-rf-hyperbolic-via-periodic-higman`. Every filling `G_m` with `m>=2`
has a finite quotient detecting all four base generators. The proof uses
explicit algebraic matrices, a primitive-divisor theorem, certified root
bounds, exact resultants, and an order-two model in `PSL_2(5)`.

An earlier shortcut had already failed:
`periodic-higman-spectrum-contains-three` gives an exact
`PSL_2(11)` certificate with period three, refuting
`periodic-higman-spectrum-has-no-odd-primes` and invalidating
`non-rf-hyperbolic-via-odd-period-exclusion`.  Borisov--Sapir's residual
finiteness theorem for the *unfilled* injective free-group mapping torus is a
second consistency check: the torsion filling is indispensable, not a
cosmetic step.

This root remains OPEN. The periodic-Higman missing-period premise is
refuted. The finite quotients just constructed do not prove that these
fillings are residually finite: separation of arbitrary nonidentity words
is still unproved.

The finite-kernel approach now has an exact scope:
[[finite-kernel-nonrf-has-central-prime-reduction]] and
[[finite-hyperbolic-residual-iff-persistent-class]] prove that it is
equivalent to finding a hyperbolic group with finite nontrivial finite
residual. The reduction isolates the invisible kernel before taking a
prime quotient, and applies even when the original finite kernel is
noncentral. This supplies no such group and no treatment of an arbitrary
infinite residual. The full proof and the correction to the explanatory
finite-index inclusion are recorded in the new artifact.

**2026-09-11: this root and Lück's virtual torsion-freeness root are one
question.** [[hyperbolic-rf-question-equals-vtf-question]] proves that a
non-residually-finite hyperbolic group exists iff a non-virtually-torsion-free
one does; a deep Dehn filling of a residual element of infinite order turns it
into invisible torsion. The routes
`non-vtf-hyperbolic-via-residual-cyclic-filling`,
`non-rf-hyperbolic-from-non-vtf-hyperbolic`,
`residual-prime-torsion-via-free-factor` and
`non-rf-hyperbolic-from-residual-prime-torsion` record the equivalence cycle.
The strongest equivalent shape is
[[hyperbolic-group-trivial-radical-residual-prime-torsion]]: trivial finite
radical, prime-order torsion in the finite residual, and hence a non-elementary
finite residual. In particular, excluding persistent degree-two classes (the
finite-residual shape above) would not settle this root: a free factor `Z`
converts a finite residual into an infinite one.

**2026-09-11 audit: the first three hyperbolic assertions are equivalent;
the MF extension is unresolved.**
[[hyperbolic-rf-vtf-kazhdan-equivalence]] proves that a non-residually-finite
hyperbolic group exists iff a non-virtually-torsion-free one exists iff an
infinite hyperbolic Kazhdan group without nontrivial finite quotients exists.
A non-MF hyperbolic group would imply all three, because residually finite
groups are MF. The former reverse implication used an unsupported passage
from MF to weak quasidiagonality. Therefore
[[hyperbolic-rf-question-equals-non-mf-question]] is an open four-way target,
not an established extension of this equivalence. The full audited proofs
and the exact MF gap are in
`research/artifacts/hyperbolic-four-statements-audit-2026-09-11.md`.

**2026-09-17: Rips-type extensions carry no invisibility from their base.**
[[hyperbolic-rf-kernel-confines-residual-to-centralizer]] proves
that if a hyperbolic group has an infinite, finitely generated, residually
finite normal subgroup `N`, then its finite residual lies in the finite
normal subgroup `C_G(N)`. Consequences:

- A torsion-free hyperbolic Rips extension, over any finitely presented
  base, is a counterexample exactly when its kernel is not residually
  finite. No choice of base changes this: quotientless, acyclic,
  Deligne-type, with a nonzero Schur multiplier, or not residually finite.
- Every counterexample with infinite residual has all such normal
  subgroups not residually finite.
- Any other counterexample falls under the finite-residual shape.

This closes the Rips family as a route to a torsion-free counterexample.
The cross-class question on
[[torsion-free-non-residually-finite-hyperbolic-group]] stays open.

A literature pointer on the same passage: Bridson--Wilton, *The triviality
problem for profinite completions*, Invent. Math. 202 (2015), arXiv:1401.2273,
the paper's final theorem (label `t:mainHyp` in the arXiv source, read
2026-09-17). It proves that this root is
equivalent to the undecidability of `Ĝ ≅ 1` for hyperbolic presentations.
The equivalence holds within the torsion-free class as well. The proof
feeds a quotientless hyperbolic input into Belegradek--Osin, so it gives no
transfer from a counterexample with torsion to a torsion-free one.


**2026-09-20 coordinated campaign: still OPEN.**
The campaign artifact records independently reviewed quadratic edge
preprocessing, a GHB7 scalar-relator rounding theorem, localization to
an equivalent scalar-expander rounding problem, and finite-detector
obstructions. The new direct route
`hrf-nonrf-via-stable-kazhdan-central-prime` reaches this root from the
OPEN stable hyperbolic Kazhdan positive-b2 premise without passing
through nonhyperlinearity. No result in that campaign establishes the
stability premise or constructs a hyperbolic counterexample.


**2026-09-20 second parallel campaign and supplied proof attempt.**
The user's finite-support proof is now recorded as
`wave2-finite-lamp-wreath-hyperbolic-subgroups-are-rf`: no hyperbolic
subgroup of the supplied finite-lamp wreath over its RF actor is a
counterexample. The accompanying
`wave2-split-locally-finite-residuals-coincide`
prevents transporting any existing finite-residual element to a
nontrivial hyperbolic image. These conclusions do not assert that all
hyperbolic quotients are RF. The supplied Deligne/Rips construction still
needs `hyperbolic-finite-images-exclude-a-central-prime`, an existence
condition already equivalent to this root for each fixed prime.

The independent new computation
`wave2-detector-psl19-perfect-first-kernel` pins an explicit hyperbolic
triangle and proves its first kernel has zero integral abelianization.
`wave2-detector-psl19-no-solvable-refinements` excludes every solvable-kernel
finite refinement over that canonical quotient, also for its nonzero
central five-twists. Nonsolvable refinements remain; the root is OPEN.

**2026-09-20 third parallel campaign: exact progress, still OPEN.**
`wave3-detector-psl19-square-kernel-retains-five-twists` proves that all
three independent central five-twists remain nonzero on the specified
second cover, the kernel of the combined map to `PSL_2(19)^2`. Three
explicit 400-coordinate certificates establish this assertion. It does
not quantify over further covers.

`wave3-canonical-k7-class-has-primitive-evaluation` proves that the
specified integral face-zero class has evaluation ideal `Z`. Its central
generator therefore lies in the commutator subgroup; every finite
detector must obtain its central cyclic image as a quotient of the
Schur multiplier of its finite base image.
`wave3-visibility-cckw-matrix-maps-lift-to-steinberg` excludes the stable
Steinberg detector construction even for noncommuting block parameters.
Neither result bounds all finite central images. The H31 audit separately
classifies all its finite images with abelian Sylow-five subgroups;
any central-seven detector must have nonabelian Sylow-five subgroups.
`wave3-audit-symplectic-root-lift` additionally excludes the rank-two
symplectic Steinberg detector construction for the commutative scalar
family, including central pushouts of its possibly noncentral kernel.
Arbitrary central extensions of the actual finite image remain untreated.

**2026-09-20 fourth campaign: stronger family restrictions, still OPEN.**
`wave4-h31-first-product-kernel-is-perfect` excludes every solvable-kernel
refinement of the canonical H31 quotient to PSL2(31) x C5.
`wave4-detector-psl19-square-kernel-mod-five-acyclicity` controls the entire
specified square kernel's first mod-five homology and excludes five-group
refinements, including for its nonzero central twists.
`wave4-visibility-dual-number-image-is-centrally-closed` excludes all
central detectors based on that actual finite matrix image.
The canonical marked presentation is now explicit, and
`wave4-canonical-centre-dies-in-class-four-quotients` puts its central
generator in gamma5. None of these families is proved to exhaust all
finite quotients, so no route to this root has been completed.

The subsequent exact finite witness
`wave4-canonical-prime-seven-class-virtually-splits` goes further in the
other direction for the chosen prime: a class-five quotient of order7^28
detects the canonical central mark, and c0 mod7 splits over a normal
subgroup of K7 of index7^27. Thus the selected mod-seven central extension
is RF exactly when K7 is; it creates no new RF failure over an RF base.
This does not decide other prime reductions or unbounded central orders.

The final integration additionally records explicit approximate-model
counterexamples to gap preservation by nearest-seventh-root rounding and
to repair by an unchanged reducing core. Liu's modified doubled-core
pruning remains available, but preserving the finite-order relations is
not established by that procedure. No new route closes this root.

**2026-09-20 fifth campaign: central powers and abelian covers.**
`wave5-canonical-central-powers-have-linear-depth` proves
z^(7^a) in gamma_(5+6a), so a nilpotent order-49 detector must reach
class at least eleven. This is a lower bound on detector complexity,
not an upper bound on all finite central orders.
`wave5-audit-k7-abelian-covers-have-only-seven-h1` proves that every
kernel of an abelian quotient of K7 has finite seven-primary
abelianization. It excludes prime-to-seven solvable refinements over
those abelian quotients. Nonabelian layers and general finite images
remain, and the root stays OPEN.

`wave5-detector-psl19-square-kernel-mod-three-acyclicity` adds full
mod-three vanishing for the specified PSL2(19)^2 kernel. With the
earlier mod-five result it excludes solvable refinements supported on
primes three and five, including for the nonzero central five-twists.
The independently checked two F8 representation sectors of the K7
class-two quotient also have zero first cohomology; this is not a
theorem about every sector or every finite cover.
