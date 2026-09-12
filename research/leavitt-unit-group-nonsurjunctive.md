---
rg: 2
id: leavitt-unit-group-nonsurjunctive
kind: claim
title: The binary Leavitt unit group is not surjunctive
root: true
distinct_from:
  openai-leavitt-unit-nonsofic: that is the nonsoficity of the same group; nonsurjunctivity implies nonsoficity, but nonsoficity supplies no converse implication
  leavitt-unit-group-algebra-not-directly-finite: that is the Kaplansky question for the same group's modular group algebra, a statement about elements of a ring; this is a statement about cellular automata on a full shift, and while the first implies the second the converse is not available
  kl-violating-equation-over-leavitt-unit-group: that asks for a Kervaire--Laudenbach violation over the same group, which would refute its hyperlinearity; this asks for an injective non-surjective cellular automaton, which would refute Gottschalk's conjecture
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
  - research/artifacts/conservative-syndrome-update-audit-2026-09-07.md
  - research/artifacts/conservative-ca-literature-and-trace-scope-2026-09-07.md
  - research/artifacts/kaplansky-two-shear-attempt-2026-09-08.md
  - research/artifacts/gottschalk-four-track-finite-chart-collision-2026-09-08.md
  - research/artifacts/forward-memory-cover-and-native-prefix-test-2026-09-08.md
  - research/artifacts/gottschalk-information-transport-pinning-control-2026-09-08.md
  - research/artifacts/gottschalk-consecutive-chart-dual-boundary-collision-2026-09-08.md
  - research/artifacts/gottschalk-parallel-order-three-five-point-collision-2026-09-08.md
  - research/artifacts/gottschalk-quadratic-block-elimination-2026-09-08.md
  - research/artifacts/gottschalk-parallel-c3-incidence-collision-criterion-2026-09-08.md
---

Exhibit a finite alphabet `A` and a cellular automaton
`tau : A^G -> A^G` over `G = L_(F_2)(1,2)^x`, the binary Leavitt unit group,
that is **injective and not surjective**.

Since Gottschalk's conjecture asserts that every group is surjunctive, such a
`tau` would refute it.

*Marked `root` because it heads a lane of its own, exactly as
`leavitt-unit-group-algebra-not-directly-finite` does: it is a top-level
external question, not a step toward `q3-4-resolved`, and no route should be
built from it toward that goal. It records the repository's Leavitt-group
candidate so the graph says where that construction does and does not reach.*

## Why this group and not another

Sofic groups are surjunctive (Gromov--Weiss), so any counterexample must be
nonsofic. The repository's proposed nonsoficity route for G is
`openai-leavitt-unit-nonsofic`. That is the **whole** of the connection.
Non-surjunctivity implies nonsoficity; the converse is not established. Every
statement in the routes below is unconditional — none uses the announcement,
and all would read the same if `G` turned out to be sofic.

## Relation to the Kaplansky lane

This claim sits strictly downstream of
`leavitt-unit-group-algebra-not-directly-finite`: a one-sided inverse in
`F_2[G]` yields the automaton
(`stable-finiteness-failure-refutes-surjunctivity`), so everything in that
lane — the corner construction, the lifting problems, the support-thirteen
floor — is evidence about this question too.  Nothing runs back the other way.

## The one honest warning

The repository supplies a strict self-embedding of a **proper** invariant
subshift (`leavitt-kernel-annihilator-strict-self-embedding`).  That is not a
step toward this claim: the same construction runs over a finitely generated
free group, which is surjunctive
(`subshift-self-embedding-carries-no-surjunctivity-content`).  It is the
dynamical twin of `direct-finiteness-not-inherited-by-quotients`, and both
kill the same shortcut.

## Attempts: a computer that preserves its malformed certificates

The forward-cover theorem
`forward-memory-lifts-exclude-strict-cellular-sections` strengthens the
memory test: for a genuine surjunctive cover, matching the decoder-after-
encoder table alone excludes strictness. Reverse-table collisions cannot
rescue it. A forward prefix chain can force the native twelve-letter
Leavitt relation into the table presentation, but its six positive-root
letters alone generate a finite subgroup. A viable rule must both read
an infinite actor and use forward identifications that escape every
surjunctive marked cover; neither condition supplies its local inverse.

The direct nonlinear seed check of 2026-09-08 excludes two proposed
memory pairs for every finite alphabet. Their two composition product
tables agree respectively with tables in A8*A8 and (A8*A8)*V4, so the
same local rules and reverse defect would transfer to a surjunctive
virtually free group. This remains true for the second seed despite its
displayed mixed identity AB=C: the table does not authenticate the
internal commutator words defining those addresses. No truth-table search
was run on either excluded window. The attached two-shear artifact gives
the precise memories and links the exact product-partition records.

The user's proposed totalization uses certificate and syndrome tracks to
avoid losing malformed computational histories. A precise subclass is
now excluded by `certificate-controlled-routing-is-surjunctive`: keep the
certificate, and locally route each output datum from one input datum.
This class is surjunctive over every group, including with multiple data
tracks and finitely many intervening reversible computation stages.

The reason is exact Bernoulli balance of incoming and outgoing reads.
Duplicating an input on a valid certificate forces an unread input on
another certificate, which destroys full-shift injectivity. The excluded
class includes arbitrary complexity of the local routing decision; a
self-aware program does not change this balance.

A further computational construction must therefore explain a mechanism
outside this finite factorization, such as a rule combining several input
values whose global injectivity is not inherited stage by stage. This is
a remaining design requirement, not a constructed counterexample or a
proof that every computational route is impossible.

There is now a precise translation for one larger construction class.
`certificate-linear-counterexamples-compile-to-lamp-algebras` allows
arbitrary local certificate predicates to choose linear combinations of
data. If such a rule is injective and nonsurjective on the full shift,
`certificate-linear-automata-have-local-linear-decoders` supplies a local
linear decoder. The strengthened constant-fiber theorem turns the pair
into `B A=I`, `A B!=I` over the prime-field group algebra of G itself,
at the original data matrix size: freeze any constant certificate and
evaluate all coefficients there. A Fourier realization in a larger lamp
group remains available, but is no longer needed to retain the defect.

The remaining construction problem is to specify the coefficient predicates
and prove injectivity for every malformed certificate while retaining one
nonsurjective fiber. The translation lets that problem be designed as a
computer with conditional linear updates and then encoded algebraically.
No such update rule is currently exhibited. Moreover,
`one-invertible-certificate-fiber-forces-global-invertibility` shows
that its defect would have to occur at every certificate, including
each constant one. Finite changes to any certificate perturb the linear
operator by finite rank; an invertible fiber would therefore force
invertibility on a dense set and then on the whole family. Complicated
certificate logic cannot confine a strict defect to selected computations.

`finite-pattern-orbit-closure-forces-surjunctivity` supplies a separate
test for genuinely nonlinear rules. If the encoder and a decoder preserve
the span of constants and finitely many rational pattern-monomial orbits
containing all one-site observables, the encoder must be surjective over
every group. Those nonconstant pattern orbits are projective modules over
Q[G], where stable finiteness is known in characteristic zero.

A proposed finite verification loop must therefore distinguish a finite
description from finite closure of its pattern observables: they are not
the same condition. A counterexample necessarily has unbounded orbit
growth under this closure process, but an explicit reversible two-track
rule already has such growth, so growth by itself proves nothing. The
remaining task is still to construct a strict full-shift embedding and
prove injectivity on every configuration.

The direct finite-difference extension of the certificate-linear route
also fails: `boolean-secants-do-not-supply-operator-left-inverses` gives
a reversible three-bit gate whose canonical telescoping secant is
singular. Encoder-decoder inversion recovers the actual difference of
two inputs, but it does not provide a matrix inverse on arbitrary data
with those inputs held as certificates. Ordinary formal derivatives
do not fix the gap, since they do not descend to the Boolean function
algebra. These are restrictions on those specific linearization methods,
not a proof against all nonlinear computation routes.

The locality issue has a positive stabilized answer in
`injective-automata-have-local-stable-secant-dilations`: two local
additive shears and a track swap give an explicit reversible operator
carrying each genuine input difference to its output difference. This
implements the proposed preservation of an error syndrome. The remaining
condition is precise: the syndrome must vanish on every arbitrary data
vector with the certificate fixed, not just on the certified execution
difference. That condition is QP=I. Without it the ambient construction
is reversible and has no missing configuration; with it a strict
zero-auxiliary restriction requires the further reverse defect PQ!=I.
No such pair is currently produced.

`output-secants-with-local-sections-force-matrix-defects` now removes one
of those two remaining conditions. Certify arbitrary decoder inputs a,b,
rather than only encoder images. For any missing output b, take
a=tau sigma(b). Their decoder values agree, so the decoder secant kills
the nonzero vector b-a. A local right inverse of that secant family would
therefore automatically have a strict reverse defect. The right inverse
may be designed as a nonlinear local program: once it is valid on all
data and all certificates, single-coordinate responses linearize it
without increasing its memory. Constructing that right inverse is still
open; the encoder tau itself does not automatically provide it.

The same fiber theorem forces any successful output-secant construction
to retain its one-sided defect even at a constant diagonal certificate.
Setting Q_(a,a)=I at one certificate is incompatible with a locally split
family and a nonlinear collision. The actual original-group inverse pair
must therefore already appear in that constant specialization.

Replacing the certificate index set G by cosets or other replicated
positions does not remove the algebraic restriction:
`rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` proves that
C_lc(B^X,k) semidirect G is stably finite exactly when k[G] is, for any
G-set X and finite nonempty B. This covers independently chosen symbols
on a permutation G-set, even with infinite stabilizers. It does not
cover arbitrary constrained subshifts or data-dependent updates to the
certificate. The full-shift construction problem remains open.

The strongest current certificate reduction no longer assumes linearity.
`nonlinear-certificate-fibers-are-all-surjective-or-all-strict` proves
that any injective full-shift automaton E(x,c)=(T_c(x),c) has either
all bijective data fibers or all strict data fibers. In the strict case,
EVERY constant certificate gives an ordinary injective nonsurjective
CA on the original data alphabet over the original group. The proof
counts the finitely many completions of a fixed outside output pattern,
then uses locality and compactness to pass from finite certificate
changes to arbitrary certificates. No linearization is used.

Thus preserving arbitrary malformed certificates cannot conceal the
entire defect in the valid computational sector, even for nonlinear
programs. Evolving the certificate by an autonomous reversible CA has
the same obstruction. A design that uses data-dependent certificate
updates lies outside this theorem; no such counterexample is currently
constructed. This reduction supplies neither a strict CA on Q nor a
general surjunctivity proof.

The conservative-syndrome strategy now has a complete positive result.
`finite-injective-conservative-binary-automata-are-surjective` proves
that exact particle conservation and injectivity on finite configurations
force surjectivity over EVERY group. It attains every particle sector,
closing the higher-particle gap recorded in the earlier attached audit.
The proof uses bounded cluster matchings, an ordered-particle lift, and
the partition-polynomial trace of
`finite-collision-operator-algebras-are-stably-finite`. Conservation
of one-site expectation alone is not used as a surjectivity argument.

The stronger result
`finite-injective-charge-noncreation-forces-surjectivity` permits any
finite alphabet with one quiescent state and strictly positive real
charges on all other states. Merely requiring charge not to increase
on finite configurations already forces conservation and surjectivity.
Lower charge sectors are filled first; an actual charge drop would then
contradict injectivity. A colored collision corner fills each new level.

Thus a strict self-verifying encoder cannot be implemented entirely
by conserving or destroying a positive amount of material. With a
quiescent state, it must increase each chosen positive charge somewhere
on finite input. This requirement does not itself yield a strict CA:
reversible rules can also grow finite particle supports. Unrestricted
data-dependent computation and arbitrary full-shift injective rules
remain outside the proved positive class. This root remains open.

The explicit four-track parallel rule built from the two atlas chart
pairs is now proved noninjective: the indicator of the first finite
GL_4(F_2) subgroup, placed on every track, maps to zero. An exact
chart-separation calculation proves the second bilinear summand
vanishes on that mask; see
[the finite-chart collision artifact](artifacts/gottschalk-four-track-finite-chart-collision-2026-09-08.md).
This excludes that concrete encoder, including every cyclic track
count using its same bilinear operation. It does not decide this
headline target or unrestricted nonlinear feedback architectures.

The positive information-transport attack also has an explicit limitation:
its exact row-accounting identity fails for a reversible degree-64 parity
shear with fully iid source and output pins. Conditional entropy has an
atomic jump for an interval of source-pin densities, and finite-exhaustion
reveal accounting misses that contribution. A second local recoding,
with an immediate decoder, strictly increases percolative entropy. These
controls rule out vanishing singular mass and general entropy invariance;
they supply neither a nonsurjunctive automaton nor the still-needed lower
bound comparing singular row and column contributions.

The consecutive-chart alternating encoder is also noninjective: coefficient
parity in the contragredient boundary representation supplies a common mask
and a literal collision. Both proposed constant-control left ideals are
proper. Parallel order-three scalar gates have separate finite collisions,
including the first cubic conflict correction and the nonconservative
orbit-complement gate. These are exact rejections of specified constructions.
The positive quadratic artifact additionally rules out all nearest-two
cyclic bilinear feedback and all scalar two-term selectors as possible
strict encoders over any group. The headline construction remains open.

**Evasion map (2026-09-12).** Three established claims narrow where a
counterexample can live:
- `gottschalk-counterexamples-lie-outside-the-permanence-closure`: this group lies
  outside the closure of the sofic groups under every surjunctivity permanence
  theorem now available, so no positive method rules it out.
- `strict-pairs-transfer-to-table-realizations`: a certificate's product tables
  must fold its orphan cells under every homomorphism into a finite or already
  surjunctive group. Candidate windows can be screened on unit products before
  any rule is tried.
- `full-shift-maps-into-two-sided-algebraic-subshifts-are-constant`: the Leavitt
  kernel subshift receives only the zero automaton from full shifts. So no
  construction can pass through the dual of the Leavitt algebra.
