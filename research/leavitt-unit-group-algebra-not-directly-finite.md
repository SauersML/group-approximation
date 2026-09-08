---
rg: 2
id: leavitt-unit-group-algebra-not-directly-finite
kind: claim
title: The modular group algebra of the Leavitt unit group is not directly finite
root: true
distinct_from:
  binary-leavitt-algebra-not-directly-finite: that is the established defect in the Leavitt algebra, which is not a group algebra; this is the same failure demanded of F_2[R^x], which is one, and the gap between them is exactly direct-finiteness-not-inherited-by-quotients.
  kl-violating-equation-over-leavitt-unit-group: that is an equation-solving question over the same group, aimed at hyperlinearity through Kervaire--Laudenbach; this is a ring-theoretic question about its modular group algebra, aimed at Kaplansky, and neither is known to imply the other.
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that is a soficity statement about d-ary Leavitt unit and elementary groups, proved here through property (T); this is a ring identity demanded of one modular group algebra, and soficity of the group would refute it rather than supply it.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
  - research/artifacts/sl2-hnn-iwahori-dynamical-fork-2026-08-21.md
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
  - notes/KAPLANSKY_FULL_PROOF_GAP_AUDIT_2026-09-07.md
  - research/artifacts/kaplansky-two-shear-attempt-2026-09-08.md
  - research/artifacts/kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md
  - research/artifacts/kaplansky-single-macro-prefix-transporter-obstruction-2026-09-08.md
  - research/artifacts/kaplansky-bit-level-transporter-without-finite-boundary-modules-2026-09-08.md
  - research/artifacts/kaplansky-first-field-coordinate-transporter-kernel-2026-09-08.md
  - research/artifacts/kaplansky-full-two-sector-relative-transporter-obstruction-2026-09-08.md
  - research/artifacts/gottschalk-central-odd-norm-conjugacy-direct-finiteness-2026-09-08.md
  - research/artifacts/kaplansky-laurent-adjugate-and-amenable-tail-kernels-2026-09-08.md
  - research/artifacts/kaplansky-complete-exterior-injective-positive-shear-control-2026-09-08.md
  - research/artifacts/kaplansky-deletion-shear-period-two-exterior-kernel-2026-09-08.md
  - research/artifacts/gottschalk-noncentral-order-three-axis-corner-2026-09-08.md
  - research/artifacts/kaplansky-finite-drazin-seed-2026-09-08.json
---

*Marked `root` because Kaplansky's conjecture is a top-level question in its
own right, not a step toward another one. It is also reachable from the
surjunctivity root, through `stably-finite-failure-from-direct-finiteness-failure`
into `leavitt-group-algebra-not-stably-finite`; the mark is kept anyway, so
that the lane does not read as a sub-question of Gottschalk. It is not on the
way to `q3-4-resolved` and no route should be built from it toward that goal
— see the scope note below.*

Exhibit `alpha, beta` in `A = F_2[R^x]`, `R = L_(F_2)(1,2)`, with

    alpha beta = 1        and        beta alpha != 1.

This would refute **Kaplansky's Direct Finiteness Conjecture** — for every
group `G` and every field `K`, `K[G]` is directly finite — since `R^x` is a
group and `F_2` is a field.  Characteristic zero is Kaplansky's own theorem,
in the stronger stably finite form, so positive characteristic is the whole
of what is open; and the sofic case is Elek--Szabo, which is why the *nonsofic*
`R^x` of `openai-leavitt-unit-nonsofic` is the natural place to test it.

**Status: open, and the honest reading is that it is wide open.**  Every route
into it terminates at an unproved lifting statement.  The material that
exists — the surjection
`leavitt-unit-group-algebra-surjects-onto-leavitt`, its unital corner
sharpening `leavitt-corner-idempotent-unital-surjection`, and the explicit
support-three generator lifts `leavitt-rank-three-unit-lift` — establishes
that the defect lives in a *quotient*, which by
`direct-finiteness-not-inherited-by-quotients` proves nothing about `A`.
Anyone reading this lane quickly should read that node first.

## Scope: what this would and would not settle

It would refute Kaplansky's conjecture and would be a major result.  It would
**not** decide hyperlinearity of `R^x`, and so would not answer `q3-4-resolved`
either way.  The implication that connects approximation properties to direct
finiteness runs from **soficity**, over division rings, and `R^x` is announced
nonsofic; no positive-characteristic analogue for hyperlinear groups is
available here to run in either direction.  Conversely a proof that `A` *is*
directly finite would not make `R^x` sofic.  The two questions share a group
and nothing else, and this node is kept out of the goal's route structure for
that reason.

## The lanes

An exact obstruction filter is available in
`finite-precision-lifted-trace-obstruction`: polynomial idempotent lifting
modulo p^k turns a nonzero trace residue into a finite rejection certificate,
with a sufficient precision for finite-subgroup defects. The sharp cyclic
examples in `no-fixed-trace-precision-detects-all-idempotents` show why one
fixed modulus cannot replace the full invariant. Passing a finite trace
check supplies no inverse pair and leaves this target open.

The [full-proof gap audit](../notes/KAPLANSKY_FULL_PROOF_GAP_AUDIT_2026-09-07.md)
records the exact projective cancellation assertion needed for the positive
direction and proves that injectivity of lifted trace on all of K_0 is false
already for F_3[C_2]. This does not refute trace detection on nonzero actual
projectives. It supplies neither a proof of the full conjecture nor a
counterexample to it; the present negative target remains open.

The all-field positive result for the Kun--Thom wreath family now extends
to a recursive hierarchy at
`recursive-wreath-libraries-have-stably-finite-group-algebras`. It does
not settle this Q target: `map-groups-cannot-enter-the-rf-wreath-hierarchy`
shows that every homomorphism from Q into the finite hierarchy or its
residual closure is trivial, using Q's minimal almost periodicity. Those
groups cannot supply a family of homomorphisms separating elements of Q.
This rules out that specific positive transfer; it supplies no inverse
defect and leaves the present claim open.

There were four.  **Two of them died on 2026-08-17**, and both died for
structural reasons rather than for want of effort — see
`research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md`.  What is
left is the two that ask for an explicit element:

* Exhibit a single pair inside the corner — `leavitt-corner-one-sided-lift-exists`,
  and pad it back up to `A` by the route
  `leavitt-unit-algebra-not-directly-finite-by-corner-padding`.
* A left-invertible lift of `s_0`
  (`left-invertible-lift-of-s0-in-leavitt-group-algebra`), which works in the
  whole algebra and belongs to the surjunctivity lane.  It is independent of
  the corner lane — in particular
  `leavitt-rank-three-lift-inverse-support-thirteen` constrains the
  whole-algebra form and is not known to transfer into the corner.

**Dead.**

* *The full Leavitt-family lift, refuted 2026-09-07.*
  `finite-subgroup-corners-have-invariant-basis-number` excludes
  `binary-leavitt-family-lifts-into-unit-corner`: the family would force
  [eS]=2[eS], whereas the lifted trace of [eS] is 2/3. This invalidates
  `leavitt-corner-lift-from-lifted-family`, while the weaker single-pair
  corner claim remains open without a live construction.
* *The trace-balanced nested pair, refuted 2026-09-07.*
  `leavitt-balanced-corners-separated-modulo-four` excludes
  `leavitt-nested-idempotent-corner-module-equivalence` at all supports
  and after every common projective stabilization. Characteristic-two
  cocenter traces vanish, but the idempotent lifts have identity
  coefficients 2 and 0 modulo four. Thus
  `nested-idempotent-padding-refutes-direct-finiteness` has a false
  prerequisite.
* *The radical hypothesis.*  `leavitt-corner-kernel-is-jacobson-radical` is
  **false**: `ker(pi_e)` contains a nonzero idempotent of augmentation zero
  (`leavitt-corner-kernel-not-jacobson-radical`), and a Jacobson radical
  contains no nonzero idempotent.  Route
  `leavitt-unit-algebra-not-directly-finite-by-radical-kernel` invalidated.
* *The module splitting.*  `leavitt-evaluation-splits-as-module-map` is
  **false**: `A` is a prime ring
  (`leavitt-unit-group-algebra-is-prime`), and a section would make `ker(pi)`
  annihilate a nonzero ideal.  Route
  `leavitt-direct-finiteness-failure-from-module-splitting` invalidated.
  `R` is not projective over `A`.

**And one route was added, in the other direction.**  By
`leavitt-stable-finiteness-equals-direct-finiteness`, a failure of stable
finiteness at any matrix size compresses back to this scalar claim
(`leavitt-direct-finiteness-failure-from-matrix-failure`).  So this claim and
`leavitt-group-algebra-not-stably-finite` are interderivable, and Kaplansky
for `F_2[R^x]` are the same existence question. Such a witness refutes
Gottschalk for `R^x`; no converse from an arbitrary nonlinear cellular
automaton is asserted.

**Two exact reformulations now isolate the live finite-support target.**

* `padic-c0-direct-finiteness-equivalence` proves that replacing `F_2[G]` by
  `c_0(G,Z_2)` is equivalent, at scalar and every matrix size.  The completion
  supplies no escape hatch; `leavitt-padic-convolution-not-directly-finite`
  is the same open problem.
* The former explicit-idempotent shortcut through
  `leavitt-e-f-murray-von-neumann-equivalence` is refuted: the canonical
  coefficient trace takes different values on `e` and `f`, so cyclicity
  forbids `xy=e`, `yx=f`.  It is not a live reformulation of the target.

On the corner lanes, one should be precise about why the corner.  The
`F_2`-augmentation excludes a full **Leavitt family** from `A` itself and from
every corner of augmentation one, so the *family* lifting problem has nowhere
else to live.  It does **not** exclude a bare pair `alpha beta = 1 != beta
alpha` from `A`: applying `eps` gives only `eps(alpha) = eps(beta) = 1`, no
contradiction.  A direct construction of such a pair in `A`, owing nothing to
the corner, remains admissible and would be a third lane; nobody has one.

## Attempts

**2026-09-08 direct construction attempt.** A fixed evaluation-kernel
shear followed by an unknown square-zero shear reduces a literal strict
inverse pair to one linear equation. The fixed inverse corner has 220
terms; a surviving common-context certificate shows that its normalized
support generates all of Q. Strictness follows from a nonzero right
annihilator of its fixed Leavitt evaluation, without constraining the
unknown shear's evaluation. The completed 109-column parameter solve has
no solution. This finite result and the exact criterion are recorded in
the two-shear artifact; the target remains open. The initial incomplete
run was replaced by a completed solve after a prefix-reduction speed fix.

**Single prefix transporter obstruction.** The reduced finite-chart
comparison still has no split `LZ=f_0`. Every candidate `Z=P_0[g]f_0`
with one prefix permutation on the chosen `F_4` coordinates is now
excluded: two conjugate charts have a finite dihedral boundary orbit
whose exterior powers give an incompatible source and target rank.
An explicit order-six transporter passes the entire exterior-square
source test and fails in degree three. This rules out the specified
single-transporter class. The same finite orbit now excludes every
element supported in the finite chart plus one prefix double coset,
with arbitrary finite-chart coefficients. For several double cosets,
a mod-three orbit-pattern test gives a further necessary condition.
Two arbitrary double cosets passing that test, general linear units,
and prefix permutations that mix the binary coordinates encoding
`F_4` remain unresolved. The unrestricted Kaplansky target remains open.

The focused note also excludes constant-matrix corrections when an
arbitrary linear Leavitt unit moves the conjugate chart into one
outside coordinate. A finite module has source rank two, zero rank
for the original target, and rank one for the conjugate target.
The explicit two-transporter pair passing the mod-three test has
a five-vector wedge kernel. The hypothesis does not cover conjugate
charts spread across several outside coordinates.

A second explicit pair, `g_0:3<->10` and
`g_1:30<->1,31<->20`, also passes the mod-three test but has a
three-vector wedge killed by both transporters, even with arbitrary
finite-chart coefficients and an added finite-chart correction.
Section 10 of the focused note gives the common kernel directly.
This excludes that pair without proving the general two-transporter
case or providing a one-sided inverse.

The bit-level actor `1->10,20->11,21->2` on the two binary coordinates
of the first F_4 root, fixing the second F_4 root, is outside that
macro-prefix scope. The subgroup generated by its two finite charts
has no nonzero finite-dimensional submodule in any positive exterior
power of the natural binary boundary module, even after extending
scalars to F_4. This is recorded in
`bit-level-chart-pair-has-no-finite-boundary-submodules`.
The earlier finite-submodule construction therefore cannot decide
this actor. A separate direct exterior-square calculation now
excludes it and every binary-linear unit confined to the first
field coordinate: the source is nonzero while the target becomes
an alternating form evaluated on two equal vectors. This is recorded
in `first-field-coordinate-transporters-have-no-split`.

For block-diagonal actors changing both field coordinates, the same
calculation excludes every case in which either block preserves or
reverses field characters. Mixing both characters in both blocks is
still not sufficient: opposite bit compressors a,a^-1 have a two-term
binary exterior kernel. Arbitrary mixed actors and arbitrary chart
coefficients around them remain unresolved.

The complete exterior-square operator for two binary coordinate
changes is now explicit on both full source character sectors.
For c=b^-1a, a nonzero kernel in either relative character block
gives a source kernel; relative semilinearity needs cancellation
between the two source sectors. This exclusion survives any shared
left change of the two coordinate operators. It is recorded in
`relative-character-kernels-forbid-projective-splits`. Both relative
blocks being injective remains only necessary. A subsequent positive
shear pair now passes the entire natural exterior-square source,
as described below.

A separate exact bridge transports any linear inverse pair to a
Boolean quadratic pair on an enlarged group. The central odd-cycle
norm rules F_B are reversibly conjugate to the original linear rule
plus unchanged coordinates, and satisfy F_B F_C=F_(BC). Finite
S_3 blocks include matrix coefficients. This does not construct a
group-ring pair for Q; it shows that the corresponding quadratic
norm family retains the characteristic-two direct-finiteness question
exactly, including any failed reverse identity.

For each fixed Gamma, the full family x+A Q_t on Gamma x C_3 with
arbitrary scalar linear A is surjunctive exactly when F_2[Gamma] is
directly finite. The converse to the norm reduction uses a local
involution and two-block elimination; stable direct finiteness is
not assumed. This is an equivalence, with neither a direct-finiteness
proof for arbitrary Gamma nor a counterexample supplied.

The complete exterior test now separates three cases. Laurent
coefficient actors always have an explicit adjugate tensor kernel;
amenable coefficient groups have a finite-support rank deficit,
without requiring an invariant finite-dimensional tail space.
These results are recorded in
`amenable-coefficient-transporters-have-exterior-kernels`.

The positive shears a=[[1,s_0],[0,1]], b=[[1,s_1],[0,1]] pass the
entire natural exterior test. A finite-prefix-support proof rules
out every tensor kernel in both source sectors. Their group-ring
split is nevertheless impossible: the free positive coefficient
algebra has an augmentation giving a finite representation with
f_0 nonzero and P_0 zero. This paired control is recorded in
`positive-shear-passes-exterior-test-without-projective-split`.

Adding deletion coefficients in the pair a=[[1,s_0],[t_0,0]],
b=[[1,s_1],[t_1,0]] removes that creator-to-zero specialization.
The pair still fails: the two periodic tails (01)^infinity and
(10)^infinity supply a four-term binary exterior kernel, recorded
in `deletion-shear-pair-has-period-two-exterior-kernel`. Its explicit
algebraic proof closes this actor; no full group-ring split has
been obtained.

The quadratic bridge also extends to order-three feedback preserving
the invariant triple subspace, with an exact criterion in eF_2[G]e.
For a normal subgroup of order three this covers arbitrary linear
feedback and identifies the corner with the quotient group algebra.
The nonnormal unrestricted case still lacks a justified treatment
of the linear axis outside that subspace.

**Every lane runs out at the same place, and it is worth seeing that they run
out for different reasons.**

* *Compress the explicit lifts into the corner.*  The inequality comes free
  and the whole problem reduces to one equation `ab = e`, whose defect lies in
  `ker(pi_e)` — see the attempts under `leavitt-corner-one-sided-lift-exists`.
  Dies on having no handle on that kernel.
* *Lift the whole Leavitt family.* Refuted in the designated corner by
  the lifted 2-adic trace: the family would force [eS]=2[eS], while
  its trace is 2/3. Vanishing ordinary augmentation does not remove
  this obstruction. The weaker single-pair lifting problem remains open.
* *Use the radical.*  **Refuted 2026-08-17.**  `ker(pi_e) = J(eAe)` would have
  made the quotient argument legal without exhibiting anything.  It is false:
  the kernel contains a nonzero idempotent.  What is worth keeping from this
  lane is the diagnosis it produced — the question was gated on whether
  `ker(pi_e)` was zero, and that was the right gate.
* *Work in the whole algebra.*  The surjunctivity lane's
  `left-invertible-lift-of-s0-in-leavitt-group-algebra` faces the identical
  correction problem with `ker(pi)` in place of `ker(pi_e)`, and its first
  necessary condition already kills the obvious candidate: a left-invertible
  lift needs `eps(a) = 1`, while the natural four-unit lift has `eps = 0`.

**What has actually been ruled out, as opposed to merely not found.**
*(Rewritten 2026-08-18 — the support floor has been superseded by a complete
no-go.)*  The explicit support-three lifts of `t_0` and of `s_0` have **no
one-sided inverse in `A` at any support whatsoever**, and the corner
compression `e t~ e` has none in `eAe`
(`leavitt-rank-three-lift-has-no-one-sided-inverse`).  The mechanism is
location rather than size: the supports of `t~`, of `s~` and of `e` all lie
inside subgroups isomorphic to `(C_2 x C_2) * C_3`
(`leavitt-rank-three-support-group-is-virtually-free` — the corner's
order-three unit `g` is exactly `u_3`), whose group algebras are directly
finite, and by `subgroup-supported-one-sided-inverse-rigidity` a partner drawn
from anywhere in `A` collapses back into that subgroup.  So every explicit
candidate this lane had built is dead, and the earlier floor
(`leavitt-rank-three-lift-inverse-support-thirteen`, support at least
thirteen, and odd) is now vacuously true.

**The contrapositive is the usable output, and it is sharper than the floor.**
Any surviving witness must have support generating a subgroup with no known
direct finiteness — in particular a **nonsofic** one.  That is exactly why
`openai-leavitt-unit-nonsofic` made `R^x` the right group to test, and it says
the search had accidentally been running inside a virtually free part of it
where a counterexample provably cannot live.  Enumerating candidates by
support size is the wrong measurement; the subgroup generated by the support
is the right one.  Since 2026-08-17 there are two structural exclusions as well,
but note what they exclude: they kill two *ways of arguing*, not any candidate
pair.  Nothing yet excludes a pair.

**The cheapest new information has now been produced, and it did not help.**
This section used to name `ker(pi_e) = 0?` as the cheapest thing anyone could
find out.  The answer is no — `leavitt-corner-kernel-not-jacobson-radical`
exhibits a twelve-term idempotent in it, and
`leavitt-recursive-kernel-idempotents` an infinite orthogonal family.  The
lesson for the surviving lanes is negative and specific: the correction ideal
in `(a + alpha)(b + beta) = e` is large and idempotent-rich rather than
radical noise, so corrections should be sought with Peirce and corner
structure, not with nilpotent perturbation.  The one recursive correction that
the new structure makes natural has been tried and fails — the telescoping
tail `lambda^m(error)` is nonzero at every finite depth, and group-algebra
elements have finite support.

**The first genuinely nonlinear packet correction is now sharply fenced.**
For `A=e t~e`, `B=e s~e`, and the conjugated constant packet `P_x`, the live
equation is

```text
A P_y + P_x B + P_x P_y = Delta.
```

`two-packet-linear-trace-vanishes` proves globally that the identity
coefficient of each linear term is zero.  Since `tau(Delta)=1`, every solution
must have odd packet-support intersection
(`two-packet-solutions-have-odd-intersection`), and `x=y` is impossible.
The exact independent-conjugator exhaustion
`mixed-root-two-packet-radius-four-has-no-solution` checks all 1,572,516
ordered pairs of genuinely mixed eight-root elements through word length four:
only 1,394 survive the trace filter and none solves the equation.  This is a
bounded family result, not a global no-go.

The current target is therefore precise: solve the two-packet equation
subject to odd intersection, or construct a one-sided inverse pair by a different finite-support
mechanism.  The tempting `e~f` branch is impossible and must not be reused.

The newer pair of `leavitt-trace-balanced-nested-idempotents` also fails,
by `leavitt-balanced-corners-separated-modulo-four`. Its construction
and characteristic-two trace calculations are correct, but the lifted
2-adic traces are 2/3 and 4/9. The difference 2/9 detects a nonzero
K_0 class, so neither arbitrary cross-atlas intertwiners nor stabilization
can identify the modules.

More generally, `lifted-trace-detects-finite-subgroup-projectives` shows
that a hypothetical nonzero inverse defect cannot be supported in any
finite subgroup, or be a nonzero finite sum of induced finite-subgroup
projectives. A computational construction using a finite-state boundary
idempotent must check this restriction even when its transition operators
generate the whole ambient group.

`nested-two-finite-subgroup-idempotents-have-strict-rank` also excludes
using two separate finite support packets as source and reverse-product
idempotents, even when their combined subgroup is infinite. For the
designated finite-supported corner identity e, a strict reverse product
must itself have support generating an infinite subgroup.

`finite-subgroup-copy-circuits-have-no-recurrent-branching` extends that
constraint to a finite network of different projective packets: exact
decomposition into successor states permits only simple cycles in the
recurrent part. This excludes branching copy circuits of finite-subgroup
projectives, not arbitrary cyclic verification or nonlinear computation.

There is also an exact bound for recursion with a fixed identity:
`lifted-trace-bounds-unital-matrix-parts` shows that the cubic corner
can contain a unital binary matrix block of size two but not four.
The existing arbitrarily large matrix embeddings use changing identities;
they do not supply unbounded coherent matrix capacity at the fixed e.

## Cross-atlas affine update (2026-09-07)

An additional computational translation is now available, with a change
of group made explicit. In
`certificate-linear-counterexamples-compile-to-lamp-algebras`, an
injective nonsurjective full-shift rule with certificate-controlled linear
data compiles into a prime-field matrix inverse pair on a finite-abelian
regular wreath product over the source group. This permits arbitrary
finite certificate predicates and data mixing; compactness constructs a
local linear decoder, and Fourier lamp idempotents encode the predicates.
It is a possible route to the headline conjectures on an enlarged group,
not a solution of this fixed-Q claim. No source counterexample has yet
been constructed.

`binary-leavitt-unit-group-four-generated` replaces the twelve individual
atlas transvections by four explicit units generating the full group.  After
forcing these four terms, `leavitt-cross-atlas-eleven-term-s0-lift` constructs
an exact eleven-term lift of `s_0`; its seven correction terms are minimum in
the anchored radius-three universe.  Unlike the support-three lift, its
support is not trapped in a directly finite virtually free subgroup: it
generates all of `Q`.

The accompanying joint solver fixes an affine lift `B` of `t_0` and imposes
both `BA=1` in the literal group algebra and `evaluation(A)=s_0` in one exact
linear system.  A hit would be automatically strict after reversal, by
`leavitt-direct-finiteness-failure-from-left-invertible-lift`.  What the
searches found is recorded, negatively, in
`eleven-term-s0-lift-has-no-radius-four-left-inverse`: no partner in the
radius-four ball for the eleven-term `A`, none for the displayed five-term
mixed-chart `B`, and none in the radius-three ball for the superseded
25-term lift.  **These are bounded fences, not a solution and not an
obstruction** — and unlike `leavitt-rank-three-lift-has-no-one-sided-inverse`
they cannot be upgraded, precisely because the support now generates all of
`Q` and `subgroup-supported-one-sided-inverse-rigidity` has nothing to bite
on.  Losing the unbounded no-go is the price of escaping it.

`recursive-quine-route-to-kaplansky-is-closed` retires two classes of attack
at once: a candidate supported in the LEF two-compressor core or in the
locally finite recursive packet tower is dead at any support, and a
reverse-Kleene compiler for direct finiteness exists exactly when a
counterexample does, so the fixed point cannot manufacture one.  Self-reference
is a scheduler here, not an algebraic amplifier.

**Do not search these again.**  The support-three lift and its corner
compression (virtually free support), the locally finite recursive packets,
symmetric compressor sums, both proposed `e ~ f` Murray--von Neumann pairs,
and blind growth of the partner universe by word radius have all failed
structurally rather than for want of compute. The modulo-four obstruction
adds the trace-balanced nested pair to this list. The next exact gate should vary both affine
factors while keeping a literal cross-atlas relation, certify the support
subgroup of the `t_0` lift to be `Q` rather than merely mixed-chart, grow the
`A`-support universe by multiplication-collision class instead of word radius,
and carry blocking clauses learned from the failed Gaussian systems.

The computational lane now has a stronger exact reduction:
`one-invertible-certificate-fiber-forces-global-invertibility` proves that
any strict certificate-controlled linear full-shift embedding yields a
strict matrix inverse pair over the original group algebra by freezing
any constant certificate. No finite-lamp enlargement is needed. This
does not exhibit the pair for Q; it shows that any successful local
verification program in this class must already retain the algebraic
defect in every constant specialization.

`rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` supplies a
separate positive permanence theorem. For residually finite lamps and
arbitrary permutation actions, stable finiteness of the wreath group
algebra is equivalent to stable finiteness of the base group algebra.
Building such a wreath library cannot create failure of stable finiteness
over a stably finite base. The earlier finite-stabilizer theorem retains
the stronger equivalence at each fixed matrix size; the arbitrary-action
extension does not assert that extra conclusion.

The library barrier now has two further extensions.
`lef-group-rings-over-stably-finite-rings-are-stably-finite` replaces
RF lamps by LEF lamps in the untwisted theorem: the finite support table
of a putative defect transfers exactly into a finite group algebra.
`residual-lamp-quotients-handle-monomial-actions` permits internal
automorphism updates when invariant finite lamp quotients separate the
lamp group, in particular for every finitely generated RF lamp. These
are positive permanence results, not an inverse pair for Q. A program
that escapes them needs an operation outside their precise construction
classes; self-reference alone supplies no such operation.

## Exact cancellation circuits beyond bounded support search

`cyclotomic-liftable-cancellation-pairs-have-no-inverse-defect` gives
a finite lattice filter for a proposed F_2 inverse rectangle. If its
equal-product cell pairing has no odd integral dependence among row
and column difference vectors, roots of unity lift the entire forward
identity to characteristic zero and force the reverse identity as well.
An odd dependence merely modulo two is insufficient; the attached
C_4 example needs eighth roots even though real signs fail.

The stronger `central-sign-survival-forces-reverse-cancellation` permits
noncommuting coefficient lifts. Introduce a central involution J and
require each paired product to differ by J in the coefficient group.
If J survives, a characteristic-zero corner again reverses the lifted
identity and reduction gives AB=1. A strict template therefore needs
J to collapse, equivalently an odd closed identity among its normalized
matching relators. In particular an aspherical matching presentation
is excluded. A D_8 coefficient example demonstrates that this test
extends strictly beyond all scalar phase assignments.

These are unrestricted-support necessary conditions for construction,
not a new inverse pair in Q. Surviving the tests still requires proving
a literal nonzero reverse defect in the ordinary group algebra.

The [half-corner construction](artifacts/kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md)
now supplies a different explicit comparison. A six-dimensional
representation excludes every primitive split in the original S_3 block.
A stable-image split instead solves the first shear equation exactly:
its corner element satisfies T^4=T^2, with h=T^2 and Drazin inverse T^3.
After conjugating the source, the remaining projectors f_+ and P have
supports 30 and 70 in one group of order 180, both regular rank 40 and
lifted trace 2/9. Their natural evaluations differ, so an explicit split
embedding f_+S into PS would have a nonzero reverse defect. The
[exact finite certificate](artifacts/kaplansky-finite-drazin-seed-2026-09-08.json)
constructs the projectors and checks their identities; it does not
construct that embedding. This headline target remains open.
