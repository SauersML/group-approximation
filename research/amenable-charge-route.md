---
rg: 2
id: amenable-charge-route
kind: route
title: Build a charge, not a carrier — Kahl–Schneider applied to the wreath candidate
target: hyperlinear-wreath-model
requires: [hyperlinear-near-representation-criterion, wreath-amenable-near-representation]
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Build a charge, not a carrier

Kahl–Schneider's criterion is an equivalence, so applying it is a one-line
reduction: an essentially free amenable near representation of `W`
(`wreath-amenable-near-representation`) is hyperlinearity of `W`. The route
exists because of what it changes about the work, not because of what it
proves.

Every architecture invalidated on this claim — nine of them now — constructs a
finite carrier and dies because the coordinate action cannot be modelled by
permutations. `notes/FALSE_HALO_ACTION_AUDIT.md` explains why that is not
accidental: a finite carrier labelled by anything locally sofic collapses, since
finitely generated subgroups of `U(n)` are linear, hence residually finite,
hence sofic, so the witness class reduces to the sofic one and the argument
becomes circular. The Kahl–Schneider witness is a finitely additive probability
charge on an orthonormal basis. It is not a finite carrier, it is not produced
by exhibiting one, and the collapse argument has nothing to grip.

This is the same non-Cartan requirement the rest of the subtree has converged
on, restated in the only language where the object is soft: the basis is the
coordinate system, and the criterion never asks the group to preserve it —
only to preserve the induced state on `B(H)`.

## Status after the 2026-08-14 pass: both risks below are now resolved, negatively

The two "honest risks" recorded at the end of this route have both been
settled, and the route survives in a narrower and more honest form.

*Bekka.* Not a conjecture any more — proved as
`amenable-rep-of-kazhdan-has-fd-subrep`, since the primary source stayed behind
an auth wall and deriving it was cheaper than obtaining it. An amenable
representation of a Kazhdan group has a nonzero finite-dimensional
subrepresentation, so a *genuine* essentially free amenable representation of
`W` is refuted by the existing finite-dimensional rigidity
(`commutant_no_growth`, and `finrank` as an invariant size). Published form and
converse direction: `bekka-valette-amenable-t-dichotomy`.

**Retraction (2026-08-14).** This paragraph originally continued: "The lane is
therefore not independent of `rigidity-route`; it is independent exactly to the
extent that flexibility is." That was wrong and the lane is in fact
independent. The inference assumed flexible HS-stability could convert an
amenable *near* representation into an amenable *genuine* one. It cannot:
amenability is an invariant state on `B(H)`, states are operator-norm
continuous, and flexible HS-stability gives only `‖·‖₂` closeness, so the
invariance does not transfer. Amenability lives at the operator-norm scale and
near-ness at the trace scale, and no repair bridges them. The pivot question is
now carried explicitly as `near-representation-amenability-dichotomy`.

*Difficulty conservation.* The concrete first attempt below is dead:
`induced-charge-extension` is invalidated by `no-invariant-mean-on-coset-space`.
Inducing the positive core's charge produces a `G`-invariant mean on `G/Γ`, and
property (T) with infinite index forbids one. The Hahn–Banach-versus-open-problem
asymmetry that motivated this route does not exist — Hahn–Banach extends a
charge to more sets under the *same* group, not along a group inclusion — and on
that comparison the charge side is strictly worse off, its obstruction being a
theorem while Gao–Junge Problem 1 is merely open.

What remains is the non-induced constructions. The route stays open, the
criterion is still a genuine equivalence, and the witness is still not a finite
carrier — but it is no longer a shortcut, and the concrete first attempt is
gone.

On independence from the other two live routes: after the retraction above,
this lane is *not* known to share their failure mode. `growing-fiber-models`
and `positive-core-dilation-splice` both work at the trace scale, where the
Kun–Thom obstruction and the rigidity results live. This one asks for an
invariant state on `B(H)`, an operator-norm-scale object, and that is precisely
why the collapse does not reach it. Whether the separation is real or an
artefact of what is currently provable is exactly
`near-representation-amenability-dichotomy`.

## What to try first (superseded — see above)

`positive-core-bernoulli-ce` gives an honest sofic action `Γ ↷ X₀` on the
positive orbit, hence — by Elek–Szabó's set-level criterion, the exact analogue
Kahl–Schneider generalize — an essentially free amenable almost-action of `Γ`
with an invariant finitely additive measure. The question is whether that
charge extends over the compressors `L₊`. That is the charge-level twin of
`simultaneous-dilation-splice`, and the two may well not have the same
difficulty: extending a finitely additive invariant measure is Hahn–Banach's
home ground, whereas extending Connes embeddability across an amalgamated free
product over a nonamenable base is a named open problem (Gao–Junge). If the
charge extends where the algebra does not, that asymmetry is the whole
programme.

## Honest risks

Two, and neither is small.

The criterion is an equivalence, so it cannot make the problem easier by
itself; all it can do is move the difficulty somewhere the available tools are
different. If the difficulty is conserved — which is the default outcome and
what the halo audit found for the previous reformulation — this buys nothing.

And there is a specific way the lane could collapse into the rigidity branch:
if Bekka's theorem says that an amenable representation of a property (T) group
must contain a finite-dimensional subrepresentation, then a genuine such
representation of `W` would be attacked by `finite-quotient-blindness`, and the
entire content would sit in the gap between "near" and "genuine" — i.e. in
flexible stability. I could not read Bekka's statement (Springer auth wall, two
secondary sources silent), so this is flagged in
`wreath-amenable-near-representation` as a conjecture about the literature and
is not used. Reading that one sentence is the cheapest way to find out whether
this route is independent of `rigidity-route` or secretly identical to it, and
it should be done before any charge is constructed.
