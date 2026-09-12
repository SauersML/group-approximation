---
rg: 2
id: wreath-amenable-near-representation
kind: claim
title: The wreath candidate admits an essentially free amenable near representation
distinct_from:
  hyperlinear-near-representation-criterion: that is the general external equivalence, established by citation; this is its instance at one candidate group, and is open
  fiber-masa-free-cocycle: that asks for finite matrices with a structural property; this asks for a finitely additive invariant charge, and no finite carrier appears in it
  hyperlinear-wreath-model: that is the goal; this is a criterion-specific reformulation of it that changes what object has to be built
  wreath-not-sofic: that is the established NONSOFICITY of the candidate, an obstruction imported by citation; this is a construction target for its HYPERLINEARITY — opposite directions on the same group, and the pair of them is exactly what would answer Q3.4
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Construct an essentially free amenable near representation of
`W = (⊕_{G/Γ} ℤ/2ℤ) ⋊ G` on a Hilbert space, in the sense of Kahl–Schneider.
By `hyperlinear-near-representation-criterion` this is equivalent to `W` being
hyperlinear, so it is a reformulation of `hyperlinear-wreath-model` rather than
a strengthening — but it reformulates the *object to be built*, which is the
point.

## RESTATEMENT AUDIT (2026-08-14)

Re-derived after the team-wide "restatement dressed as reduction" warning.
This claim is equivalent to the target modulo one established claim, and the
node already said so in passing — "a reformulation of `hyperlinear-wreath-model`
rather than a strengthening" — without drawing the consequence.

`hyperlinear-near-representation-criterion` is established and is an **iff**:
a group is hyperlinear exactly when it admits an essentially free amenable near
representation. So "W admits one" is "W is hyperlinear" is
`hyperlinear-wreath-model`, and `amenable-charge-route` is a translation, not a
reduction.

The translation is worth having — the witness type changes from a finite
carrier to a finitely additive charge, the toolbox changes from finite
construction to Hahn–Banach and compactness, and the scale changes from trace
to operator norm, which is exactly why this lane does not inherit the rigidity
collapse. But a translation with an open hole looks like a second front and is
not one. All three live routes into `hyperlinear-wreath-model` fail this audit;
see `simultaneous-dilation-splice` and `fiber-masa-free-cocycle`.

## The exact parallel, and where it breaks

The two criteria are the same statement in two categories, and both halves are
source-verified.

Elek–Szabó (arXiv:math/0408400, *Math. Ann.* 332 (2005)) define, verbatim:

> An amenable action of a group Γ on a set X is called *essentially free* if
> there exists a Γ-invariant finitely additive measure μ on X such that for any
> 1≠g∈Γ, μ(Fix(g))=0, where Fix(g)⊆X denotes the fixed point set of g.

and prove, verbatim, that *"a group has an essentially free amenable
almost-action if and only if it is sofic"*. Kahl–Schneider (arXiv:2504.10988,
revised 2026-01-05) prove the Hilbert-space analogue, verbatim: *"a group is
hyperlinear if and only if it admits an essentially free amenable near
representation"*, with amenability in Bekka's sense, characterized by an
orthonormal basis supporting an invariant probability charge.

So soficity asks for a charge on a **set** that the group almost-permutes, and
hyperlinearity asks for a charge on an **orthonormal basis** that the group
merely has to preserve *as a state on `B(H)`* — the basis itself need not be
carried to itself. Kun–Thom Theorem A says the first object does not exist for
`W`. Whether the second does is open, and the gap between them is once again
the non-Cartan gap: the basis is the coordinate system, and the criterion does
not require it to be equivariant.

## Why this is worth a separate node rather than a rephrasing

Because the witness is soft. Every architecture invalidated on
`hyperlinear-wreath-model` builds a finite carrier, and
`notes/FALSE_HALO_ACTION_AUDIT.md` shows finite carriers with locally sofic
labels are circular here — a finitely generated subgroup of `U(n)` is linear,
hence residually finite, hence sofic. A finitely additive charge is not a
finite carrier and is not produced by exhibiting one: charges come from
Hahn–Banach, from invariant means, from ultrafilter limits. That is a different
toolbox from the one the nine dead routes exhausted, and it is the reason this
lane is not a variation on them.

It also composes with the established foothold. `positive-core-bernoulli-ce`
gives an honest sofic action `Γ ↷ X₀`, hence by Elek–Szabó an essentially free
amenable almost-action of `Γ` on a set; the question is whether the charge
extends over the compressors. That is a charge-level version of
`simultaneous-dilation-splice`, and extending a finitely additive measure is
the kind of thing Hahn–Banach does and a von Neumann algebra permanence theorem
does not. Whether the two versions have the same difficulty is untested and is
the first thing to check.

## Resolved: the genuine shadow is rigid

The paragraph below was written when Bekka's statement was unread and therefore
unusable. It is now settled, by proof rather than by citation, as
`amenable-rep-of-kazhdan-has-fd-subrep`: an amenable representation of a
Kazhdan group has a nonzero finite-dimensional subrepresentation. Restricting
the invariant state to `G ≤ W` makes `π|_G` amenable, and `G` is Kazhdan, so a
*genuine* essentially free amenable representation of `W` would carry a
finite-dimensional subrepresentation of `G` — precisely the regime where
`commutant_no_growth` and the `finrank` instance of
`no_strict_compression_of_invariantSize` bite.

So the whole content of the criterion at `W` sits in the gap between *near* and
*genuine*. The lane is not dead, but it is not independent of the rigidity
branch either: it is independent exactly to the extent that flexibility is.
Anyone building a charge here should know they are building an object with no
genuine shadow, and that is the specification, not an accident.

The first concrete attempt is also closed: `induced-charge-extension` is
invalidated by `no-invariant-mean-on-coset-space`, so the positive core's
charge does not extend by induction.

## Superseded — the original flag, kept for the record

There is a plausible sharp obstruction on this lane that I could not verify and
am therefore not asserting. Bekka, *Amenable unitary representations of locally
compact groups*, Invent. Math. 100 (1990) 383–401, is reported to describe the
amenable representations of property (T) groups via the Hulanicki–Reiter
theorem; the statement I expected is that for `G` with property (T) a unitary
representation is amenable exactly when it has a finite-dimensional
subrepresentation. **I did not read it** — the Springer full text is behind an
authentication wall and two secondary sources did not restate it. If it is
true in that form, then a *genuine* amenable representation of `W` would carry
a finite-dimensional subrepresentation, which `finite-quotient-blindness` would
then attack, and the entire content of the criterion would sit in the gap
between "near" and "genuine" — i.e. in flexible stability, the same fork as
everything else. Verifying that sentence is cheap and would immediately tell us
whether this lane is independent of the rigidity branch or secretly the same
question. Until then it is a conjecture about the literature, not an input.
