---
rg: 2
id: defect-normally-generates-torsion-free-quotient
kind: claim
title: The simple factor can be made to normally generate a Kazhdan subgroup of the quotient
distinct_from:
  fournier-facio-torsion-free-skeleton: that claim is established and records what the published construction already gives; this one is the single additional demand on the small-cancellation step.
  torsion-free-countable-non-mf: that claim is an existence statement about non-MF groups; this one is pure combinatorial group theory about a common quotient and mentions no operator algebra.
  torsion-free-higman-embedding: that claim is about embedding recursively presented torsion-free groups into finitely presented ones; this one is about the normal closure of a prescribed subgroup in a small-cancellation quotient.
---

In the Fournier-Facio construction (`fournier-facio-torsion-free-skeleton`)
the Hull common quotient `pi : E -> G` can additionally be arranged so that
the normal closure `K = <<pi(S)>>^G` of the simple factor is a **Kazhdan**
subgroup of `G` — for instance so that `K` has finite index in `G`, or
`K = G`.

This is the only gap between the published torsion-free group and a
torsion-free finitely presented non-MF group: `K` is automatically normal,
nontrivial, and contained in the compression defect, and property (T) of `G`
passes to `K` as soon as the index is finite.

**It buys more than it is asked for.**  In its strongest form `K = G`, this
claim also makes `G` minimally almost periodic, by
`fournier-facio-group-finite-dimensional-shadow` clause 3 — and minimal
almost periodicity of the Kazhdan source is precisely the hypothesis that
both open analytic branches of the central-mark route independently require
(`bounded-rank-corners-excluded` and
`finite-dimensional-models-break-coordinate-generation`).  So a single
small-cancellation fact would serve the primary route and both secondary
ones.  That is a reason to attack this claim before any of the analytic
holes.

## Ideas

Three ways to buy it, in increasing order of strength.

- *Finite index.*  The weakest sufficient form, and the one to attack first.
  Property (T) is inherited by finite-index subgroups, so it is enough that
  `G / <<pi(S)>>` be finite.  Hull's small cancellation adds finitely many
  relators to `E * H`; the natural move is to add, alongside the relators
  producing the common quotient, relators expressing each generator of `G`
  as a word in conjugates of `s`.  This is the same style of step that
  Fournier-Facio already uses to embed `U` into `P`, so the machinery is on
  hand; what must be checked is that the added relators still satisfy the
  small-cancellation condition and still preserve torsion-freeness
  (Hull, Theorem 7.1(e)) and finite presentability.
- *Simplicity.*  If `G` can be taken simple then `K = G` and there is
  nothing to check.  Beware: this asks for a finitely presented simple group
  with property (T) and no torsion.  Quotients of Kazhdan groups are
  Kazhdan, so the (T) is free, but finitely presented plus simple is a
  serious extra demand — Burger--Mozes and Hyde--Lodha groups are finitely
  presented, simple and torsion-free but are not Kazhdan, and the standard
  routes to simple small-cancellation quotients produce direct limits, which
  are not finitely presented.  Do not assume this is available.
- *Routed defect.*  The strongest form, and the one the repository already
  formalized: `defectNormal.map source = top`, the field `defect_surjective`
  of `RelativeCommonQuotientData` in the development deleted by commit
  `241440fe`, pinned by revision path — read it with
  `git show 241440fe^:GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`.
  That development derives the whole non-MF package from this field, so a
  proof of it — for the published Fournier-Facio quotient rather than for
  hypothetical routing data — closes the root outright.

An honest warning about all three: the demand interacts with the rest of the
construction, because `pi|_S` must stay injective (Fournier-Facio needs it,
and `fournier-facio-torsion-free-skeleton` needs `S'` to be centreless).
Adding relators that fold generators into the normal closure of `s` must not
collapse `S` itself.  Simplicity of `S` gives the usual dichotomy — the
image of `S` is trivial or faithful — so the real content is keeping it
nontrivial, which is exactly what Hull's finite-set injectivity clause
already delivers in the published step.
