---
rg: 2
id: fpbs-amen2-fixed-price-one
kind: claim
title: Every countably infinite group with all two-generated subgroups amenable has fixed price one
root: true
---

**Statement.** Every countably infinite group all of whose two-generated subgroups are amenable has
fixed price one. Two independent routes reach it. The direct route composes the bounded-exponent case
with the published unbounded-exponent case and glues countable exhaustions by relative cost. The
action-wise route is a one-line corollary of Theorem 6.2: in any free action, an infinite amenable pair
subgroup restricts to cost one and a finite pair subgroup of order h restricts to cost 1-1/h, so the
two-generator hypothesis holds and C(alpha)=1 for every alpha. The contrapositive, recorded separately
as Corollary 7.2, is that a countable group with a free action of cost above one contains a
two-generated nonamenable subgroup.

This does not settle the universal Fixed Price problem. It is a class theorem whose class is defined
by a two-generated-subgroup condition.

**Proof location.** `research/artifacts/fpbs/amen2-complete-proof.md` for the direct route and
`research/artifacts/fpbs/two-generator-complete-proof.md`, Section 6, for the action-wise route;
responses 14 and 15.

**Imported inputs.** Ershov-Golan-Sapir, arXiv:1401.2202, Theorem 5.6 supplies the finitely generated
unbounded-exponent case outright, and Lemma 5.7 the relative-cost bound relC(R;S) <= C(R)-1 for
aperiodic S. Gaboriau, arXiv:1011.2294v1, for the amenable cost theorem and Proposition 2.39.
Suchkova-Shunkov as stated in Chernikov, arXiv:0711.2597v1, and Chernikov's own arXiv:0710.1979v1 for
the membership of binary-finite groups and 2-groups among periodic Shunkov groups. All four
identifiers resolve with matching titles and authors. Finite-index multiplicativity of cost is
explicitly not an input.

**Finite-replay evidence.** `amen2-proof-audit.json`, status WRITTEN_PROOF_WITH_PUBLISHED_INPUTS,
reusing `bounded-exponent-reaudit-checks.json` (PASS, 48,584 exact assertions, 5,952 exhaustive
colorings). The audit lists eight audited distinctions, among them that the construction stays in the
same original action with no Bernoulli extension, that selector and repair costs are summed, and that
binary finiteness is not asserted to be local finiteness.

**Evidence level.** Written deduction with named published inputs and a passing finite replay of the
combinatorial steps. Not refereed, not formally verified. The unbounded-exponent finitely generated
half is a published theorem; the bounded-exponent half and the countable assembly are the archive's own.
