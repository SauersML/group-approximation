---
rg: 2
id: fpbs-bounded-exponent-two-groups-fixed-price
kind: claim
title: Every countably infinite bounded-exponent 2-group has fixed price one
root: true
---

**Statement.** Corollary 8.1 of the bounded-exponent note: for every r>=1, every countably infinite
group G with g^(2^r)=e for all g has fixed price one, that is, all its free p.m.p. actions have cost
one. Held's theorem gives an infinite abelian subgroup, which is torsion and therefore locally finite,
so its restricted action has cost one; the bounded-exponent subgroup theorem transfers that upward.
Bounded exponent is essential to the transfer, not to Held: no conclusion follows for 2-groups whose
element orders are unbounded.

The transfer step is Theorem 4.1 of the same note: if g^N=e for a fixed N and H<=G is infinite, then
relC(R_G;R_H)=0, C(alpha) <= C(alpha restricted to H) for every essentially free action alpha, and
C*(G) <= C*(H). No centralizer commutativity, centralizer cardinality bound, finite generation or
normality is assumed.

**Proof location.** `research/artifacts/fpbs/bounded-exponent-progress.md`, Section 8.1, on Theorem 4.1
of Section 4 and the locally finite calculation of Section 1; response 15.

**Imported inputs.** Held, *On abelian subgroups of infinite 2-groups*, the theorem on page 97: every
infinite 2-group contains an infinite abelian subgroup. The note records that the original two-page
paper was read visually and that it proves the infinite-abelian assertion rather than the weaker
unbounded-finite-subgroup one; Ivanov records the weaker consequence. This import has no arXiv
identifier and could not be machine-checked. Gaboriau, arXiv:1011.2294v1, for locally finite cost.

**Finite-replay evidence.** `bounded-exponent-checks.json` and the identical
`bounded-exponent-reaudit-checks.json` via `scripts/replay_bounded_exponent.py`: status PASS, 48,584
exact assertions across nineteen categories, including 13,744 power-fiber-in-centralizer checks, 6,546
centralizer coset identities, 5,952 exhaustive labelings for the generated relation and 5,952 for paid
repair.

**Evidence level.** Written deduction with one non-arXiv published input and a passing finite replay of
its combinatorial core. Not refereed, not formally verified. The companion Corollary 8.2, recorded as
`fpbs-large-even-burnside-fixed-price`, gives fixed price one for B(m,n) with n>=2^48 and 2^9 dividing
n, on Ivanov's infinitude and Ivanov-Olshanskii's locally finite subgroups.
