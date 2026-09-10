---
rg: 2
id: fpbs-qb-action-bound
kind: claim
title: Every free action of B(2,n) has cost at most the explicit number U_n
root: true
---

**Statement.** For n>=3 and 0<=q<=1 put

    B_n(q) = 1 - 1/n + q + (1-q)(1-q^(n-1))^n - q^n/n,
    U_n    = min_{0<=q<=1} B_n(q).

Theorem 4.1 of the explicit-bound note: for odd n>=1003, every free p.m.p. action alpha of B(2,n)
satisfies 1 <= C(alpha) <= U_n < 2 - 2/n. The strict improvement comes from the pruning term: with
q=1-t, B_n(1-t) = 2 - 2/n - (n-1)t^2/2 + O_n(t^3), so every sufficiently small t>0 beats the coarse
bound. The gain is logarithmic on the 1/n scale, lim_n n(2-U_n)/log n = 1, witnessed by the explicit
parameter q_n = (log(n)/n)^(1/(n-1)). U_n is an upper bound on the cost of every action, not an exact
action cost, and not a fixed-price assertion.

**Proof location.** `research/artifacts/fpbs/burnside-explicit-bound.md`, Section 4, using the torsion
repair of Theorem 2.1 and the cycle pruning of Lemma 3.1; response 34.

**Imported inputs.** Gaboriau, arXiv:1011.2294v1 (definitions, infinite-action lower bound one).
Donoso-Echenique-Silva, *Free Burnside groups of large odd exponent have cost 1*, arXiv:2608.20472v1,
for the centralizer and subgroup-embedding lemmas; the archive correctly reads their Theorem 1.2 as
infimal group cost and not as fixed price. Abert-Weiss, arXiv:1103.1063v2. All three identifiers
resolve with matching titles and authors.

**Finite-replay evidence.** `research/artifacts/fpbs/burnside-explicit-checks.json` via
`scripts/replay_burnside_explicit.py`: status "finite checks passed", 12,732 assertions, 4,160
exhaustive labelings, 234 interval checks, over S_3 and A_4 fixtures with exact rational expectations
against the proved pruned upper bounds. The audit records that the numeric minima are not certified
and that the rational parameter bounds are outward rounded.

**Evidence level.** Written deduction with named published inputs and a passing finite replay of the
rational expectation identities. Not refereed, not formally verified. The bound stays strictly above
one, so this does not decide whether B(2,n) has fixed price one.

Status reflects a written deduction or imported input, not independent mathematical verification.
