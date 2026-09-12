---
rg: 2
id: fpbs-prime-divisor-upper-cost
kind: claim
title: The least prime divisor improves every-action Burnside cost to two minus two over that prime
root: true
---

**Statement.** Theorem 5 of the local-sparsifier note: let n>=1003 be odd with smallest prime divisor
p. Then every free p.m.p. action of B(m,n), m>=2, has cost at most 2 - 2/p, and the same bound holds
for every infinite finitely generated subgroup. When 3 divides n this gives 4/3. It is an upper bound
on every action's cost, not an exact action cost and not a fixed-price assertion.

The mechanism is that the least prime divisor, rather than n itself, sets the price of the cyclic
backbone. The powers a_1^(n/p) and a_2^(n/p) have order p and do not commute, since C(a_1^(n/p)) =
<a_1> while the two cyclic generator subgroups meet trivially by abelianization. Adjoining both to a
finite generating set and running the original-action construction costs 1-1/p for each cyclic part
and at most epsilon for the remaining generators. No original-edge claim is made for this sharper
bound.

**Proof location.** `research/artifacts/fpbs/local-sparsifiers.md`, Section 10, on the action-level
sparsifier of Section 7; response 30.

**Imported inputs.** Ivanov, *On subgroups of free Burnside groups of large odd exponent*,
arXiv:math/0210191, for the embedding of B(infinity,n) in every noncyclic subgroup at large odd
exponent. Donoso-Echenique-Silva, arXiv:2608.20472v1, Lemma 2.4 for cyclic centralizers and Theorem 2.5
for the refined subgroup embeddings; the archive reads their cost-one theorem as infimal cost, which is
correct. Osin, arXiv:math/0404073v1, for uniform non-amenability. Abert-Weiss, arXiv:1103.1063v2,
Theorem 1, for finite-pattern approximation inside the original free action, explicitly not an actual
independent labeling. All four identifiers resolve with matching titles and authors.

**Finite-replay evidence.** `research/artifacts/fpbs/local-sparsifier-checks.json` via
`scripts/replay_local_sparsifiers.py`: status PASS, with 28,216 cut-deletion pairs over cycles of
lengths 3, 5, 7, 9 and 11 and eighteen exact selector-density identities.

**Evidence level.** Written deduction with four verified published inputs and a passing finite replay of
the cycle-boundary and retention identities. Not refereed, not formally verified. The bound is strictly
above one, so it does not decide fixed price for large odd Burnside groups; that target remains OPEN
as `fpbs-burnside-upper-cost-one`.

This route records a written proof or cited input; Cairn does not independently verify mathematics.
