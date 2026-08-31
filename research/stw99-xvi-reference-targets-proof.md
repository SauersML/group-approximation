---
rg: 2
id: stw99-xvi-reference-targets-proof
kind: route
title: Divisibility absorption one way, ultrapower embedding the other, and mutual absorption closes
target: stw99-xvi-holds-for-reference-targets
requires: [ssa-unit-divisibility-forces-uhf-absorption]
artifacts:
  - research/artifacts/stw99-xvi-reference-cases-2026-08-30.md
---

Throughout, `D` is simple and nuclear (approximately inner flip,
Effros--Rosenberg) and satisfies the Toms--Winter dichotomy: stably
finite with unique trace, or purely infinite.  Two strongly
self-absorbing algebras absorbing each other are isomorphic
(Toms--Winter's Elliott-intertwining proposition); we verify mutual
absorption in each case.

**`E = O_2`.**  `[1_D] = 0` forces `D` non-stably-finite (a
quasitrace state on `(K_0, [1])` would give `1 ↦ 1 ≠ 0`; more simply,
a faithful trace makes `[1]` nonzero), so `D` is a Kirchberg algebra.
`[1] = [1] + [1]` realizes (Cuntz class arithmetic, as in the
required claim's proof) two isometries with complementary ranges:
a unital `O_2 → D`.  Tail-centrality (the required claim) gives
`O_2 → D_ω ∩ D'`, so `D ≅ D ⊗ O_2`; and `D ⊗ O_2 ≅ O_2` holds for
every unital simple separable nuclear `D` (Kirchberg's
`O_2`-absorption theorem).  Hence `D ≅ O_2`.

**`E = Q ⊗ O_∞`.**  The all-positive order forces `D` purely
infinite (a stably finite `D` has a faithful quasitrace state
separating `±x`), so `D` is a Kirchberg algebra and
`D ≅ D ⊗ O_∞` (Kirchberg).  `[1] = 1 ∈ Q = K_0(D)` is `p`-divisible
for every `p`, so the required claim gives `D ≅ D ⊗ Q`.  Hence
`D ≅ D ⊗ (Q ⊗ O_∞)`.  Conversely the hypothesis gives a unital
`D → (Q ⊗ O_∞)_ω`, and the required claim's central-upgrade
homomorphism turns it into `D → (Q ⊗ O_∞)_ω ∩ (Q ⊗ O_∞)'`, so
`Q ⊗ O_∞ ≅ (Q ⊗ O_∞) ⊗ D`.  Mutual absorption closes.

**`E = Q`.**  The strict order and unique state force the finite side
of the dichotomy.  `[1]` is `p`-divisible for all `p`, so
`D ≅ D ⊗ Q` by the required claim.  Conversely, `D` nuclear and
quasidiagonal gives asymptotically multiplicative unital u.c.p. maps
into matrices; the ultraproduct is a unital `*`-homomorphism
`D → ∏_ω M_{n_i}`, and each `M_{n_i}` embeds unitally into `Q`
(every integer divides the universal supernatural number), giving
`D → Q_ω`, then `D → Q_ω ∩ Q'` by the central upgrade, so
`Q ≅ Q ⊗ D`.  Mutual absorption closes.

**Why the remaining targets resist.**  For `E = M_{J^∞}` (proper
`J`) the first direction works verbatim (`[1]` is `J`-divisible), but
the second needs unital models of `D` in matrix algebras of
`J`-supernatural size; arbitrary QD models have unconstrained sizes
and cannot be dilated into `J`-sizes (unital `M_n → M_m` needs
`n | m`).  For `E = O_∞` and `E = Z` there is no divisibility to
spend at all, and a unital `O_2` never helps (`[1] ≠ 0` blocks it).
These are recorded as the problem's true residue.
