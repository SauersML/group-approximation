---
rg: 2
id: sl2-root-triangle-2dim-iff-zero-frobenius-holonomy
kind: claim
title: A Kazhdan SL_2 root triangle has a nontrivial two-dimensional representation iff its gluing twists are semilinear with zero Frobenius holonomy, and then it maps onto SL_2(q^2) injectively on vertex groups
distinct_from:
  sl2-root-triangle-2dim-reps-force-semilinear-gluing: that proves only the necessity of semilinear twists; this adds the necessary holonomy condition and proves sufficiency by an explicit configuration
  sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2: that treats the identity gluing, plus a scalar twist on one edge; this treats every gluing and decides exactly which members map onto SL_2(q^2)
artifacts:
  - research/artifacts/sl2-root-triangle-frobenius-holonomy-2026-09-16.md
---

**Setting.** Take the data and notation of `sl2-root-triangle-char2-frobenius-spectrum-transport`:
- `q = 2^f >= 8`, `k = F_q ⊂ F = F_{q^2}`, `s ∈ F \ k`;
- relative twists `φ_e = α_j^e (α_i^e)^{-1} ∈ GL(k,+)` for `e = 12, 13, 23`.

When all twists are semilinear, `φ_e(x) = λ_e x^{2^{a_e}}` with `λ_e ∈ k^*` and `a_e ∈ Z/f`, the **Frobenius
holonomy** is `hol = a_12 + a_23 - a_13 ∈ Z/f`.

**ESTABLISHED (unreviewed).** For the colimit `Λ` the following are equivalent:
1. `Λ` has a nontrivial homomorphism to `GL_2(K)` for some field `K`.
2. `Λ` has a homomorphism onto `SL_2(q^2)` that is injective on every vertex group.
3. All three relative twists are semilinear and `hol = 0`.

When they hold, the kernel in (2) is torsion-free, by `triangle-of-groups-half-girth-structure` (iv). So
`Λ` is virtually torsion-free, with a nontrivial finite quotient.

**The configuration for 3 ⇒ 2.** Let:
- `b_1 = a_13`, `b_2 = a_23`, `b_3 = 0`;
- `μ_12 = λ_12^{2^{a_23}}`, `μ_13 = λ_13`, `μ_23 = s λ_23`, `ν = μ_13 μ_23`;
- `τ, ω, P ∈ F` with `τ^2 = 1/μ_13`, `ω^2 = 1/μ_12`, `P^2 = μ_12/ν`;
- `h = [[P,1],[1,0]]`, `g_1 = h`, `g_2 = h·u(1/P)·diag(ω, ω^{-1})`, `g_3 = diag(τ, τ^{-1})`.

Then `ρ_i = conj_{g_i} ∘ Frob^{b_i}` agree on the three edge groups. Here `Frob^{b}` raises every matrix
entry to the power `2^{b}`.

**Calibration.**
- The untwisted member has `hol = 0`, and the configuration reduces to the one of
  `sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2`.
- `experiments/sl2-root-triangle-frobenius-holonomy-2026-09-16/holonomy.py` checks the configuration on
  every edge element:
  - 80 random zero-holonomy semilinear gluings for `q = 8`, all passing (`out-q8.txt`);
  - 40 for `q = 16`, all passing (`out-q16.txt`).
- As an independent calibration, a search over `K = F_64` alone (`q = 8`, `ρ_3` the identity up to
  Frobenius) finds configurations for each of 5 zero-holonomy gluings. It finds none for 3 gluings with
  `hol ≠ 0`, nor for one non-semilinear gluing.

**Counts of relative-twist triples** (not isomorphism classes of `Λ`):

| `q` | all triples | semilinear | `hol = 0` | semilinear, `hol ≠ 0` |
|---|---|---|---|---|
| 8 | 4,741,632 | 9,261 | 3,087 | 6,174 |
| 16 | 8,193,540,096,000 | 216,000 | 54,000 | 162,000 |

In general `hol = 0` holds for `f^2 (q-1)^3` triples.

**Consequence for `sl2-root-kazhdan-triangle-without-finite-quotients`.**
- Zero-holonomy semilinear members are virtually torsion-free, so they are not candidates.
- Semilinear members with `hol ≠ 0` have no nontrivial 2-dimensional representation. So they join the
  non-semilinear members as the remaining candidates.

**What it does not say.**
- It says nothing about representations of dimension `>= 3`, or about finite quotients that are not linear
  in dimension 2.
- By `sl2-root-triangle-char2-frobenius-spectrum-transport`, a candidate with `f = 3` has no nontrivial
  representation of dimension `< 4`. Steinberg-type `q`-dimensional representations are not excluded.

Proof: `sl2-root-triangle-2dim-iff-zero-frobenius-holonomy-proof`.
