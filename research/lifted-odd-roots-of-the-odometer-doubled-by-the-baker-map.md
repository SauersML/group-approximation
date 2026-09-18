---
rg: 2
id: lifted-odd-roots-of-the-odometer-doubled-by-the-baker-map
kind: claim
title: Some odd root of the 2V_tau odometer built from a V-torsion lift is squared by a doubling element, the first step toward Q semidirect 2 inside the F_infinity simple host 2V_tau
target: affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q
requires:
  - odometer-2v-is-fp-simple-and-contains-bs12
  - odometer-lift-central-extensions-of-v-subgroups-into-2v-tau
distinct_from:
  affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q: that node proves the NATURAL (translation) copy of Q semidirect <2> lies in no finitely generated affine 2V_H host, and leaves wild copies open; this claim proposes a specific wild copy, built from lifts of torsion of V as in the odometer-lift node, and reduces its first step to explicit functional equations.
  odometer-generators-carry-no-nonsolvable-baumslag-solitar: that forbids BS(m,n) with m or n odd on the odometer generator itself; here the doubling conjugation is u r u^{-1} = r^2, a BS(1,2) relation on the odd root r, which that node does not exclude.
---

**OPEN.** Lane bh-free-30 (09-18), a construction target outside the ring and prime-shift frames of the GL_n(Q) campaign. It is the n = 1 affine step: Q ⋊ ⟨2⟩ ≤ Aff(Q) ≤ GL_2(Q).

## Setting

- 2V_τ is F_∞ and simple and contains s = τ × id and the inverse baker map u(x, y_0 y) = (y_0 x, y), with u s u^{-1} = s^2 (`odometer-2v-is-fp-simple-and-contains-bs12`).
- For ρ ∈ V acting on the second coordinate and a locally constant k: C → Z, put r(x, y) = (τ^{k(y)} x, ρ y). This lies in 2V_τ, the topological full group, as in `odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`.

## The claim (q = 3 first)

There are ρ ∈ V of order 3 and k with
- **(A)** k(y) + k(ρy) + k(ρ²y) = 1 for all y, so r³ = s;
- **(B)** for all x_0 ∈ {0,1} and y: ρ(x_0 y) = e · ρ²(y), with e = x_0 + k(y) + k(ρy) − 2k(x_0 y) ∈ {0,1}.

**Why (A)+(B) is the right target (computed here).** Write x = x_0 + 2x' and ρ(x_0 y) = e w. Then u r u^{-1}(x, y) = (e + 2x' + 2k(x_0 y), w), while r²(x, y) = (x_0 + 2x' + k(y) + k(ρy), ρ² y). So u r u^{-1} = r² exactly when (B) holds. Given (A), (B) says ρ is a lookahead wreath recursion whose section on each first-letter cone is ρ² = ρ^{-1}.

**Consequence.** ⟨r, u⟩ is then a quotient of BS(1,2) on the odd root r of s. It is faithful, since r has infinite order (r³ = s). So the u-tower of r gives (1/3)·Z[1/2] inside 2V_τ, normalized by u acting as ×2.

**Full target.** For each odd q, a q-th root r_q of s of the same form (order-q ρ_q ∈ V, and k_q summing to 1 over ρ_q-orbits), with r_{qq'}^{q'} = r_q and u r_q u^{-1} = r_q². This embeds Q ⋊ ⟨2⟩ = Z[1/2]-closure of (∪_q r_q) ⋊ ⟨u⟩ in the F_∞ simple group 2V_τ. That would answer the wild-copy question left open by `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`.

## Attempt 1 (this lane)

- If e depends only on x_0 (a first-letter permutation π with ρ = π·(ρ², ρ²)), then ρ³ = 1 forces π = id, and then ρ(x_0 y) = x_0 ρ^{-1}(y). Recursively, ρ = id. So any solution needs **lookahead**: e must depend on y through k, which is locally constant.
- A binary first letter can't carry an order-3 permutation. So solutions must use k's lookahead to decide the output letter. This is the design problem.

## Open

Solve (A)+(B), or show it has no solution in V with u the baker map. In the latter case, any doubling element u' with u' s u'^{-1} = s² may replace u, giving a larger search space: the same computation with u' in place of u.
