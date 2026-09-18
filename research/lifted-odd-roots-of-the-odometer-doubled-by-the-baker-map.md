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

## Attempt 1 (this lane): the pure baker ansatz has NO solution (proved)

**Claim.** With u the baker map and r = (τ^{k(y)}x, ρy), ρ ∈ V, conditions (A)+(B) have no solution. So no odd root of s of this form is squared by u.

**Proof.**
- **Injectivity forces a first-letter XOR.** For fixed y, the points 0y and 1y both go to tail ρ^{-1}(y). So e(0,y) ≠ e(1,y). From the formula for e, this forces k(1y) − k(0y) ∈ {0,1}. Hence ρ(x_0 y) = (x_0 ⊕ f(y)) · ρ^{-1}(y), with f(y) = k(1y) − k(0y).
- **Both ρ and ρ^{-1} have this shape.** Inverting gives ρ^{-1}(z_0 w) = (z_0 ⊕ f(ρw)) · ρ(w).
- **So ρ is synchronous.** Unfolding the two formulas alternately emits exactly one output digit per input digit. So ρ is a tree automorphism: digitwise XOR with bits that depend on the tail.
- **So ρ is finitary.** A tree automorphism lying in V is finitary: it changes only positions < N for some N.
- **Propagation contradiction.** Let n be the least position that ρ changes at some point.
  - If n ≥ 1, then ρ^{-1} changes position n − 1 somewhere. Then so does ρ, contradicting minimality. So n = 0.
  - If ρ changes position 0 at y, then ρ^{-1} changes position 0 at ρ(y). Since ρ(x_0 z) has tail ρ^{-1}(z), ρ then changes position 1. By induction ρ changes every position, so ρ is not finitary.
  - Hence ρ = id. But then (A) reads 3k = 1, which is impossible. ∎

## Reformulation for other doubling elements (OPEN)

Every u' = u∘c with c = (τ^{j(y)}x, g y) (g ∈ V) centralizes-then-doubles: u' s u'^{-1} = s². Then u' r u'^{-1} = r² exactly when:
- ρ̃ := g ρ g^{-1} satisfies ρ̃ = Ψ_f(ρ^{-1}), where Ψ_f(h)(x_0 y) = (x_0 ⊕ f(y)) h(y);
- the cocycle equation for (k, j) coming from the e-condition holds.

Ψ_f(ρ^{-1}) lies in V, and it has order 3 iff f sums to 0 mod 2 over ρ-orbits. The propagation argument does not apply here, because g breaks synchronicity.

So the q = 3 step reduces to two things:
- (i) a V-conjugacy g ρ g^{-1} = Ψ_f(ρ^{-1}) between two order-3 elements of V. Higman-type conjugacy of torsion in V makes this plausible, but I have not checked it.
- (ii) a linear cocycle equation for k.

The full target also needs ONE u' working for all odd q at once.

## Attempt 2 (bh-free-30): every single odd q is solved; the uniform doubling element is open

- **Each q separately.** `odd-roots-of-the-2v-tau-odometer-have-doubling-conjugators` settles (i) and (ii) for every odd q, with explicit formulas.
  - For (i): with ρ a single q-cycle of cones A_i, the element g(A_i x w) = x A_{2i} w of V satisfies gρg^{-1} = Φ(ρ²), with f = 0.
  - For (ii): take k odd with orbit sums 1. Then k̃ = (k + k∘ρ)/2, and j solves one coboundary equation.
  - So for each odd q, 2V_τ contains a q-th root r_q of s and a u_q = u∘c_q with u_q r_q u_q^{-1} = r_q².
  - Note that for general q the target condition is gρg^{-1} = Ψ_f(ρ²). The earlier form Ψ_f(ρ^{-1}) is the special case q = 3.
- **Reduction for the full target** (sketch only, not claimed). Elements commuting with s should be fibered, (x + k(y), ρy). The reason: τ is minimal, so s-orbit closures are the fibers, and the centralizer of the odometer in Homeo(Z_2) is Z_2. If so, the ansatz is general, and Q ⋊ ⟨2⟩ with s = 1 ↦ odometer needs three things:
  - a free action ρ of L = Q_odd/Z on C by V;
  - ONE g ∈ V with gρ(a)g^{-1} = Ψ_{f_a}(ρ(2a)) for all a ∈ L, so that C ≅ C^{×2} ⊔ C^{×2} as L-spaces via a V-map;
  - a cocycle k: Q_odd × C → Z lifting ρ, with k_1 = 1 and the e-conditions for one j.
  The per-level solutions don't glue. Along a tower q_1 | q_2 the canonical g's move different letters to the front, so the open problem is to design a "self-similar" free L-action.
