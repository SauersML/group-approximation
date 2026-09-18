---
rg: 2
id: rokhlin-excess-never-drops-under-bernoulli-transfers
kind: claim
title: The excess of a Bernoulli isomorphism over the Rokhlin supremum never drops under products, chaining, co-induction or finite-index restriction, so transfers cannot prove the rigidity threshold
distinct_from:
  bernoulli-rigidity-threshold-equals-rokhlin-supremum: that is the open claim that nontrivial Bernoulli isomorphisms reach down to the supremum; this proves that the multi-group transfer calculus cannot lower their distance to the supremum, and when the claim passes between groups.
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that proves the transfer rules one group or one step at a time; this composes them over arbitrary chains of groups and proves the excess over the supremum is a Lyapunov function for all of them.
  bernoulli-collapse-is-null-or-eventually-total: that gives a one-group formal model separating eventual collapse from the threshold claim; this kills every multi-group transfer derivation from seeds of positive excess, and proves permanence of the threshold claim.
  bernoulli-entropy-counterexample-constraints: that records qualitative constraints on a counterexample; this gives the quantitative supremum inequalities along finite index and overgroups, and the defect bound along whole paths.
artifacts:
  - research/artifacts/rokhlin-excess-transfer-lyapunov-2026-09-17.md
---

Proof: [[rokhlin-excess-never-drops-under-bernoulli-transfers-proof]], with full details in the artifact.

**Setting.**
- Groups are countably infinite, `s(G) = h^Rok_sup(G)`, and `X_h` is the Bernoulli shift over `G` of base entropy
  `h`.
- `a ~_G b` means `X_a ≅ X_b` over `G`. `R(G)` and `r(G)` are as in `bernoulli-collapse-is-null-or-eventually-total`.
- The **excess** of a nontrivial pair `a ~_G b` is `min(a, b) − s(G) ≥ 0`.

**Theorem.**
1. **Supremum inequalities.**
   - If `G ≤ Γ` and `s(G) < ∞`, then `s(Γ) ≤ s(G)`.
   - If `H ≤ G` has index `k` and `s(G) < ∞`, then `s(G) ≤ s(H) ≤ k s(G)`.
2. **Excess floor.** Let `S` be a set of seed pairs `(G, a, b)` with `min(a, b) ≥ s(G)`. Let `T(S)` be the smallest
   family of equivalence relations on levels, one per group, that contains `S` and is closed under
   - translation `a ≈_G b ⇒ a + t ≈_G b + t`,
   - co-induction `a ≈_G b ⇒ a ≈_Γ b` for `G ≤ Γ`,
   - restriction `a ≈_G b ⇒ ka ≈_H kb` for `H ≤ G` of index `k`.

   Every nontrivial pair of `T(S)` over `Γ` has `min(a, b) ≥ s(Γ) + δ_S(Γ)`. Here `δ_S(Γ)` is the infimum, over
   seeds and finite paths of co-induction and restriction steps from the seed's group to `Γ`, of the seed excess
   pushed along the path. A co-induction step adds `s(G_i) − s(G_(i+1)) ≥ 0`. A restriction step multiplies by
   `k_i ≥ 1` and adds `k_i s(G_i) − s(G_(i+1)) ≥ 0`.
3. **Class kill.** If `T(S)` witnesses `bernoulli-rigidity-threshold-equals-rokhlin-supremum` at `Γ`, then for every
   `ε > 0` some seed has excess `< ε` and reaches `Γ` along a path whose every step has defect `< ε`. So seeds of
   excess bounded below, such as eventual collapse at a fixed `M > s`, or seeds co-induced from groups of strictly
   larger supremum, never give the claim.
4. **Permanence.** Write H2(G) for the threshold claim at `G`.
   - If `G ≤ Γ` and `s(Γ) = s(G) < ∞`, then H2(G) ⇒ H2(Γ).
   - If `H ≤ G` has index `k` and `s(H) = k s(G) < ∞`, then H2(G) ⇒ H2(H).
   - Among groups with `s = 0`, H2 passes to all overgroups and all finite-index subgroups. So it is a
     commensurability invariant there.
5. **Counterexamples.** Suppose `s(Γ) < ∞` and `r(Γ) > s(Γ)`.
   - Every subgroup `G ≤ Γ` has `r(G) ≥ r(Γ)`. So a subgroup satisfying H2 has `s(G) ≥ r(Γ)`.
   - Every index-`k` subgroup `H` has `r(Γ) ≤ r(H) ≤ k r(Γ)`.
   - H2 fails at every subgroup of `Γ` with the same supremum.

**Reading.**
- Every construction of Bernoulli isomorphisms that the graph records as moving between groups or levels is a step
  of `T`, together with Seward's equal-entropy theorem.
- So a proof of the threshold claim must lower the excess by a step outside `T`. The options are:
  - cancellation of a common Bernoulli factor, which is recorded dead on the target;
  - a primitive isomorphism of excess `< ε` at some group, which is the claim up to `ε` at that group.
- Nothing here constructs a group with finite supremum or proves any level rigid.
