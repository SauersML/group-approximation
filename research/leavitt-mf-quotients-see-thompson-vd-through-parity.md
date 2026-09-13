---
rg: 2
id: leavitt-mf-quotients-see-thompson-vd-through-parity
kind: claim
title: Every homomorphism from a Leavitt unit group L_k(1,d)^x to an MF group sees the Higman–Thompson group V_d at most through its parity character, and kills V_d when d is even or −1 is a (d−1)-th power in k
distinct_from:
  purely-infinite-unit-group-max-mf-quotient-is-k1: that computes the maximal MF quotient of the whole unit group as K_1; this computes what that quotient sees of the distinguished subgroup V_d, namely at most its parity.
  leavitt-cylinder-swaps-generate-thompson-in-el: that places V inside an elementary prefix group over the binary Leavitt algebra in characteristic two; this is the MF-radical position of V_d for every d and every countable field, through K_1 classes of transpositions.
artifacts:
  - research/artifacts/un-full-groups-bridge-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Route: `leavitt-mf-quotients-see-thompson-vd-through-parity-proof`.

**Setting.** `k` is a countable field, `d >= 2`, `R = L_k(1,d)` and `H = R^×`. `V_d = V_(d,1) = [[𝒢_d]] ⊆ H` via the
bisection units, and `κ : H -> K_1(R)` is the canonical map.

1. `κ(V_d) = ⟨[−1]⟩`, of order at most 2. So every homomorphism from `H` to an MF group maps `V_d` onto a group of
   order `<= 2` and kills `D(V_d)`.
2. If `d` is even or `−1 ∈ (k^×)^(d−1)`, then `V_d ⊆ Rad_MF(H)`. In particular Thompson's `V` lies in the MF radical of
   every binary Leavitt unit group.
3. If `d` is odd and `−1 ∉ (k^×)^(d−1)`, then `V_d ∩ Rad_MF(H) = D(V_d)` and `κ|_(V_d)` is the parity character
   `V_d -> Z/2`.
   - This item uses ABC Cor 7.7 with the canonical vertex-inclusion map `K_1(k) -> K_1(R)` (recalled; artifact §3).
   - Items 1 and 2 do not use it.
4. `⟨[H,H], V_d⟩ = κ^(-1)⟨[−1]⟩`.

**Firewall.** Nothing follows about whether `V_d` itself is MF or sofic. If `V_d` is MF, its MF approximations do not
extend to `H` beyond the parity character.

**Why it matters for the UN program.** Inside the paradoxical unit group, the topological full group, which is the
amenable-or-LEF-flavoured piece of the groupoid, is invisible to every MF quotient except through `K_1`. On the measure
side the same full group is LEF together with the Kazhdan elementary groups
(`lrf-cantor-actions-give-lef-full-and-elementary-groups`).

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part2.md`): PASS. Lemma 2.1 (λ ↦ λI_d) and Lemma 2.2 (block form, the two 2×2 identities, [1 − 2·1_A] = [−1]^m) recomputed. Item 3 rests on the flagged identification K_1(L_k(1,d)) ≅ k^×/(k^×)^(d−1) with [λ] ↦ λ, consistent with tex Cor l.1297.**
