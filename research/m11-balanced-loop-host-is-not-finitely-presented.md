---
rg: 2
id: m11-balanced-loop-host-is-not-finitely-presented
kind: claim
title: The balanced-loop host R° = <M_11, b, C> is not finitely presented, and neither is its simple Tits host; relations of a finitely presented self-similar group have stable sections in a finite section-closed set, for R° that set is made of pure powers b^55j, alpha^55j, beta^55j, and the relations (sigma^k(alpha))^11 keep the fixed section omega_alpha^11, which is nontrivial in Z/55 * Z/55
artifacts:
  - experiments/m11-balanced-loop-host-not-fp-2026-09-18/nonfp_checks.py
  - experiments/m11-balanced-loop-host-not-fp-2026-09-18/nonfp_checks.out
distinct_from:
  m11-balanced-loop-host-has-exact-finite-l-presentation: that gives the finite L-presentation and reduces finite presentation of R° to the inclusion sigma(Q_0) in <<Q_0>>; this decides the question negatively, refutes that inclusion with an explicit level-3 certificate, and its main proof does not use the level shift.
  m11-odometer-free-host-is-not-finitely-presented: that kills R'' through its ray-loop subgroup, which contains a contracting branch group; for R° the loop subgroups are C_55, Z and 1, so the loop obstruction is silent, and this uses a stable-relator argument instead.
  self-wreathing-groups-are-not-fp-infinity: that obstruction needs H_1 or H_2 of the local group to be nonzero and is blind here, since M_11 is superperfect; this argument is not homological.
  fp-self-similar-groups-have-fp-ray-loop-subgroups: that constrains FP self-similar groups through loop subgroups at periodic rays; this constrains them through the stable part of the section closure of a finite relator set, which sees a relation family whose sections along 1^infinity never shrink.
---

**ESTABLISHED (unreviewed).** Proof: `m11-balanced-loop-host-is-not-finitely-presented-proof`.
The proof is by hand. The script computes the explicit C-free words for `α@1`, `β@1`, `b@1`,
checks them exactly in `R°`, and computes `ω_α` and its normal form. It also runs the
level-3 certificate on the sibling L-presentation.

**Setting.** As in `m11-balanced-loop-host-has-exact-finite-l-presentation`. Right actions on
`X = {1, …, 11}`.
- `α = (1, …, 11)` and `β = (1,2,3,4,8)(5,10,7,11,6)`, with `⟨α, β⟩ = M_11`.
- `b = (b, α, β, 1, …, 1)` has order 55, and `C = (1, 1, 1, C, bα, C^{-1}, 1, …, 1)` has
  infinite order.
- `F` is free on `S = {α, β, b, C}`, and `K = ker(F → R°)`. The section map `w ↦ w|_x` on
  free words is letterwise, followed by free reduction. The *weight* of a word counts its
  letters `b^{±1}, C^{±1}`.
- `W_α, W_β, W_b` are explicit C-free words (lengths 152, 164, 315) representing
  `α@1, β@1, b@1`. Their free sections at 1 are
  `ω_α = α^{-2}β^{-1}αβ^{-1}α^{-1}βαβαβ^{-1}α^{-1}β^{-1}αβ²`, `ω_β` (length 20) and `b`.
  All other sections of `W_α` and `W_β` are empty.

**Theorem.**

1. **Stable relators (any self-similar group).** Let `G` be a self-similar group on a finite
   generating set `S` whose letter sections are words over `S`, such that the section
   closure of every finite set of words is finite. (For `R°` this holds because sections
   never increase the weight, and a section has length at most twice its weight.) Let
   `R ⊆ K` be finite with section closure `Q`, and let `Q^(k)` be the set of nonempty
   level-`k` sections of words of `Q`. Then `Q^(k+1) ⊆ Q^(k)`, so the chain stabilizes at
   some level `k_0` to a set `Q^∞`. For every `w ∈ ⟨⟨R⟩⟩` and every vertex `v` with
   `|v| ≥ k_0`, the free word `w|_v` lies in `⟨⟨Q^∞⟩⟩_F`.
2. **Stable part for `R°`.** For every finite section-closed `Q ⊆ K`, the stable part
   satisfies `Q^∞ ⊆ {b^{55j}, α^{55j}, β^{55j} : j ≠ 0}`. For the set `Q_0` of the
   L-presentation it equals `{b^55, α^55, β^55}`, reached at level 3.
3. **A relation family with a fixed section.** Let `σ` be the endomorphism
   `α ↦ W_α, β ↦ W_β, b ↦ W_b` (and `C ↦ W_C`). Then `σ^k(α)` represents `α@1^k`, and as a
   free word `σ^k(α)|_{1^k} = ω_α` for every `k ≥ 1`. So
   `w_k = σ^k(α)^{11} ∈ K` has section `w_k|_{1^k} = ω_α^{11}`.
4. **`R°` is not finitely presented.** Let `χ : F → A = Z/55 * Z/55` send `α, β` to the
   generators and `b, C ↦ 1`. Then `χ` kills `b^{55j}, α^{55j}, β^{55j}`. But
   `χ(ω_α)` is cyclically reduced of syllable length 14, so `χ(ω_α^{11}) ≠ 1`. By items 1–3,
   `K` is not the normal closure of any finite set.
5. **Tits host.** `Γ⁺ = (R° ≀ M_12) *_{R°×R°} (R° ≀ M_12)` is a finitely generated simple group
   that is **not finitely presented** (`tits-hosts-for-transitive-local-actions`).
6. **The explicit inclusion fails.** `σ(R2(C)) ∉ ⟨⟨Q_0⟩⟩`. The witness is the map
   `φ_3 : F → A ≀ Aut(X^3)` given by level-3 sections followed by `χ`. It kills `Q_0` but
   not `σ(R2(C))`, which has six χ-nontrivial level-3 sections below vertex 1. The same holds
   for a finite quotient: compose with `A → S_5`, `α ↦ (12345)`, `β ↦ (12453)`.
   So the epimorphism `θ : G_0 ↠ G_0 ≀ M_11` is not injective, and the chain `K_n` of the
   L-presentation is strictly increasing. This agrees with item 4 through Theorem C of the
   sibling node.

**What this says about the Tits route of `boone-higman-conjecture`.**
- `R°` passed every screen on the graph: `H_1(R°) = Z/55`, the loop subgroups are finite or
  cyclic, it is not contracting, and it has an exact finite L-presentation. It still fails.
- The mechanism is the same one that made the L-presentation exact. Weight-preserving
  section paths end in pure powers, so stable relators are pure powers. But `ι_1` embeds
  `⟨M_11, b⟩` along `1^∞` with the nontrivial "twist" `α ↦ ω_α`. This twist is invisible to
  relators that are pure powers, and it survives forever along the ray.
- **Design rule.** Suppose that in a candidate every weight-preserving letter section is a
  single state letter, and no two state letters keep their weight at a common point (here
  `b` only at 1, `C` only at 4 and 6). Then the proof of item 2 applies: stable relators are
  pure powers and their descendants. Such a candidate is not finitely presented as soon as
  one relation family has a non-shrinking section along a ray that survives modulo these
  powers, as `ω_α^{11}` does here. So a finitely presented candidate needs a stable relator
  that is not a pure power. That means a relation on a weight-preserving section cycle that
  mixes state letters, or state letters with root permutations.
