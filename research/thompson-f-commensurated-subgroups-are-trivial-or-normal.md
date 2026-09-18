---
rg: 2
id: thompson-f-commensurated-subgroups-are-trivial-or-normal
kind: claim
title: "Every commensurated subgroup of Thompson's group F is trivial or contains F′, so every totally disconnected locally compact group with a dense image of F is discrete or compact-by-abelian"
distinct_from:
  thompson-f-confined-subgroups-fix-finite-sets: that imports Chaudkhari's classification of confined subgroups (between a germ stabilizer and a finite-set stabilizer); this proves that the much smaller class of commensurated subgroups collapses to the normal ones and the trivial one.
  thompson-f-recurrent-f-sets-factor-through-the-abelianization: that proves recurrent Schreier graphs force H ⊇ F′ through a Z³ rough embedding; this proves commensurated H ⊇ F′ through a disjoint-support commutator trick, with no random walk input.
  thompson-f-has-an-amenable-normalish-tail-subgroup: that exhibits an amenable normalish (not commensurated) subgroup; this shows no nontrivial non-normal subgroup of F is commensurated.
  brin-thompson-brick-charts-are-not-commensurated: that concerns particular chart subgroups of nV; this classifies all commensurated subgroups of F.
---

**ESTABLISHED** by `thompson-f-commensurated-subgroups-are-trivial-or-normal-proof` (direct proof from the
imported facts (F1), (F2), (F4) of `thompson-f-rigid-interval-subgroups-facts`; not independently refereed;
very likely folklore for micro-supported groups, no priority claimed).

**Theorem.** Let `H ≤ F` be commensurated: `[H : H ∩ gHg⁻¹] < ∞` for every `g ∈ F`. Then `H = 1` or
`H ⊇ F′` (so `H` is normal).

**Corollary (tdlc hulls).** Let `φ : F → G` be a homomorphism with dense image into a totally disconnected
locally compact group `G`. Then either `G` is discrete and `G = φ(F)` is `F` or an abelian quotient of `F`,
or the closure `N` of `φ(F′)` is a compact normal subgroup with `G/N` abelian, so `G` is amenable.

**Corollary (locally finite graphs).** In every action of `F` by automorphisms of a connected locally finite
graph, either every vertex stabilizer is trivial or `F′` fixes every vertex.

**Why it matters.** It kills, at one invariant, every non-amenability certificate that passes through a Hecke
pair or a Schlichting completion: a commensurated amenable `H` with a non-amenable completion `Ĝ` would give
`F` non-amenable (amenability of `F` is amenability of `H` plus amenability of `Ĝ`). The only commensurated
subgroups are `1` (completion `F` itself, the root) and `H ⊇ F′` (completion compact-by-abelian, and `H`
amenable iff `F` is). See `thompson-f-subgroup-pair-certificates-collapse`.

**Mechanism.** A nontrivial `h ∈ H` has a fundamental interval `I` that all nonzero powers move off itself.
For `f₁, f₂` supported in `I`, commensuration puts `u_i = f_i⁻¹ h^(m_i) f_i h^(−m_i)` in `H` with
`m₁ ≠ m₂`, and `[u₁, u₂] = [f₁⁻¹, f₂⁻¹]`, so `H ⊇ F(I)`. Since `F(I) ≅ F′` is infinite simple, it has no
proper finite-index subgroup, so every conjugate `F(gI)` lies in `H` too, and these generate `F′`.

Proof route: `thompson-f-commensurated-subgroups-are-trivial-or-normal-proof`.
