---
rg: 2
id: finite-k-graph-boundary-groupoid-standard-facts
kind: claim
title: Standard facts on groupoids of finite higher rank graphs - Li's boundary groupoid is the Kumjian–Pask path groupoid, products go to products, and aperiodic graphs give effective Cantor groupoids
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**ESTABLISHED** (2026-09-18) by `finite-k-graph-standard-facts-proof` (lane proof, bh-groupoid; not independently reviewed). That proof derives item 1 from Li's own definitions and lemmas, read at source in arXiv:2110.04501 (Definition `def:Omega`, the transformation groupoid, Lemma `lem:infpaths`, Lemma `lem:Omegamax`), and needs only "no sources". Items 2–4 are proved there directly. The original (weaker) hypothesis note follows. Let `Λ` be a finite `k`-graph such
that every vertex receives and emits at least one edge of each colour (no sources and no
sinks in each colour).

1. **Models agree.** Li's boundary groupoid `I_l(Λ) ⋉ ∂Ω` (Spielberg's model for left
   cancellative small categories) is isomorphic to the Kumjian–Pask path groupoid
   `G_Λ = {(x, p - q, y) ∈ Λ^∞ × Z^k × Λ^∞ : σ^p x = σ^q y}`. The compact open sets
   `Z(λ, μ) = {(λz, d(λ) - d(μ), μz)}` form a basis, and the unit space is identified with
   the infinite path space `Λ^∞`.
2. **Products.** For finite `k`- and `l`-graphs `Λ_1`, `Λ_2` of this kind,
   `G_{Λ_1 × Λ_2} ≅ G_{Λ_1} × G_{Λ_2}`.
3. **Topology.** `G_Λ` is a second countable Hausdorff ample groupoid. Every compact open
   subset of `Λ^∞` is a finite disjoint union of cylinders `Z(λ)`. If every vertex has at
   least two edges of some colour, `Λ^∞` has no isolated points, so it is a Cantor set.
4. **Effectiveness.** If `Λ` is aperiodic in the Kumjian–Pask sense, with aperiodic points
   dense in `Λ^∞`, then `G_Λ` is topologically principal, hence essentially principal.

These are recalled from Kumjian–Pask, *Higher rank graph C*-algebras*, New York J. Math. 6
(2000); Spielberg, *Groupoids and C*-algebras for left cancellative small categories*; and
X. Li, arXiv:2110.04501. (Superseded by the proof route above.) They had not been read at source in the lane that wrote this node; the TeX fetched for arXiv:math/9912002 did not contain the expected text. Each is standard, and the
proof of `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple` uses exactly
items 1–4.
