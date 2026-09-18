---
rg: 2
id: robertson-steger-two-graph-groupoids-are-cocycle-rigid
kind: claim
title: Every locally constant real cocycle on the path groupoid of a Robertson-Steger A2 tile 2-graph is cohomologous to a combination of the two degree cocycles
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
  - experiments/nv-conformal-rigidity-2026-09-17/block_h1_pg22_k1.log
  - experiments/nv-conformal-rigidity-2026-09-17/product_control.log
distinct_from:
  two-graph-brick-codings-are-rigid-under-rank-two-h1: that assumes rank-two H^1 of the finite square complex K(Lambda), which is level 0 only; this asks for rank two in the colimit over all block levels, which is the groupoid cohomology of locally constant cocycles.
  robertson-steger-a2-two-graphs-are-primitive-and-aperiodic: that is about primitivity and aperiodicity of the transition matrices; this is a higher-rank cocycle rigidity statement for the groupoid.
---

**OPEN.**

**Setting.** Let `T` be a triangle presentation over `PG(2,q)` satisfying (A1)–(A3). Let
`Λ_T` be its tile 2-graph (`rs2graph.py` rules, as in
`cmsz-pg22-rs-two-graphs-admit-no-brick-coding`). `G_{Λ_T}` is the path groupoid, and `d_1`
and `d_2` are the degree cocycles.

**Claim.**
- (a) Every locally constant cocycle `c : G_{Λ_T} -> R` equals
  `a d_1 + b d_2 + H∘r - H∘s` for some reals `a, b` and some continuous `H` on the unit
  space. Equivalently, the direct limit over `k` of `H^1(K(Λ_T^{[k]}); R)` along the block
  pullbacks is 2-dimensional.
- (b) `Λ_T` has no sources and `ρ(M_1) > 1`. This is expected with constant row sums `q^2`,
  and is checked for `q = 2, 3`.

**Why it matters (decomposition).** With
`spatial-two-graph-realizations-in-g2n-leave-the-degree-plane` (ii), this single statement
implies that `G_{Λ_T}` has no spatial realization in any `G_2^n`, for every `q`. That kills,
for the route `[[Λ_T]] ↪ mV` of `some-brin-thompson-group-has-an-infinite-kazhdan-subgroup`,
three earlier survivors at once:
- (1) block recodings at every level;
- (2) groupoid-level spatial embeddings;
- (4) `q = 2^r`.

What remains are non-spatial abstract embeddings and Kazhdan groups not of Ã₂ type.

**Evidence** (Section 4 of the artifact).
- For the five `PG(2,2)` presentations T0–T4, `dim H^1(K(Λ_T^{[k]})) = 2` at `k = 0, 1`.
- For both `PG(2,3)` presentations it is 2 at `k = 0` (`experiments/nv-brick-coding-2026-09-17/q3_hypotheses.log`).
- The product of two full 4-shifts, which is not rigid, gives `26, 98, 386` at
  `k = 0, 1, 2`.

**How it could fail.**
- The claim fails iff some `H^1(K_k)` has a class outside the degree plane that stays
  nonzero at all higher levels. Such a class would have to appear first at a level
  `k ≥ 2`.

**Kill test / next step.**
- Compute `k = 2` for T0: 10752 vertices and about 86000 edges, beyond the current Python
  elimination in a reasonable time.
- Or prove a transfer lemma: a level-`k` cocycle is cohomologous at level `k+1` to one
  pulled back from level `k-1`, using the unique filling of Ã₂ squares. That would give
  the colimit from `k ≤ 1`.
- A Katok–Spatzier type argument for the `Z^2` shift action on the Ã₂ boundary would give
  it for all `q`.
