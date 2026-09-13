---
rg: 2
id: depth-monotone-leavitt-stable-finiteness-proof
kind: route
title: Restrict the function representation to stopping-partition spaces and pass to a product modulo sum
target: depth-monotone-leavitt-subalgebras-are-stably-finite
requires: []
artifacts:
  - research/artifacts/depth-monotone-leavitt-firewall-2026-09-12.md
---
Artifact Sections 1 and 2. Passed by `w4-vf-gate` (verdict below).
1. **Faithful representation** (Lemma 1.1). `L_K(1,2)` acts on locally constant functions on `{0,1}^N`, and a
   combination `Σ λ_μ s_μ` is detected on the cylinder of `μ_0 1 0^M 1`.
2. **Invariance** (Lemma 1.2). The functions constant on the weight-`r` stopping partition are invariant under
   `s_μ t_ν` when `ω(μ) <= ω(ν)` and `ω(μ) <= r`.
3. **Embedding** (Theorem 1). Eventual restriction gives an injective unital map into
   `∏_k End(F_k) / ⊕_k End(F_k)`, which is stably finite since each `F_k` is finite-dimensional. The opposite
   side follows by the anti-automorphism `s_i <-> t_i`.
4. **Units** (Corollary 2). Over a finite field, finitely generated unit subgroups embed in `∏_k GL(F_k)`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 30.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
