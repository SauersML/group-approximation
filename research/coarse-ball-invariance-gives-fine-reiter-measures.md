---
rg: 2
id: coarse-ball-invariance-gives-fine-reiter-measures
kind: claim
title: In any finitely generated group, a probability measure moved by at most 1 in ℓ¹ by every element of the ball of radius 2K yields, after K−1 steps of the lazy random walk, a Reiter measure with error O(1/√K) at a support-radius cost of K−1
distinct_from:
  moore-ramsey-criterion-for-amenability: that imports Towsner's Proposition 3.1, which turns Ramsey sets into Reiter measures by a minimax over |S| functions and composes the Ramsey function; this turns one coarsely invariant measure into a finely invariant one with no Ramsey input and only additive radius overhead.
  thompson-f-norm-bound-from-epg-32-term-moments: that bounds the spectral radius of the Markov operator of F from below by moments; this is a quantitative Kesten-type smoothing statement that holds in every group and says nothing about the norm of F.
---

**ESTABLISHED** by `coarse-ball-invariance-gives-fine-reiter-measures-proof`. It is a short self-contained spectral
argument. It is almost certainly folklore (a quantitative form of Kesten's criterion), and no priority is claimed.

**Setting.** `G` is a group, `S` is a finite generating set, `S' = S ∪ S⁻¹ ∪ {e}` and `B_r` is the ball of radius `r`
in the word metric of `S ∪ S⁻¹`. Measures are finitely supported probability vectors. `(gν)(x) = ν(g⁻¹x)`, and `‖·‖`
is the ℓ¹ norm.

**Lemma.** Let `K ≥ 1` and `r ≥ 0`. Suppose `ν` is supported in `B_r` and `‖gν − ν‖ ≤ 1` for every `g ∈ B_{2K}`.
Then there is a measure `μ` supported in `B_{r+K−1}` with

`‖sμ − μ‖ ≤ 2|S'|·√(2 ln 2 / K)` for every `s ∈ S'`,

and hence `‖gμ − μ‖ ≤ 2|g|·|S'|·√(2 ln 2 / K)` for every `g ∈ G`. Explicitly, `μ = η²/‖η‖₂²` with
`η = P^{K−1}√ν`, where `P = |S'|⁻¹ Σ_{s∈S'} λ_s` is the lazy random-walk operator on `ℓ²(G)`.

**Why it matters.** Precision amplification is free for *measures*. Coarse invariance (error 1) under a ball of
radius `2K` already gives fine invariance (error `≈ K^{−1/2}`) under the generators, and the support radius grows
only additively. So the radius function of coarsely invariant measures,

`CR(M) = min{ r : some ν supported in B_r has ‖gν − ν‖ ≤ 1 for all g ∈ B_M }`,

controls Moore–Towsner's function `F_{G,S}(m, 1/u)` up to an elementary change of argument. This is used in
`thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap` to show that, in F, the open amplification problem
(¬AMP) is not about precision at all. It is about exchanging the quantifiers "for every coloring there is a
measure" and "one measure for every coloring" at the coarse precision 1/2.
