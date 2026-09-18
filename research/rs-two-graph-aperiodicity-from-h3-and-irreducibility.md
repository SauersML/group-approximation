---
rg: 2
id: rs-two-graph-aperiodicity-from-h3-and-irreducibility
kind: claim
title: A Robertson–Steger 2-graph satisfying (H3) whose two transition matrices are irreducible is aperiodic in the Kumjian–Pask sense
distinct_from:
  robertson-steger-a2-two-graphs-are-primitive-and-aperiodic: that asks for primitivity and aperiodicity of the Ã₂ tile 2-graphs; this proves that aperiodicity follows from (H3) as soon as each colour is irreducible, so only primitivity is left there.
  finite-k-graph-boundary-groupoid-standard-facts: that collects unpinned facts on k-graph groupoids; this is a finite combinatorial statement proved inline from Robertson–Sims' criterion, read at source.
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane proof, bh-groupoid 2026-09-18, inline below; not independently
reviewed; no novelty claimed).

## Statement

Let `A` be a finite alphabet and `M_1, M_2` be `{0,1}`-matrices satisfying Robertson–Steger's
conditions (H0), (H1) and (H3) (arXiv:1302.5593, §1, read at source). Let `Λ` be the
associated 2-graph: `Λ^0 = A` and `Λ^m = W_m` (words of shape `m`), with `r(w) = w(0)`,
`s(w) = w(m)`, and factorization from (H1). Suppose each `M_j` has no zero row, so `Λ` has
no sources. Suppose also that the directed graph with an edge `a -> b` whenever
`M_j(b,a) = 1` is strongly connected, separately for `j = 1` and for `j = 2`.

Then `Λ` satisfies the Kumjian–Pask aperiodicity condition (A).

For the Robertson–Steger 2-graph `Λ_Γ` of a type rotating group acting freely on the vertices
of an Ã₂ building with finitely many orbits:
- (H0), (H1) and (H3) always hold (`robertson-steger-a2-boundary-algebras-are-rank-two-ck`,
  item 1);
- every row sum of `M_j` is `q²` (see `cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive`).

So `Λ_Γ` is aperiodic as soon as `M_1` and `M_2` are irreducible, and in particular as soon as
they are primitive.

## Proof

**Criterion.** Robertson–Sims, *Simplicity of C\*-algebras associated to higher-rank graphs*,
arXiv:math/0602120, Lemma `lem:equiv aperiodicity`, read at source (TeX on MSI). For a
row-finite `k`-graph with no sources, (A) is equivalent to (iv):

> for each vertex `v` and each pair `m ≠ n ∈ N^k` there is a path `λ ∈ vΛ` with
> `d(λ) ≥ m ∨ n` and `λ(m, m + d(λ) − (m∨n)) ≠ λ(n, n + d(λ) − (m∨n))`.

**Words at every large offset.** Let `d_j` be the period of the strongly connected graph of
`M_j`.
- By Perron–Frobenius, for each vertex `b` there is `K` with `M_j^{k d_j}(b,b) > 0` for all
  `k ≥ K`.
- So for every `b` there are closed paths at `b` of degree `(k_1 d_1, 0)` and `(0, k_2 d_2)`,
  for all `k_1, k_2 ≥ K`.
- Their composites are closed paths at `b` of degree `(k_1 d_1, k_2 d_2)`.
- By strong connectivity of colour 1 there is a path from `v` to `b` of some degree `o_0`.
- So for every pair of vertices `v, b` and every `N ∈ N²` there is a path from `v` to `b` of
  some degree `o ≥ N`.

**Verification of (iv).** Fix `v` and `m ≠ n`, and put `p = m − n ≠ 0`.
1. By (H3) there is a word `w` of some shape `q` that is not `p`-periodic. That is, there is
   `l` with `l, l + p ∈ [0,q]` and `w(l) ≠ w(l+p)`.
2. Choose a path `μ` from `v` to `w(0)` of degree `o ≥ m ∨ n`, and put `λ = μw`, of degree
   `o + q`. Put `e = d(λ) − m∨n` and `j = o + l − n`.
3. **j ≥ 0**, since `o ≥ n`.
4. **j ≤ e.** This is equivalent to `l + (m∨n − n) ≤ q`. Since `m∨n − n = max(p, 0)`, the
   left side is `max(l, l+p) ≤ q`.
5. **The two vertices differ.**
   - `λ(n + j) = λ(o + l) = w(l)`.
   - `λ(m + j) = λ(o + l + p) = w(l+p)`.
   - So the paths `λ(m, m+e)` and `λ(n, n+e)` differ at relative position `j`.

This is (iv), so (A) holds. ∎

## Remark

Robertson–Steger's (H3) is a statement about words anywhere in `W`, while (A) asks for
aperiodic paths from every vertex. Irreducibility of each colour is exactly what moves a
non-periodic word to every vertex at every large offset.
