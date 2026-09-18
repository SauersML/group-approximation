---
rg: 2
id: finite-k-graph-full-groups-have-exponential-word-problem
kind: claim
title: Finitely generated subgroups of topological full groups of aperiodic finite higher rank graphs have single-exponential word problem, so no such host class, in any rank, is a universal Boone–Higman container
distinct_from:
  input-encoded-sft-groupoid-hosts-are-not-universal: that is rank one (one-sided shifts of finite type), where it also excludes infinite Kazhdan groups; this covers every rank k, where the Kazhdan exclusion is false (rank-two-prefix-replacement-groups-contain-infinite-kazhdan, a2-group-embeds-in-full-group-of-its-rs-two-graph), so complexity is the only obstruction left for these hosts.
  sft-topological-full-groups-have-exponential-word-problem: that is the rank-one word-problem bound; this is the same bound for finite k-graphs of every rank, which contain nV and the F_infinity hosts of Li.
  complexity-bounded-host-classes-are-not-universal: that is the general principle; this supplies the uniform bound for the whole class of finite k-graph hosts.
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (lane proof, bh-groupoid 2026-09-18, inline below; not independently
reviewed; no novelty claimed).

## Setting

- `Λ` is a finite `k`-graph (any `k ≥ 1`) with no sources, and aperiodic in the
  Kumjian–Pask sense (A): every vertex `v` has an infinite path `z ∈ vΛ^∞` with
  `σ^a z = σ^b z` only for `a = b`.
- Kumjian–Pask conventions: `r(λ)`, `s(λ)`, and `Z(λ) = {λz : r(z) = s(λ)}`.
- `[[Λ]]` is the group of homeomorphisms `g` of `Λ^∞` given by a finite table of pairs
  `(μ_j -> λ_j)` with `s(μ_j) = s(λ_j)`, such that the `Z(μ_j)` partition `Λ^∞`, the
  `Z(λ_j)` partition `Λ^∞`, and `g(μ_j z) = λ_j z`.
  - For a finite `k`-graph with no sources, every compact open global bisection of the
    path groupoid `G_Λ` is a finite disjoint union of basic sets `Z(λ, μ)`. So `[[Λ]]`
    is the topological full group `[[G_Λ]]`.
  - Reductions `[[G_Λ|_Y]]` to clopen sets embed in it, by extending with the identity.

## Statement

1. **Word problem.** Every finitely generated `S ≤ [[Λ]]` has, for any finite generating
   set, a word-problem algorithm running in time `C_S · 2^{C_S l}` on words of length `l`.
2. **Non-universality.** By `complexity-bounded-host-classes-are-not-universal` with
   `T(l) = 2^l`, some two-generated group with solvable word problem embeds in no
   `[[Λ]]`, for any `k` and any aperiodic finite `k`-graph `Λ` without sources.

**What item 2 covers.**
- Brin's `nV`, which is the full group of a product of full shifts.
- Higman–Thompson and Matui's SFT full groups (rank one).
- Li's `F_∞` full groups of finite `k`-graphs with two loops of each colour at every
  vertex (`li-finite-k-graph-full-groups-are-f-infinity`).
- The hosts `[[G_{Λ^(n) × B_2}]]` of `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple`.

## Proof of 1

**Lemma (identity detection).** Let `α, α'` be finite paths with `s(α) = s(α') = v`, and
suppose `αz = α'z` for all `z ∈ vΛ^∞`. Then `α = α'`.

- By (A), pick an aperiodic `z ∈ vΛ^∞`, and put `x = αz = α'z`. Then
  `σ^{d(α)}x = z = σ^{d(α')}x`.
- `x` is aperiodic. If `σ^a x = σ^b x`, apply `σ^{d(α)}`: then `σ^a z = σ^b z`, so
  `a = b`.
- Hence `d(α) = d(α')`, and `α = x(0, d(α)) = α'`. ∎

**Algorithm.**
- **Normalize the tables.** Refine each generator's table and its inverse's by the
  factorization property: replace `(μ -> λ)` by all `(μν -> λν)`, `ν ∈ s(μ)Λ^{c𝟙 − d(μ)}`.
  Afterwards every domain rectangle has degree exactly `c𝟙`, for one constant `c`.
- **Track one cylinder.** Let `w = x_1⋯x_l`. For each `α ∈ Λ^{cl𝟙}`, apply the letters
  from the right to a current path `β`, starting from `β = α`.
  - Factor `β = μν` with `d(μ) = c𝟙`. This is unique, and it applies because
    `d(β) ≥ c𝟙` throughout: each letter lowers every coordinate of the degree by at most
    `c`.
  - Replace `μ` by its table image `λ`.
  - The output `α_w` satisfies `w(αz) = α_w z` for all `z`.
- **Decide.** `w = 1` iff `α_w = α` for every `α`.
  - "If" is clear.
  - "Only if" is the Lemma applied on each cylinder `Z(α)`, since the cylinders of degree
    `cl𝟙` partition `Λ^∞` (no sources).

**Cost.** There are at most `|Λ^0|·E^{k c l}` paths `α`, where `E` bounds the number of
edges of each colour at a vertex. Each run costs `l` factorizations of paths of degree at
most `O(l)`. Such a path is stored by `O(kl)` edges along a monotone lattice path, and is
refactored with the finitely many commuting squares of `Λ` in polynomial time. The total
is `C_S · 2^{C_S l}`. ∎

## Consequence for the groupoid route to Boone–Higman

Finite `k`-graph hosts, including Li's finitely presented ones, can only carry inputs
whose word problem is at most single-exponential with some constant.
- A universal groupoid host must therefore take its complexity from the input.
- The natural way is a coefficient group: a self-similar action of a finitely presented
  group `G` on a finite `k`-graph (Li, arXiv:2110.04505, Example `ex:ZS` case (III)).
- Even then, the image of `G` in the full group is residually finite. `G` permutes each
  finite set `Λ^n` of paths of degree `n`, and it acts faithfully on their union
  whenever it acts faithfully on `Λ^∞`.
- So non-residually-finite inputs must be produced by mixing `G` with coefficient-free
  cylinder exchanges.
- See `research/artifacts/gq-bh-bh-groupoid-frontier.md`.

## Scope

- Aperiodicity is used only for identity detection. Without it, item 1 still holds for the
  table-equality relation, but that relation may be finer than equality of homeomorphisms.
- Nothing is claimed about coefficient groups `G ≠ 1`.
