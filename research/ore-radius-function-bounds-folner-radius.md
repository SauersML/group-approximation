---
rg: 2
id: ore-radius-function-bounds-folner-radius
kind: claim
title: If common multiples in a group-ring domain K[G] have radius controlled by Omega, then a set with |B(k)F| < (1 + ln|B(k)|)|F| lies in the ball of radius tau^((r-1)d)(k), r = H_n n! + 1
distinct_from:
  thompson-f-amenable-iff-group-ring-is-ore: that is Kielak's qualitative equivalence between amenability and the Ore condition; this is a quantitative version of the Ore-to-amenable direction, bounding where an expanding-ratio set lives in terms of the radius of common multiples.
  thompson-f-cardinality-certificates-need-tower-degree: that bounds cardinality certificates (sets that do not double); this bounds arbitrary common multiples found by any method, including linear algebra, which that claim's Scope leaves unconstrained.
  amenable-groups-satisfy-the-garden-of-eden-theorem: that is the Ceccherini-Machi-Scarabotti direction of Myhill's theorem; this localizes Bartholdi's converse construction to finite radius and composes it with Ore elimination.
artifacts:
  - experiments/ore-radius-folner-2026-09-17/check_local_bartholdi.py
---

**ESTABLISHED** through `ore-radius-function-bounds-folner-radius-proof` (direct proof; imports
Bartholdi's Lemma 2.1 verbatim; not independently reviewed; swarm-0917, c-famen).

**Setting.**
- `G` is a group, `S` a finite symmetric subset with `1 ∈ S`, and `B(R) = S^R`.
- `K` is a field such that `K[G]` has no zero divisors.
- For `R >= 0`, the **Ore radius** `Ω(R) = Ω_(K,S)(R) ∈ N ∪ {∞}` is the least `ρ` such that every pair of
  nonzero `a, b ∈ K[B(R)]` has nonzero `t, u ∈ K[B(ρ)]` with `a t = b u`.
- `Ω` is nondecreasing. Put `τ(R) = R + Ω(R)` and write `τ^(p)` for the `p`-fold iterate.
- `H_n = 1 + 1/2 + ... + 1/n`.

**Theorem A.** Assume `Ω(R) < ∞` for all `R`. Let `k >= 1` with `n = |B(k)| >= 3`, and let
`r = H_n n! + 1`. Put `d = 1` if `K` is infinite, and `d = n^2 + ⌈log_2 r⌉ + 1` if `K` is finite. Then
there is a finite nonempty `F ⊆ B(τ^((r-1)d)(k) - k)` with

`|B(k) F| < (1 + ln n) |F|`.

**Remarks.**
- *Converse direction.* If `G` is amenable then `Ω(R) < ∞` for every `R` and every such `K` (Tamari's
  counting). Take a finite `E` with `|B(R)E| < 2|E|`. Then `aK[E]` and `bK[E]` are `|E|`-dimensional
  subspaces of `K[B(R)E]`, so they meet nontrivially, and `Ω(R)` is at most the radius of `E`. So
  Theorem A turns Kielak's qualitative equivalence into a two-sided comparison between `Ω` and the
  Følner function.
- *Why a matrix is needed.* The pair-level statement "the support of a common multiple of `a, b` has
  small doubling with respect to `supp a ∪ supp b`" is false. In `Z^d` take `S = {0, e_1, ..., e_d}`,
  `a = Σ_(s∈S) λ_s X^s` and `b = Σ_(s∈S) μ_s X^s`. Then `t = b`, `u = a` is a common multiple supported
  on `S`, and `|S + S| / |S| = (d+2)/2`, which exceeds `1 + ln(d+1)` for large `d`. Theorem A instead
  eliminates through Bartholdi's `(r-1) × r` matrix, whose width `r` depends only on `n`. The
  elimination depth `(r-1)d` is the price of this, and it is what limits the consequences for `F`
  (`thompson-f-ore-radius-function-is-not-quasi-polynomial`).
- The artifact checks, in exact arithmetic mod `1000003`:
  - Bartholdi's counts `#Y = H_n n!` and `#X_(i,I) = n!/#I` for `n <= 6`;
  - the slack inequality `n!(1 + ln n - H_n) >= 1` for `3 <= n <= 400`;
  - genericity for `n = 3`;
  - kernel supports obeying the ratio bound on `Z`;
  - the absence of kernel vectors on a ball of the free product `C_2 * C_2 * C_2`.
