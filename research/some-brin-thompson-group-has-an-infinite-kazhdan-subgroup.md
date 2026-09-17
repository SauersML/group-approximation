---
rg: 2
id: some-brin-thompson-group-has-an-infinite-kazhdan-subgroup
kind: claim
title: Some Brin-Thompson group nV contains an infinite subgroup with property (T)
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asserts that every Kazhdan subgroup of every nV is finite; this is its negation.
  some-hyperbolic-group-does-not-embed-in-thompson-v: that excludes infinite Kazhdan groups from V = 1V; this asks for one inside some nV with n at least 2.
---

There is `n ≥ 2` and an infinite group `K ≤ nV` with property (T). Then kV
contains `K` for every `k ≥ n`. By Farley's theorem this is impossible for
n = 1.

## What it would give

- kV fails the Haagerup property for every k ≥ n. That is a negative answer to
  the Haagerup half of Zaremsky Problem 2.7.
- It refutes `kazhdan-subgroups-of-brin-thompson-groups-are-finite`.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv): route
  `infinite-kazhdan-subgroup-of-nv-from-hyperbolic-embeddings` reduces this
  claim to the affirmative answer of Zaremsky 2.19(a). A yes to 2.19(c) would
  also give it, through SL_3(Z).
- 2026-09-13, same lane: no candidate is known.
  - The natural Kazhdan groups acting on Cantor sets are boundary actions of
    hyperbolic Kazhdan groups and actions of lattices on p-adic flag varieties.
    Both have local maps with nontrivial states, not prefix replacements.
  - The topological full group of the two-sided full shift sits in 2V through
    the baker's map, but has no infinite Kazhdan subgroup, because its orbits
    are copies of Z.
- 2026-09-17 (lane swarm-0917-w4-nv-rel-t): the Ã₂ route, and where its natural
  version dies. Artifact: `research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md`.
  - **Decomposition.** A CMSZ group `Γ_T` has (T). The route is (P2) `Γ_T ↪ [[Λ_T]]`, the
    node `a2-group-embeds-in-full-group-of-its-rs-two-graph`, followed by (P3)
    `[[Λ_T]] ↪ mV`.
  - **Tool (ESTABLISHED).** `brick-coded-two-graph-full-groups-embed-in-brin-thompson`
    reduces (P3) to a brick coding of the 2-graph: edge codes that are brick partitions
    and commute on squares.
  - **Obstruction (ESTABLISHED).** `two-graph-brick-codings-are-rigid-under-rank-two-h1`.
    - Invariant: `H^1` of the tile square complex, together with the Perron eigenvalue
      `q^2`.
    - Kraft plus Perron–Frobenius forces `q^2 = 2^α`, and transport and separation force
      `m ≤ α`.
    - So every brick coding dies at Step B1 when `q` is not a power of 2, provided
      `dim H^1 = 2`.
  - **Computation (ESTABLISHED, SAT-based).**
    `cmsz-pg22-rs-two-graphs-admit-no-brick-coding`.
    - For five explicit presentations over `PG(2,2)`, `dim H^1 = 2`, both colours are
      primitive and each colour has one transport class.
    - The forced instance (dimension 2, length 2) is UNSAT with two solvers.
    - So those `Λ_T` have no brick coding in any dimension.
  - **q = 3 (ESTABLISHED, no SAT).** `cmsz-pg23-rs-two-graphs-admit-no-brick-coding`.
    - Two presentations over `PG(2,3)`: row sums 9, primitive with exponent 4.
    - The Gram rank is 2651 mod p, so `dim H^1 = 2`.
    - Kraft/Perron would force `9 = 2^α`, so there is no brick coding in any dimension.
  - **Still open.**
    1. Block recodings `Λ^{[k]}`, where the question is whether `dim H^1` stays 2.
    2. Groupoid-level spatial embeddings. These would be killed for `q` not a power of 2
       if every continuous real cocycle on `G_{Λ_T}` is cohomologous to a multiple of the
       degree cocycle: the Radon–Nikodym cocycle of pulled-back Lebesgue measure must be
       integral at the fixed point of a cycle rectangle of degree `(r,s) ≠ 0`, while
       Perron forces it to be `(r+s) log_2 q^2`.
    3. Non-spatial embeddings.
    4. `q = 2^r` with `r ≥ 2`.
    5. Kazhdan groups not of Ã₂ type.
- 2026-09-17 (lane swarm-0917-w5-z-nv-kazhdan-subgroups): brick codings die at connected
  corners, for every `q`. Artifact:
  `research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md`.
  - **Invariant.** The corner compatibility graph `B_1(a)`. It joins a colour-1 and a
    colour-2 edge at `a` when they begin a common square.
  - **Theorem (proof written; route requires only ESTABLISHED rigidity (b)).**
    `two-graph-brick-codings-die-at-connected-corners`: (R1)–(R3) plus connected `B_1(a)`
    at every vertex exclude brick codings in every dimension. Every coding dies at one
    step:
    - (B2) makes corner codes comparable;
    - connectivity then gives one first letter per coordinate at each vertex, which
      contradicts (B1);
    - so each vertex has an edge with empty code, giving a zero-length cycle against
      `α_j, β_j > 0`.
  - **Geometry (proof written, self-contained).**
    `triangle-presentation-tile-two-graphs-have-affine-corner-graphs`.
    - For every triangle presentation over every `PG(2,q)`, `B_1(a)` is the incidence graph
      of `PG(2,q) \ λ(u)` minus the parallel class of `w`, hence connected.
    - The proof uses (A1)–(A3) and unique filling only.
  - **Corollary.** `rank-two-h1-tile-two-graphs-admit-no-brick-coding`.
    - For all `q` (including `q = 2^r`), (H1) + irreducibility + `dim H^1 = 2` + one
      transport class per colour gives no brick coding.
    - New SAT-free route `cmsz-pg22-no-brick-coding-by-corners` for the `PG(2,2)` claim.
  - **Computations** (`experiments/nv-kazhdan-independence-2026-09-17/`).
    - Only a `1/q` fraction of corner pairs complete (`corners.py`), so "every corner
      completes" is false.
    - Compatible `(k,0)/(0,k)` pairs have exactly `q^k` completions (`completions.py`).
    - `B_k(a)` is connected for `k ≤ 2` at the tested vertices (`compat_graph.py`).
  - **Still open after this entry.**
    - (a) Survivor 4 above is now reduced to (R2)/(R3) for `q = 2^r` presentations (none
      computed).
    - (b) Survivor 1, block recodings, needs (C1) for `Λ^{[k]}`, that is, connectivity of
      `B_k(a)` for all `k` (computed only for `k ≤ 2`), and (R2)/(R3) for `Λ^{[k]}`.
    - (c) Survivors 2, 3 and 5 are untouched. Any surviving embedding of `[[Λ_T]]` into
      `mV` must send some cylinder to a non-brick.
