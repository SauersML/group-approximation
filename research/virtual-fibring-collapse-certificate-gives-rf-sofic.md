---
rg: 2
id: virtual-fibring-collapse-certificate-gives-rf-sofic
kind: claim
title: A finite-cover virtual-fibring certificate with collapsing windows makes a two-generator one-relator group virtually free-by-cyclic, residually finite and sofic
distinct_from:
  sl3z-coherence-forces-rfrs-cd2-subgroups-free-by-cyclic: that derives free-by-cyclic structure from coherence and RFRS hypotheses; this is an explicit finite combinatorial certificate on a finite cover of a one-relator presentation complex, checkable by computer.
  finitely-generated-rf-automorphism-mapping-torus-is-rf: that is residual finiteness of automorphism mapping tori; this produces such a mapping torus, of finite index in a one-relator group, from finite data.
artifacts:
  - research/artifacts/or-length16-nonfree-residue-2026-09-16.md
---

Proved through `virtual-fibring-collapse-certificate-proof`.

**Setting.** Let `w` be a word in the letters `a, A = a^{-1}, t, T = t^{-1}` and let
`G = <a, t | w>`. A *collapse certificate of index `k`* for `w` consists of two permutations
`α, τ` of `Q = {0, …, k−1}` and an integer function `c` on `{a, t} × Q`. It must satisfy
(V0)–(V3) below.

- **(V0)** `w` is cyclically reduced, contains a letter from `{a, A}` and one from `{t, T}`, and
  is not a string repetition `u^m` with `m ≥ 2`.
- **(V1)** `Q` carries the right action `i·a = α(i)`, `i·A = α^{-1}(i)`, `i·t = τ(i)`,
  `i·T = τ^{-1}(i)`, extended letter by letter. This action is transitive, and `i·w = i` for
  every `i ∈ Q`.

  Let `X_H` be the 2-complex with vertex set `Q`, an edge `(x, i)` from `i` to `i·x` for each
  `x ∈ {a, t}` and `i ∈ Q`, and one 2-cell `σ_s` for each `s ∈ Q`. The cell `σ_s` is attached
  along the edge path that starts at `s` and reads `w`.

  Along that path, assign heights: start at `0`, add `c(x, i)` when `(x, i)` is traversed
  forwards, and subtract it when it is traversed backwards.
- **(V2)** Every boundary path `∂σ_s` returns to height `0`. For some spanning tree of the
  1-skeleton of `X_H`, the values of `c` on the fundamental loops have gcd `1`.
- **(V3)** Let `S` be the largest height span (maximum minus minimum) of a boundary path `∂σ_s`.
  Then `|c(x, i)| ≤ S` for every edge.

  Let `X̃` be the complex with vertices `(i, y) ∈ Q × Z`, edges `(x, i, y)` from `(i, y)` to
  `(i·x, y + c(x, i))`, and 2-cells `(s, y)` attached along the lift of `∂σ_s` that starts at
  `(s, y)`. For `p ≤ q`, let `X[p, q]` be the full subcomplex on the vertices of height in
  `[p, q]`: a piece belongs to it when all of its vertices have heights in `[p, q]`.

  Then `X[0, S+1]` and `X[−1, S]` each reduce to `X[0, S]` by finite sequences of the following
  moves.
  - *Vertex move:* remove a vertex `v` together with an edge `e`, where `e` is the only edge of
    the current complex at `v`, `e` is not a loop, and no 2-cell of the current complex passes
    through `v`.
  - *Edge move:* remove an edge `e` together with a 2-cell `σ`, where `σ` is the only 2-cell of
    the current complex whose boundary contains `e`, and `e` occurs exactly once in the boundary
    word of `σ`.

**Claim.** If `w` has a collapse certificate of index `k`, then:
1. `H = Stab_G(0)` has index `k` in `G`, and `c` defines a surjection `φ : H → Z`;
2. `X[0, S]` is connected, and `ker φ` is free of rank `n = 1 − χ(X[0, S])`;
3. `H ≅ F_n ⋊ Z`;
4. `G` is residually finite, and hence sofic.

All four conditions are finite and decidable from `(w, α, τ, c)`. The independent checker
`experiments/or-length16-nonfree-residue-2026-09-16/recheck.py` tests exactly (V0)–(V3), with
the moves as stated.

The virtual-fibring strategy itself is not new. Attempt 6 of
`unpeelable-extreme-one-relator-groups-sofic` used it for length 15, citing Lyndon asphericity
and Bieri's theorem without a node. This claim packages the implication, with Kochloukova's
theorem in place of Bieri's, as a named node that the census claims can require.
