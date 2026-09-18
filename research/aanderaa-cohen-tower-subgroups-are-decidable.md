---
rg: 2
id: aanderaa-cohen-tower-subgroups-are-decidable
kind: claim
title: In the Aanderaa–Cohen Higman tower K ≤ K_M ≤ H_1 ≤ H_2 ≤ H_3 of a group C with solvable word problem (and a machine M with decidable H_0(M)), every associated subgroup of every HNN rung has decidable membership in its base, and the machine subgroup T'_M has membership Turing-equivalent to H_0(M); so the consumption condition for relative seeds holds on every rung, CAP is decided at the rung (K_M, T'_M), and gluing alone carries seeds to the input only through C x F_n
requires:
  - aanderaa-cohen-tower-subgroups-are-decidable-proof
  - relative-seeds-glue-graphs-of-groups-into-class-c
distinct_from:
  relative-seeds-glue-graphs-of-groups-into-class-c: that glues rigid relative seeds along graphs of groups and puts K_M in class C; this checks, rung by rung, the necessary condition (decidable membership, its item 3) for the relative seeds the Aanderaa–Cohen tower needs above K_M, and locates where gluing stops.
  relative-seeds-descend-to-quotients-and-consume-membership: that shows towers over subgroups containing normal subgroups only relocate the problem; this treats the core-free machine tower.
---

**ESTABLISHED** by `aanderaa-cohen-tower-subgroups-are-decidable-proof` (lane
bh-free-56, 2026-09-18; elementary lane proof, not reviewed; no priority claimed).
- The construction is read from Chiodo–Vyas, arXiv:1604.03788 v3, §§3–4 (PDF read 2026-09-18). They
  follow D. E. Cohen, *Combinatorial Group Theory: a Topological Approach*, pp. 266–268 and 279–281, and
  Aanderaa–Cohen (1980).
- The fact that a machine with decidable `H_0(M)` exists for decidable `C`, as in Clapham's theorem, is
  recalled, not re-read. Below it is a hypothesis.

## The tower (Chiodo–Vyas §4.1–4.2, their notation)

- **The base.** `K = ⟨x, y, t | [x, y]⟩ = Z² * Z`, with `t(r, s) = y^{-s} x^{-r} t x^r y^s`. Then
  `K = T ⋊ Z²`, where `T` is free on the `t(r, s)`.
  - `K^{M,N}_{a,b} = ⟨t(a,b), x^M, y^N⟩`.
  - For a modular machine `M` with modulus `m`, the maps `φ_i : K^{m,m}_{a_i,b_i} → K^{m²,1}_{c_i,0}`
    (quadruples R) and `ϕ_j : K^{m,m}_{a_j,b_j} → K^{1,m²}_{0,c_j}` (quadruples L) realize the moves on
    the indices of `t`.
- **Rung 1.** `K_M = K *_{φ_i, ϕ_j}`, with stable letters `r_i, l_j`.
  - `T'_M = ⟨t, r_i, l_j⟩`.
  - `t(α, β) ∈ T'_M` iff `(α, β) ∈ H_0(M)`, the set of configurations whose run halts at `(0, 0)`.
  - The machine group is `G_M = K_M *_{T'_M}`.
- **Rung 2.** `H_1 = K_M * (C × F(b_1, …, b_n)) * ⟨d⟩`.
- **Rung 3.** `H_2 = H_1 *_ψ`, with stable letter `p`, where `ψ : P = ⟨t_α : α ∈ I⟩ → P' = ⟨t_α w_α(b) d⟩`
  and `t_α = t(α, 0)`.
- **Rung 4.** `H_3 = H_2 *_{ψ_1, …, ψ_{2n}, ψ_+}`, with stable letters `a_i, k`, over:
  - `A = ⟨t, x, d, b, p⟩ → A_i = ⟨t_i, x^m, b_i d, b, p⟩`;
  - `A_+ = ⟨U, d, b, p⟩ → A_- = ⟨U, d, b_j c_j, p⟩`, where `U = {t, r_i, l_j}`.
- **The result.** `H_3` is finitely presented and `C ↪ H_3`.

## Statement

Let `C = ⟨c_1, …, c_n | S⟩` have solvable word problem, and let `M` be as above with `H_0(M)` decidable.

1. **Rung 1.** Membership in `K^{M,N}_{a,b}` inside `K` is decidable, with no hypothesis. So `K_M` has
   solvable word problem.
2. **The machine subgroup.** Membership in `T'_M` inside `K_M` is Turing-equivalent to `H_0(M)`.
   - `H_0(M) ≤` membership, via `t(α, β)`.
   - Membership `≤ H_0(M)`, by a good-subgroup algorithm.
   - So `WP(G_M) ≡_T H_0(M)`.
3. **Rung 3.** Membership in `P` and in `P'` inside `H_1` is decidable. Only `P'` uses `WP(C)`.
4. **Rung 4.** Membership in each of `A, A_1, …, A_{2n}, A_+, A_-` inside `H_2` is decidable, using
   `WP(C)` and `H_0(M)`.
5. **Consequence.** Every rung has solvable word problem, by Britton's lemma. This recovers Clapham's
   conclusion for this tower.

## Seeds up the tower (the CAP rung and where gluing stops)

- **Consumption is never violated.** By item 3 of `relative-seeds-glue-graphs-of-groups-into-class-c`,
  a relative seed for an associated subgroup needs decidable membership. Items 1–4 show this necessary
  condition holds at every rung whenever `WP(C)` and `H_0(M)` are decidable.
  - In particular it holds for the machine rung `(K_M, T'_M)` iff `H_0(M)` is decidable.
- **CAP is decided at one rung.** `K_M ∈ 𝒞` (`relative-seeds-glue-graphs-of-groups-into-class-c`, (c)).
  - If `(K_M, T'_M) ∈ 𝓡`, gluing along the one-vertex graph gives `G_M ∈ 𝒞`, with `WP(G_M) ≡_T H_0(M)`.
  - Decidable `H_0(M)` can have arbitrarily high complexity. So rigid relative seeds for `(K_M, T'_M)`
    over such machines would make CAP false.
  - The input group `C` plays no role in this rung.
- **Gluing alone does not reach the input.**
  - `H_1` is a free product with the factor `C × F_n`. Gluing over its trivial edges needs
    `(C × F_n, 1) ∈ 𝓡`, that is, `C × F_n ∈ 𝒞`.
  - `H_2` and `H_3` are one-vertex HNN extensions over `H_1` and `H_2`. Gluing puts them in `𝒞` only if
    the vertex group is in `𝒞`.
  - So, through this tower, gluing proves (★𝒞) for `C` only from a seed on `C × F_n`. The relative
    seeds of rungs 3–4 are necessary but not sufficient.
  - This is the "irreducible geometry" gate (SYNTHESIS v6, gate 2). The tower forces it for every
    input, not only for inputs with (FA).

## Lesson for general BH

The Aanderaa–Cohen tower separates the two halves of the seed problem.
- **Complexity** enters at exactly one rung, the machine subgroup `T'_M ≤ K_M`.
  - That rung is core-free, needs only decidable `H_0(M)`, and does not involve the input.
  - So CAP is precisely the question whether rigid relative seeds exist for `(K_M, T'_M)` over machines
    of large complexity.
- **Geometry** enters at the free factor `C × F_n` of `H_1`. No relative seed on the tower's associated
  subgroups can supply it, because gluing needs a seed on every vertex group that is left along a
  trivial edge.
- **Consumption is never the obstruction.** Every associated subgroup is decidable exactly when the
  input and the machine are.
  - So the tower can fail to carry seeds only through the existence or rigidity of the seeds themselves.
  - It cannot fail through decidability.
