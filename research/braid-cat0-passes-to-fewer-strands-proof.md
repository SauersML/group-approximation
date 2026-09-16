---
rg: 2
id: braid-cat0-passes-to-fewer-strands-proof
kind: route
title: The centralizer of the n-strand full twist in B_{n+1} is B_n × Z, and CAT(0) passes to centralizers and to quotients by central infinite cyclic subgroups
target: braid-cat0-passes-to-fewer-strands
requires: []
artifacts:
  - research/artifacts/braid-cat0-fewer-strands-2026-09-16.md
---

The complete proof is §§1–5 of the artifact. This body records its structure.

**Standard inputs (not re-proved).**
- Bridson–Haefliger (1999):
  - II.2.2, convexity of the metric;
  - II.6.8, `Min(z) = Y × R` for a hyperbolic `z`, with every commuting isometry
    acting as `(α', translation)`;
  - I.3.7, Hopf–Rinow–Cohn-Vossen.
- The Fadell–Neuwirth fibration: the kernel of forgetting the last strand of a
  pure braid is free.
- Nielsen–Schreier.

Everything else is proved in the artifact.

**Step 1 (geometric actions; artifact §1).** Let `G` act geometrically on a
complete CAT(0) space `X`.
- `X` is proper.
- `F_S = {g : gS ∩ S ≠ ∅}` is finite for every compact `S`.
- Every `γ ∈ G` has `Min(γ)` nonempty, closed and convex. Nonemptiness comes from
  a finiteness argument on conjugates `g⁻¹γg` that move a point of a fundamental
  compact set by a bounded amount.
- If `γ` has infinite order, then `|γ| > 0`, since a fixed point would put all
  powers of `γ` in a finite `F_{{x}}`.

**Step 2 (centralizers; §2).** `C_G(γ)` acts geometrically on `Min(γ)`.
- Properness restricts.
- Cocompactness: if `x = gk ∈ Min(γ)` with `k ∈ K`, then `g⁻¹γg` moves `k` by
  `|γ|`, so it lies in a finite set `{h_1, …, h_m}`. Fix `g_i` with
  `g_i⁻¹γg_i = h_i`. Then `g ∈ C_G(γ)g_i`, and `Min(γ) ⊆ C_G(γ)·⋃_i g_iK`.

**Step 3 (central infinite cyclic subgroups; §3).** Let `z` be central of
infinite order.
- `G` acts geometrically on `Min(z) = Y × R`, where `z` acts as `(id, +|z|)` and
  every `g ∈ G` acts as `(g', τ_{s(g)})`.
- `G/⟨z⟩` acts on the complete CAT(0) space `Y`. It acts cocompactly, by
  projecting a compact fundamental set.
- It acts properly: if `g'` moves a point of `B(y, 1)` into `B(y, 1)`, then for
  a suitable `m`, `gz^m` moves a point of `B̄((y, 0), 1 + |z|)` into that ball.
  So `gz^m` lies in a finite `F_S`.
- If `C_G(γ) = H × ⟨z⟩`, then `H ≅ C_G(γ)/⟨z⟩` is CAT(0).

**Step 4 (the braid centralizer; §4).** Braids are loops in configuration spaces.
- `ι : B_n → B_{n+1}` adds a straight last strand.
- `f` forgets the last strand on braids fixing it, and `f∘ι = id`.
- `Δ²_m` is the rigid `2π` rotation, central by a torus homotopy.
- `lk_{ij}` are winding numbers of pure braids, and conjugation by `β` permutes
  them by `σ_β`.

For `n ≥ 2` let `γ = ι(Δ²_n)`, `z = Δ²_{n+1}` and `β ∈ C(γ)`.
1. The total winding `tot_k(γ)` is `n − 1 > 0` for `k ≤ n` and `0` for
   `k = n+1`. So `σ_β` fixes `n + 1`.
2. `w = β·ι(f(β))⁻¹` lies in the free group `ker f` and commutes with
   `δ = γ⁻¹z ∈ ker f`.
3. `lk_{1,n+1}(δ) = 1`, so `δ` is not a proper power and `w = δ^k`.
4. Hence `β ∈ ⟨z⟩·ι(B_n)`.

Winding numbers also show `⟨z⟩ ∩ ι(B_n) = 1` and that `z` has infinite order. So
`C_{B_{n+1}}(γ) = ι(B_n) × ⟨Δ²_{n+1}⟩`.

**Step 5 (§5).** For `n = 1`, `B_1` is trivial. For `n ≥ 2`, apply Step 2 to
`γ = ι(Δ²_n)` in `B_{n+1}`, then Step 3 with `H = ι(B_n) ≅ B_n` and
`z = Δ²_{n+1}`. ∎
