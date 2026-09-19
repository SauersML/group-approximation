---
rg: 2
id: a2-seed-rigidity-reduces-to-its-perfect-boundary
kind: claim
title: The Ã2 origin-projection seeds are locally forced, so they are quantum rigid iff their seedless boundary is; that boundary has no isolated points, so it is its own perfect kernel and no Cantor–Bendixson reduction goes further
distinct_from:
  quantum-rigidity-is-decided-on-the-derived-subshift: that is the general theorem (locally forced isolated points never affect rigidity); this checks its hypotheses for the Ã2 seeds and shows that its iterated form stops after one step.
  a2-lattice-phase-seeds-are-quantum-rigid: that is the open rigidity claim for the phase seed; this reduces it, exactly, to rigidity of the perfect SFT ∂Y^(N).
---

**ESTABLISHED** (lane proof, bh-emitter-b, 2026-09-18; elementary given the parents; not reviewed).
Notation: `Y = Y_Γ` or `Y_Γ^(N)` as in `a2-lattices-carry-finite-type-seeds`. `∂Y` is `Y` with `*`
forbidden. It is an SFT and equals `Y ∖ Γ·y_1`.

## Statement

1. **Local forcing.** `y_1` is locally forced with radius 1, in the sense of
   `quantum-rigidity-is-decided-on-the-derived-subshift`.
2. **Reduction.** `Y` is quantum rigid at all large scales iff `∂Y` is (Corollary A there).
3. **No further reduction.** `∂Y` has no isolated points. So `∂Y` is the perfect kernel of `Y`, and
   Corollary B (Cantor–Bendixson) gives nothing beyond item 2.

## Proof

1. **Local forcing.** Take `π = y_1|_(B_1)`, which isolates `y_1` at `1` (Step 2 of the parent).
   - Suppose `k` lies in the forced set `F_j`, and `h` is outward from `k` for the label `y_1(k)`.
   - Every `β ∈ L_1(Y)` that agrees with `y_1` at `k` has the outward-determined value at `k^(-1)h`
     (Step 1 of the parent, which reads only the centre label).
   - So `h ∈ F_(j+1)`.
   - Every vertex lies on a graph geodesic from `1`, whose steps are outward in `y_1`. So the forcing
     closure is `Γ`.
   - The phase seed is the same: phase changes are read off the centre label.
2. **Reduction.** Item 1 and Corollary A of the parent. By (C2), `U = Γ·y_1` and `Y' = ∂Y`.
3. **No isolated points.** Let `η ∈ ∂Y` and `R >= 0`.
   - **Setup.** Step 4 of the parent gives `z` with `B_R(1) ⊆ Out(z)`. Every `y ∈ Y` with
     `y(z) = η(z)` agrees with `η` on `B_R(1)`. We build two distinct seedless such `y`.
   - **Flag label.** Suppose `η(z)` is a flag `(p_0, ℓ_0)`. Fix an apartment `A` containing that
     chamber at `z`. Fix `j, j' >= 1`, and put `o_k = z − kω_1 − jω_2` and `o'_k = z − j'ω_1 − kω_2`.
     Both have the flag as their label at `z`.
     - Take limits `y`, `y'` of `y_(o_k)` and `y_(o'_k)` along subsequences. They are seedless, since
       `o_k -> ∞`, and they carry `η(z)` at `z`.
     - At `s = z − jω_2` we have `σ(o_k, s) = (k, 0)` and `σ(o'_k, s) = (j', k − j)`. So for `k > j`,
       `y(s)` is a wall label and `y'(s)` a flag, and `y ≠ y'`.
   - **Wall label.** Suppose `η(z) = ℓ_0`, with `n = 0`. By thickness, two rays from `z` through
     `ℓ_0` diverge at `ℓ_0`: at least `q² >= 4` vertices of `Lk(ℓ_0)` are opposite the direction
     back to `z`.
     - Let `o_k` and `o'_k` be the vertices at distance `k` on the two rays, and take limits `y`, `y'`.
     - Both carry `ℓ_0` at `z`. Their labels at `ℓ_0` are the two different next vertices, so `y ≠ y'`.
     - The dual wall label is handled in the same way.
   - **Phases.** For `Y_Γ^(N)`, match the phase `(m_0, n_0)` of `η(z)`: take `j ≡ n_0` and `j' ≡ m_0`,
     and let `k` run through `m_0 + NZ` for `o_k` and through `n_0 + NZ` for `o'_k`. For wall labels,
     let `k` run through the progression that fixes the residue.
   - **Conclusion.** One of `y`, `y'` differs from `η` and agrees with it on `B_R(1)`, so `η` is not
     isolated. `∎`

## Consequences

- **What rung 1d is.** Rigidity of the phase seed is exactly rigidity of the perfect SFT
  `∂Y_Γ^(N)`. Its perfect part contains:
  - the phase-coded chamber boundary, whose pieces are rigid via
    `a2-lattice-boundary-skew-shifts-are-quantum-rigid`;
  - the wall strata, which are Cantor families over vertices at infinity (description, not proved).
- **No shortcut (hand remark).** The strata cannot be made scattered by re-labelling. Every seed coding a vertex
  field has limits along wall directions, and those limits vary with the vertex at infinity. The same
  holds for chamber-origin fields, whose labels are always chambers.
- **Remaining.** A relative version of the derived-subshift theorem is needed: pass from the rigid
  closed chamber stratum to `∂Y` across the open wall strata. There, forcing is only fibrewise (along
  outward wall trees) and not pointwise. An alternative is a finitely presented host for
  `G_V × (Γ ⋉ ∂Y^(N))`.

## Lesson for general BH

Every seed decomposes its rigidity problem into a classical, locally forced origin and a perfect
boundary. For higher-rank lattices that boundary is stratified by the Weyl geometry at infinity. The
chamber stratum is the one that finite presentation certifies. The wall strata are rank-one tree
bundles, and a relative derived-subshift theorem with fibrewise forcing is exactly the missing tool.
