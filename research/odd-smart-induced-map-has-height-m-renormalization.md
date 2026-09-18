---
rg: 2
id: odd-smart-induced-map-has-height-m-renormalization
kind: claim
title: For every odd m >= 3, SMART_m induced on its level-zero moves is an element of 2V with a brick-local height-m renormalization
requires:
  - odd-smart-machines-have-exact-m-fold-moves
  - brin-thompson-first-return-maps-lie-in-kv
distinct_from:
  smart-induced-map-has-brick-local-height-3-renormalization: that is the case m = 3 for SMART; this is the same construction for the machine SMART_m of every odd m, with the extra cell taking r = (m-1)/2 values of each kind.
  smart-induced-on-genuine-moves-has-exact-tripling: that proves the bounded return and the exact count 3^k for SMART; this proves bounded return and the exact count m^k for SMART_m.
  renormalizable-thompson-elements-give-baumslag-solitar: that turns a height-m renormalization into BS(1,m); this supplies one for every odd m.
---

**ESTABLISHED** (lane bh-free-18, lane proof, not reviewed). It follows the refereed `m = 3` proof
(`research/artifacts/gq-gq-nv-obstruct-smart-renormalization.md`, §1–§3) step by step, with the move
proposition, nesting and parent table of `odd-smart-machines-have-exact-m-fold-moves` in place of
Callard--Salo's Proposition 3.2. No numerical check was run (no local compute); an MSI whole-tape
check of `φ U^m = U φ` at `m = 5` would be the natural validation.

## Setting

`F` is the moving-tape map of `SMART_m` on `X = Γ^Z × Q` (head at the origin). With a complete binary
prefix code for `Q × Γ` (8m words) on the right half-tape and one for `Γ` (m words) on both half-tapes,
`F` is a brick map of `C^2`, so `F ∈ 2V`, exactly as for SMART
(`three-v-contains-aperiodic-rationals-proof`, item 1).

`Y ⊆ X` is the clopen set of **starts of genuine level-0 moves**: `b_2` or `d_2` on a nonzero cell; `p_2`
with nonzero right neighbour; `q_2` with nonzero left neighbour.

## 1. Bounded return and the exact count

- `F` alternates phases: a phase-2 state moves into a phase-1 state, and a phase-1 state matches into a
  phase-2 state.
- The phase-2 configurations outside `Y` reach `Y` quickly.
  - `b_2` on `0` moves right onto a cell `c`. If `c = 0`, `b_1` writes `x_1` and gives `d_2` on `x_1`, which
    is in `Y` (2 steps). If `c ≠ 0`, `b_1` keeps it and gives `q_2`, whose left neighbour is the `0`; `q_2`
    moves back and `q_1` on `0` writes `y_1` and gives `d_2` on `y_1`, which is in `Y` (4 steps).
  - `p_2` with right neighbour `0` moves onto it, and `p_1` writes `y_1`, giving `b_2` on `y_1` (2 steps).
  - `d_2` and `q_2` are mirrors.
- So every configuration enters `Y` within 5 steps and the return time satisfies `r_Y <= 6`, the same
  bounds as for SMART. By `brin-thompson-first-return-maps-lie-in-kv`, `U := F_Y` is conjugate by a
  brick-local map to an element of `2V`.
- **Exact count.** Inside a move, the phase-2 junction steps are not in `Y`: the last step of `M_b(k+1)` is
  `b_2` on the reset cell `e = 0`, and the first step of `M_p(k+1)` is `p_2` whose right neighbour is
  `e = 0` (mirrors for `d`, `q`). Every genuine level-0 move starts in `Y`. So `M_t(k)` contains exactly
  `m^k` points of `Y`, consecutive in `U`-time.

## 2. Canonical chains

Every `y ∈ Y` starts a level-0 move of type `t` with boundary `(σ_+, σ_*)` read off radius 1. The parent
table of `odd-smart-machines-have-exact-m-fold-moves` gives its parent move and the index `i_0(y)`. The
parent's boundary is again read off the tape (its `s_+` is `σ_*` if `σ_* ≠ 0`, else `σ_+`; its `s_*` is the
cell beyond the extra cell), so the chain continues at every level, with indices `i_0(y), i_1(y), …`.
Each `i_j` is locally constant. Uniqueness of parents gives `i_0(Uy) = i_0(y) + 1 mod m`.

## 3. The renormalization

`A := {y ∈ Y : i_0(y) = 0}` is clopen, `Y = A ⊔ UA ⊔ … ⊔ U^{m-1}A` and `U^m A = A`.

| level-1 move | its first `Y`-point | first `Y`-point of `M_t(0)` | `φ` |
|---|---|---|---|
| `M_b(1)` on `s_+ 0 s_*` | `b_2` on `s_+` | `b_2` on `s_+` in `s_+ s_*` | delete the `0` right of the head |
| `M_d(1)` on `s_* 0 s_+` | `d_2` on `s_+` | `d_2` on `s_+` in `s_* s_+` | delete the `0` left of the head |
| `M_p(1)` on `s_* 0 s_+` | `b_2` on `y_1` in `s_* y_1 s_+` | `p_2` on `s_*` in `s_* s_+` | delete the head cell, head one left, state `p_2` |
| `M_q(1)` on `s_+ 0 s_*` | `d_2` on `y_1` in `s_+ y_1 s_*` | `q_2` on `s_*` in `s_+ s_*` | delete the head cell, head one right, state `q_2` |

- **Rows are local.** A `b_2`-point of `A` has right neighbour `0` (row `b`) or has head letter `y_1` and
  nonzero right neighbour (row `p`). The other `b_2`-points of `Y` (`b_2` on `x_j`, or on `y_j` with `j >= 2`,
  with nonzero right neighbour) have `i_0 ≠ 0`. `d_2` is the mirror.
- **Brick-local.** Each edit deletes a cell next to the head or the head cell, and changes the head
  state: finitely many prefix replacements in the two coordinates, as in the `m = 3` case.
- **Bijective onto `Y`.** The inverse inserts `0` beside the head, or inserts `y_1` under a new head `b_2`
  (resp. `d_2`). Its image lies in `A` by the parent table: `(b, (s_+, 0))` is index 0 of a `b` parent, and
  `(b, (y_1, s_+))` with `s_+ ≠ 0` is index 0 of a `p` parent.

**Lemma (one level less, one cell less).** For `K >= 1`, let `C1_K(t, s_+, s_*, ρ)` be the content of
`M_t(K)` at the first `Y`-point of its `ρ`-th level-1 sub-move and `C0_{K-1}(t, s_+, s_*, ρ)` the content of
`M_t(K-1)` at the start of its `ρ`-th level-0 sub-move (`ρ` in base `m`). Then `φ(C1_K) = C0_{K-1}`.

*Proof.* `K = 1` is the table. For `K+1`, the domain of `M_t(K+1)` is a sub-domain plus one cell (the
parent's `s_*`, which no sub-move touches), and the `i`-th sub-move is `M_{σ(t)_i}(K)` with boundary
values `β(t, i, s_+, s_*)` from the nesting table. Neither the side of that cell nor `β` depends on `K`. So
`C1_{K+1}(t, …, (i, ρ'))` and `C0_K(t, …, (i, ρ'))` are that cell next to `C1_K(σ(t)_i, β, ρ')` and
`C0_{K-1}(σ(t)_i, β, ρ')`, and the induction hypothesis applies inside the sub-domain. ∎

**The identity `φ U^m = U φ` on `A`.**
1. If `y` and `U^m y` lie in one finite-level move, the lemma gives `φ(y)` and `φ(U^m y)` as consecutive
   level-0 starts of `M_t(K-1)`, with the tape outside the domain unchanged, so `U φ(y) = φ(U^m y)`.
2. This fails only if every ancestor of `y`'s level-1 move is a last sub-move. Last sub-moves are `p` (of `b`
   or `p`) and `q` (of `d` or `q`), and `b`, `d` are never last, so the chain is all `p` (or all `q`). In an
   all-`p` chain each ancestor sits in a `p` parent, so has `s_* = 0` and shares the right end cell `v ≠ 0`,
   and the tape left of the domains is all `0`. Rewrite one far-left cell to a nonzero letter `w`. The
   ancestor whose `s_*` it is then has `σ_* = w ≠ 0`, so its parent is a `b` parent (if `v = x_j`) or a `q`
   parent (if `v = y_j`); in both cases either the sub-move is not last, or its parent `b` is not last. The
   perturbation keeps any given window, so points of case 1 are dense in `A`. The all-`q` case is the
   mirror.
3. Both sides are continuous, so they agree on `A`.

**Conclusion.** Transported by the brick-local conjugacy of §1, `(A, φ)` is a height-`m` renormalization
of an element `U' ∈ 2V` in the sense of items 1–3 of `renormalizable-thompson-elements-give-baumslag-solitar`.
`U'` has infinite order (automatic from items 1–2).
