---
rg: 2
id: smart-level-zero-return-map-has-free-divergence
kind: claim
title: SMART's level-0 return map has free divergence at every point, so neither it nor any finite skew-product decoration factors onto the ternary valuation Toeplitz subshift
requires:
  - smart-level-zero-return-map-factors-onto-3-adic-odometer
distinct_from:
  smart-renormalization-admits-no-graded-basins: that rules out gradings of SMART's one landed renormalization and its decorations, and records openness of the odometer factor at the holes as a heuristic; this proves that openness (free divergence) at every point and so rules out every factor map onto T_3, whatever renormalization or coding is used.
  graded-renormalization-gives-ternary-toeplitz-factor: that proves Lemma A (a factor onto T_3 forces non-open odometer phases at the holes); this shows SMART's induced map violates the finer, level-sensitive form of that necessity everywhere.
  smart-level-zero-return-map-factors-onto-3-adic-odometer: that constructs the phase map π; this analyses how π varies near each point.
---

**ESTABLISHED** (lane proof below, bh-free-50, 2026-09-18, by hand; not independently reviewed; no
priority claimed).

Inputs:
- the moves and recursions of Callard–Salo, arXiv:2208.00685v3, `prop:smart-moves` and its proof (TeX
  `distortion-1-smart.tex`, read in `$GQ/src/callard-salo/`);
- the canonical-chain facts and π of `smart-level-zero-return-map-factors-onto-3-adic-odometer` (refereed
  PASS);
- minimality of SMART's moving-tape map (imported from COT through Callard–Salo §1, as in the nodes
  above). It is used only in item 3, to make odometer phases unique up to a constant.

## Setting

- `F` is SMART on `Q × {0,1,2}^Z`. `Y` is the clopen set of level-0 configurations, `U = F_Y` its
  first-return map, and `π : Y → Z/2 × Z_3` the phase.
- Every `y ∈ Y` lies in a canonical chain of genuine moves `M_{x_k}(k)`, `k ≥ 0`. The level-`k` move has
  type `x_k ∈ {b,d,p,q}` and end cells `s_+(k) ∈ {1,2}`, `s_*(k) ∈ {0,1,2}`. Its domain has `k+2` cells
  and contains the head.
- `i_k ∈ {0,1,2}` is the index of `M_{x_k}(k)` in its parent. Then
  `π(y) = pos_0 + Σ_k i_k·2·3^k`, so the Z_3-component of `π(y) − π(y')` has 3-adic valuation `m` whenever
  `pos_0` agrees, `i_k = i'_k` for `k < m`, and `i_m ≠ i'_m`.
- Write `v(y, y') = v_3(π_3(y) − π_3(y'))`.
- `O_0`, `O_1` are the Z-orbits of `(0,0)` and `(1,0)` in `Z/2 × Z_3`. They are exactly the phases whose
  digits `(i_k)` are eventually constant: eventually `0` or `2` give `O_0`, eventually `1` gives `O_1`.

## Statement

1. **Free divergence.** For every `y ∈ Y` and every `D`, there is `K` such that for every `m ≥ K`
   there is `y' ∈ Y` that agrees with `y` on the `D`-neighbourhood of the head, has the same `pos_0`, and
   has `v(y, y') = m`. In particular, near every point, phases diverging at levels of every residue class
   mod every `r` occur.
2. **Openness off two orbits.** `π` is open at every `y` with `π(y) ∉ O_0 ∪ O_1`.
3. **No level-sensitive holes.** Fix `c ∈ Z/2 × Z_3`, `r ≥ 2`, `L : Z/r → A` and `N`. Let `λ : Y → A` be
   continuous with `λ(y') = L(v_3(π_3(y') − c_3) mod r)` for all `y'` in a neighbourhood of `π^{-1}(c)` that
   have the Z/2-coordinate of `c` and satisfy `N ≤ v_3(π_3(y') − c_3) < ∞`. Then `L` is constant.
   The same holds on `Ỹ = Y × K` for every finite skew product `Ũ(y,κ) = (Uy, τ(y)κ)` with `τ` locally
   constant.
4. **Consequences for the Toeplitz route.**
   - `(Y, U)` has no factor onto the ternary valuation Toeplitz subshift `T_3` of
     `graded-renormalization-gives-ternary-toeplitz-factor`, and no finite skew product of it has one either.
   - The same holds for the Schreier subshift of Nekrashevych's ternary fragmentation (Attempt 1 of
     `brin-thompson-groups-contain-infinite-periodic-groups`), whose hole labels are the annulus index
     `v_3 mod 3`.
   - Every almost 1-1 subshift extension of `Z/2 × Z_3` that is a factor of `(Y, U)` has all its
     non-singleton fibres over `O_0 ∪ O_1` (translated). By item 3, none of its hole letters is a
     non-constant function of the divergence level mod `r`.

## Proof

**Step 1: the parent rule.** This is read off the two recursion displays in the proof of `prop:smart-moves`.
- In `M_b(k+1)` on `(P_+ 0^k 0 P_*)`, the sub-moves are:
  - `M_b(k)` with `(s_+, s_*) = (P_+, 0)`;
  - `M_d(k)` with `(s_*, s_+) = (P_+, 1)`;
  - `M_p(k)` with `(s_*, s_+) = (P_+, 1)`.
- In `M_p(k+1)` on `(P_* 0 0^k P_+)`, the sub-moves are:
  - `M_b(k)` with `(s_+, s_*) = (2, P_+)`;
  - `M_q(k)` with `(s_+, s_*) = (2, P_+)`;
  - `M_p(k)` with `(s_*, s_+) = (0, P_+)`.
- `d` and `q` are mirror images. The parent's `P_*` is the one new cell. It lies right of the sub-domain
  for `b`- and `q`-parents and left of it for `d`- and `p`-parents.

So a level-`k` move `(x, s_+, s_*)` has the following parent (type, index, `P_+`):

| `x` | `s_* = 0` | `s_* ≠ 0`, `s_+ = 1` | `s_* ≠ 0`, `s_+ = 2` |
|---|---|---|---|
| `b` | `(b, 0, s_+)` | `(d, 1, s_*)` | `(p, 0, s_*)` |
| `d` | `(d, 0, s_+)` | `(b, 1, s_*)` | `(q, 0, s_*)` |
| `p` | `(p, 2, s_+)` | `(b, 2, s_*)` | `(q, 1, s_*)` |
| `q` | `(q, 2, s_+)` | `(d, 2, s_*)` | `(p, 1, s_*)` |

The types and indices agree with the refereed table of the odometer artifact. Two facts follow:
- `x_k` and `s_+(k)` are functions of the level-`(k−1)` domain.
- `s_*(k)` is the new cell, outside that domain. Its content is arbitrary, since every tape is a
  configuration and the table is exhaustive.

**Step 2: the digit automaton.** Group states by family (`bd` or `pq`) and by `s_+`:
- `A = (bd, 1)`, `B = (bd, 2)`, `C = (pq, 1)`, `D = (pq, 2)`.
- The input at level `k` is `s_*(k)`. Each transition below is written `input → next state / digit i_k`.

| state | `0` | `1` | `2` |
|---|---|---|---|
| `A` | `A / 0` | `A / 1` | `B / 1` |
| `B` | `B / 0` | `C / 0` | `D / 0` |
| `C` | `C / 2` | `A / 2` | `B / 2` |
| `D` | `D / 2` | `C / 1` | `D / 1` |

Digit sets: `A` gives `{0,1}`, `B` gives `{0}`, `C` gives `{2}` and `D` gives `{1,2}`.

**Step 3: one-sided chains are eventually pure.** The new cell at level `k+1` lies on the side fixed by
`x_{k+1}`: right for `b` and `q`, left for `d` and `p`.
- Staying inside `{b, q}` (or inside `{d, p}`) forces `s_* = 0` at each level, so the type is eventually
  constant and the digits are eventually `0` (type `b` or `d`) or eventually `2` (type `p` or `q`).
- So either both ends of the level-`k` domain go to infinity ("balanced"), or the chain is eventually pure
  and `π(y) ∈ O_0`.

**Step 4: a reachable-set invariant.**
- For a state `s` at level `k` and a digit string `c_k c_{k+1} …` produced by some path from `s`, let
  `R_m` be the set of states reachable at level `m` along paths that produce `c_k … c_{m−1}`.
- *Claim:* `R_m ∩ {A, D} ≠ ∅` for all `m ≥ k+1`.
  - `{B}` goes to `{B,C,D}` under digit `0`. `{C}` goes to `{A,B,C}` under digit `2`.
  - The property is preserved from then on:
    - if `A ∈ R` and `c ∈ {0,1}`, then `A → A`;
    - if `D ∈ R` and `c ∈ {1,2}`, then `D → D`;
    - if `A ∈ R`, `D ∉ R` and `c = 2`, the path's own state is `C`, and `C → A`;
    - if `D ∈ R`, `A ∉ R` and `c = 0`, the path's own state is `B`, and `B → D`.
- *Claim:* `R_m` stays a proper subset forever only if `c_{≥k}` is `0^∞`, `0^a 1^∞`, `2^∞` or `2^a 1^∞`.
  Otherwise it becomes `{A,B,C,D}`, which every digit maps to itself.
  - The recurrent proper sets are `{A}` and `{B,C,D}` under `0`, `{A,B}` and `{C,D}` under `1`, and
    `{A,B,C}` and `{D}` under `2`.
  - `{A,B}` under `0`, `{C,D}` under `2`, `{A,B,C}` under `0` and `{B,C,D}` under `2` all go to the full set.

**Step 5: free divergence.**
- *(a) Balanced `y`.* Choose `k` with the level-`(k−1)` domain containing the `D`-neighbourhood. Every
  `y'` that agrees with `y` there has the same chain below level `k`, and its later new cells lie outside
  that domain and are free.
  - By Step 4 some state in `R_m ∩ {A, D}` has a digit different from `c_m`, for every `m ≥ k+1`.
  - Realise that path up to level `m`, take a different digit at `m`, and keep `y`'s cells elsewhere. That
    gives `v(y, y') = m`.
- *(b) Eventually pure `y`.* Change only the far cell `s_*(k)` to `1`.
  - From `A` or `D` this changes the digit at level `k` (`A`: `0 → 1`; `D`: `2 → 1`).
  - From `B` or `C` the digit at `k` is unchanged, and the new state is `C` (from `B`) or `A` (from `C`).
    Its whole digit set avoids `c_{k+1}`, whatever the next (possibly nearby, fixed) cell is. So the phase
    diverges exactly at `k+1`.
  - Hence `v(y, y') ∈ {k, k+1}`, fixed by the eventually constant state, for every large `k`. The changed
    cell is at distance `→ ∞`.
- In both cases, cells `0, ±1` and `pos_0` are unchanged, so `y' ∈ Y`.

**Step 6: openness.** If `π(y) ∉ O_0 ∪ O_1`, then `y` is balanced (Step 3) and `R_m` becomes full at some
`M` (Step 4). So the image under `π` of every small neighbourhood of `y` contains every phase with `y`'s
`pos_0` and digits `< M`. That is a neighbourhood of `π(y)`.

**Step 7: item 3.**
- Take `y ∈ π^{-1}(c)` (π is onto) and, for each `j ∈ Z/r`, points `y_n^{(j)} → y` from item 1 with
  divergence levels `≡ j mod r` and `→ ∞`. Continuity gives `λ(y) = L(j)` for every `j`.
- *Skew products.* `Ỹ` splits into finitely many clopen minimal sets. On each, an invariant continuous map
  to `Z_3` is constant, so every odometer phase of `Ũ` has the form `π_3 ∘ pr + const` there. For
  `(y, κ)` in such a set, `(y_n^{(j)}, κ)` lies in the same set for large `n`, and the argument repeats.

**Step 8: item 4.**
- For a factor `J : Y → T_3` with odometer map `p`, `p ∘ J − π_3` is continuous and invariant. It is
  constant by minimality of `U` (induced from the minimal `F`) or, for `Ũ`, on each minimal clopen set.
- `J(·)(0)` is continuous and equals `v_3(p∘J) mod 3` off the hole. Item 3 with `L = id` gives a
  contradiction.
- The same holds for the fragmentation Schreier subshift. Its ψ-coordinates of
  `graded-renormalization-gives-ternary-toeplitz-factor` are affine with unit slope in `Z_3`, so the annulus
  index is `v_3(π_3 − c) mod 3`.
- The location of the non-singleton fibres follows from item 2 by the two-neighbourhood argument of Lemma A:
  where `π` is open, a fibre has one point.

## Reading

- SMART's hierarchy gains one free cell per level, and at every level some choice of that cell moves the
  divergence point. So the depth of a hole is never visible at bounded range. This is a property of every
  configuration, not of one renormalization.
- A witness for `some-nv-element-has-a-graded-height-3-renormalization` must therefore come from a machine
  whose fresh cells are not free at the holes. Its hierarchy has to be rigid enough that the local window
  near an infinitely deep point fixes the depth class mod 3.

## Lesson for general BH

- **A periodic group inside a Thompson-type host needs depth that is visible nearby.**
  - Grigorchuk- and Nekrashevych-type groups need the hierarchy level at a hole to be readable within
    bounded range.
  - A host can supply this in two ways:
    - elements of unbounded reach, like the self-similar tails of Röver–Nekrashevych groups, which are
      the known finitely presented simple hosts of periodic groups;
    - bounded-reach elements whose dynamics is *graded-rigid*: the odometer phase is non-open at the
      holes, and the level class is fixed by a bounded window.
- **`nV` has neither built in.** The machines that give `nV` its universality (SMART, which puts whole
  minimal full groups into `2V`) have one free fresh cell per level. By this node, that freedom makes the
  phase open off two orbits, which is exactly what destroys grading.
- **Consequence.** Universality through robust simulation and periodicity through graded holes pull
  against each other in `nV`. A Burnside-type host for general BH must engineer graded rigidity; it will
  not come from simulation. The testable invariant is openness of the eigenfunction phase of one element.
