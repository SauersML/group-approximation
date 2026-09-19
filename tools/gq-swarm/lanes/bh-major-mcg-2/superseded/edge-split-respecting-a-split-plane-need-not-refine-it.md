---
rg: 2
id: edge-split-respecting-a-split-plane-need-not-refine-it
kind: claim
title: A ten-piece edge-split dissection of the triangle cone respects the plane of a first split but does not refine that split in the edge-split operad
invalidates:
  - edge-split-dissections-respecting-an-atom-plane-split-there
artifacts:
  - research/artifacts/gq-bh-major-mcg-2-ldatom-counterexample.md
distinct_from:
  edge-split-dissections-respecting-an-atom-plane-split-there: that claims every edge-split dissection respecting a first-split plane refines that split in the operad order (LD_atom); this is a counterexample with ten pieces, beyond the seven-piece exhaustive check recorded there.
  edge-split-descendants-are-not-factor-closed: that shows a single descendant cell can lie in a child without descending from it; this shows that a whole edge-split dissection whose pieces all lie on one side of each child can still fail to be edge-split in the child.
  edge-split-operad-has-common-refinements: that is Ore's condition (OPEN); this refutes one route to it, and for its own pair exhibits a common refinement, so Ore's condition is not refuted.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). It is an explicit finite
counterexample, checked by hand and by exact integer arithmetic (script and output in
the artifact; one MSI process, under a second). No priority claimed.

## Statement

Notation of `edge-split-operad-satisfies-ore`, with `m = 2` and
`Δ = cone(e_0, e_1, e_2)`.
- **Setting.** `E_{01}` splits `Δ` at `v_{01} = e_0 + e_1` into the halves
  `H_1 = cone(e_0, v_{01}, e_2) = {x_1 ≤ x_0}` and
  `H_2 = cone(v_{01}, e_1, e_2) = {x_0 ≤ x_1}`.
- **The dissection.** There is a `D ∈ 𝒪_E(Δ)` with ten pieces such that:
  1. every piece of `D` lies in `H_1` or in `H_2`;
  2. the restriction of `D` to `H_1` is **not** an edge-split dissection of `H_1`.
- **Consequences.**
  - `D` refines `E_{01}` geometrically, but `D ≱_E E_{01}`. So LD_atom
    (`edge-split-dissections-respecting-an-atom-plane-split-there`) is false.
  - The stronger LD_gen recorded there is false too: `H_1` is a node that is a union of
    pieces of `D`.
  - On `𝒪_E`-dissections, the operad order `≥_E` does not coincide with geometric
    refinement.

## The dissection

Put `v_{02} = (1,0,1)`, `u = (2,0,1)`, `w = (2,1,1)`, `z = (2,2,1)`, `c = (1,1,1)`.
`D` is built by the following split tree. Each step splits one cell at the sum of
two of its rays.
1. **Δ at the edge `(e_0, e_2)`**, giving `K = cone(e_0, e_1, v_{02})` and
   `K' = cone(v_{02}, e_1, e_2)`.
2. **`K'` at `(v_{02}, e_1)`**, giving `P_7 = cone(v_{02}, c, e_2)` and
   `P_8 = cone(c, e_1, e_2)`.
3. **`K` at its far edge `(e_0, v_{02})`**, giving `K_a = cone(e_0, e_1, u)` and
   `K_b = cone(u, e_1, v_{02})`.
4. **`K_a`.**
   - Split at `(e_1, u)`: `cone(e_0, e_1, w)` and `P_1 = cone(e_0, w, u)`.
   - Then `cone(e_0, e_1, w)` at `(e_1, w)`: `cone(e_0, e_1, z)` and
     `P_2 = cone(e_0, z, w)`.
   - Then `cone(e_0, e_1, z)` at `(e_0, e_1)`: `N_A = cone(v_{01}, e_1, z)` and
     `P_3 = cone(e_0, v_{01}, z)`.
5. **`K_b`.**
   - Split at `(u, e_1)`: `cone(w, e_1, v_{02})` and `P_4 = cone(u, w, v_{02})`.
   - Then `cone(w, e_1, v_{02})` at `(w, e_1)`: `cone(z, e_1, v_{02})` and
     `P_5 = cone(w, z, v_{02})`.
   - Then `cone(z, e_1, v_{02})` at `(e_1, v_{02})`: `N_B = cone(z, e_1, c)` and
     `P_6 = cone(z, c, v_{02})`.

So `D = {P_1, …, P_8, N_A, N_B}`. Each piece is unimodular, and the weights
`1/∏(coordinate sums)` add up to `1`.

## Proof

**1. `D` respects `x_0 = x_1`.**
- Values of `ℓ = x_0 − x_1` on the rays:
  `e_0: 1`, `e_1: −1`, `e_2: 0`, `v_{01}: 0`, `v_{02}: 1`, `u: 2`, `w: 1`, `z: 0`, `c: 0`.
- `ℓ ≥ 0` on every ray of `P_1, …, P_7`, and `ℓ ≤ 0` on every ray of `N_A`, `N_B` and
  `P_8`.
- So `D|_{H_1} = {P_1, …, P_7}` and `D|_{H_2} = {N_A, N_B, P_8}`.
- `D|_{H_2}` is edge-split: split `H_2` at `(v_{01}, e_2)` (midpoint `c`), then
  `cone(v_{01}, e_1, c)` at `(v_{01}, c)` (midpoint `z`).

**2. `D|_{H_1}` is not edge-split.** An edge-split dissection of `H_1` other than `H_1`
itself respects one of the three first splits of `H_1`. Each of them is straddled by a
piece:

| first split of `H_1` | its plane | a straddling piece and its values |
|---|---|---|
| edge `(e_0, e_2)`, point `v_{02}` | `x_0 − x_1 − x_2 = 0` | `P_2 = (e_0, z, w)`: `1, −1, 0` |
| edge `(v_{01}, e_2)`, point `c` | `x_1 − x_2 = 0` | `P_5 = (w, z, v_{02})`: `0, 1, −1` |
| edge `(e_0, v_{01})`, point `(2,1,0)` | `x_0 − 2x_1 = 0` | `P_2 = (e_0, z, w)`: `1, −2, 0` |

**3. Ore's condition is not refuted for this pair.**
- Split `P_2` and `P_3` once more, each at its edge `(e_0, z)` (midpoint `(3,2,1)`).
  The result `D^*` has 12 pieces and `D^* ≥_E D`.
- `D^*|_{H_1}` is edge-split. The split points, in order:
  - `H_1` at `v_{02}`;
  - `cone(e_0, v_{01}, v_{02})` at `w`, then at `u` and at `(3,2,1)`;
  - `cone(v_{02}, v_{01}, e_2)` at `c`;
  - `cone(v_{02}, v_{01}, c)` at `z`;
  - `cone(v_{02}, v_{01}, z)` at `w`;
  - `cone(w, v_{01}, z)` at `(3,2,1)`.
- So `D^* ≥_E D` and `D^* ≥_E E_{01}`. All of this is re-checked by the script.

## How it was found

- **The open sub-case.** The partial proof of LD_atom leaves open one sub-case: the
  far-edge first split, where the medial line becomes a unit-corner line `(1, −1, 2)`
  in `K_a` and `(2, −1, 1)` in `K_b`.
- **The negative side is automatic.** The negative side of a unit-corner line
  `(α, −1, γ)` is a unimodular descendant `N`. The far-edge split of the cell
  restricts to an edge split of `N`. So `D|_N` causes no trouble; here `N_A ∪ N_B` is
  the corner of the medial line, split at its edge.
- **The positive side is where it fails.** The minimal resolutions of `(α, −1, γ)` are
  indexed by interleavings of `α` splits at `(a_0, a_1)` with `γ` splits at
  `(a_1, a_2)`. Take the word `tts` in `K_a` and `sst` in `K_b`. The resulting
  positive pieces do not fit any first split of `H_1`.
- **Size.** The whole dissection has ten pieces, beyond the seven-piece exhaustive
  check.

## What survives, and the corrected reduction

- `edge-split-ore-via-atom-plane-restriction` is dead: its input is false.
  `edge-split-operad-has-common-refinements` (Ore) stays OPEN.
- **Ore is equivalent to WLD.**
  `edge-split-ore-via-first-split-refinements` reduces it to
  `edge-split-dissections-refine-into-any-first-split`: every edge-split dissection
  has an edge-split refinement that refines any prescribed first split. Part 3 is an
  instance.

## Lesson for general BH

- **Rearrangement is the wrong form of confluence.** For non-LCM dissection operads,
  "a dissection that respects a generator's cut can be rearranged to make that cut
  first" is false, even when every local diamond closes.
  - The obstruction lives on the side of the cut away from the corner: pieces made
    by one resolution order do not fit the other.
  - It disappears after refining, here by two extra splits.
- **The right statement.** Confluence up to refinement (WLD). That is Ore's
  condition itself, not a local lemma that implies it.
- **A calibration warning.** The exhaustive check was complete to seven pieces. The
  first failure needs the far-edge recursion twice, which costs ten. Small-window
  exhaustive evidence for operad-order statements is weak when the recursion that
  generates hard cases grows the piece count.
