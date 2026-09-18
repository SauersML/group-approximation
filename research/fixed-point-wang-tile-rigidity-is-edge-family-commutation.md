---
rg: 2
id: fixed-point-wang-tile-rigidity-is-edge-family-commutation
kind: claim
title: A self-similar Wang tile set with a side-local simulation is quantum rigid iff it is 1-rigid iff every face-local edge family commutes; so its rigidity is a scale-zero contextuality question, and edge-disconnected differences kill it at every scale
distinct_from:
  self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale: that substitutes D-families and gets the check scale D_0 = 3 for zoom >= 4; this substitutes families that commute only inside single tiles, needs the side-local layout of fixed-point tile sets, and gets scale 1 and an exact scale-free reformulation.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that uses walls of width 2D; here a difference set that is disconnected along differing edges, with no width at all, already kills a side-local self-similar tile set at every scale.
  path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is: that transfers rigidity between groups along folds; this transfers it between levels of one hierarchy, down to single tiles.
---

**ESTABLISHED (2026-09-18)** through `fixed-point-wang-tile-rigidity-is-edge-family-commutation-proof`.
Lane proof (bh-g2-fixedpoint-a), elementary, not independently reviewed. No priority is claimed; a bounded
search of main found no edge-family formulation.

## Setting

- `τ ⊆ C^4` is a Wang tile set (a tile is its four colours `(l, r, b, t)`), **trimmed**: every tile occurs in
  some tiling. `Ω_τ ⊆ τ^(Z^2)` is its tiling shift (`r = 1`). Quantum families and `D`-rigidity are as in
  `sft-crossed-product-fp-iff-quantum-rigid` (conditions (Q1)–(Q3), `ℓ¹` metric).
- `S : τ → τ^([0,N)^2)` is a **self-simulation** in the sense of Durand–Romashchenko–Shen
  (arXiv:0910.2415, §2.1, read at source): injective, `t, t'` match iff `S(t), S(t')` match, and every tiling
  splits uniquely into blocks from the range of `S`.
- `S` is **side-local with margin `m >= 1`** if, for every `t` and every position `q`:
  - if `q` lies within distance `< m` of exactly one side, `S(t)_q` depends only on that side's colour of `t`;
  - if `q` lies within distance `< m` of two sides (a *corner*), `S(t)_q` does not depend on `t`.
- A **face-local edge family (FLEF)** on a `k`-space `W` puts a partition of unity into orthogonal
  idempotents `(P_c(e))_(c ∈ C)` on every edge `e` of the square grid, such that:
  - (F1) the four edges of each face pairwise commute;
  - (F2) `P_l(left) P_r(right) P_b(bottom) P_t(top) = 0` at each face for every `(l, r, b, t) ∉ τ`.
  Nothing is required of two edges that share no face, even adjacent ones.

## Theorem

1. **Families are edge families.** Every `D`-family of `Ω_τ` with `D >= 1` gives an FLEF by taking colour
   marginals, and the FLEF commutes iff the family does.
2. **Edge families substitute up.** `S^k` is side-local with margin `m N^(k−1)`. If `2D < m N^(k−1)`, every
   FLEF `P` yields a `D`-family `E_a(z) = Σ_{t : S^k(t)_(z − N^k Z) = a} F_t(Z)`, with `Z = ⌊z / N^k⌋` and
   `F_t = P_l P_r P_b P_t`. It commutes iff `P` does.
3. **Scale zero.** The following are equivalent:
   - `τ` is quantum rigid (`D`-rigid for some `D`);
   - `τ` is `1`-rigid;
   - every FLEF of `τ` commutes;
   - `LC(Ω_τ, k) ⋊ Z^2` is finitely presented.
4. **Edge walls.** Suppose tilings `x ≠ x'` exist whose difference set `{z : x(z) ≠ x'(z)}` is disconnected
   for the relation "adjacent, with differing colours on the shared edge". Then some FLEF on `k^2` does not
   commute. So `τ` is not quantum rigid at any scale, and its crossed product is not finitely presented.

**Examples.** The fixed-point tile sets of DRS §2.2–2.3 are side-local, with margin a fixed fraction of `N`
for the layout of their Fig. 3:
- border colours are 0 except the `k` middle bits of each side;
- wires run from the sides to a central computation zone.

DRS fix the wiring "in any reasonable way", so margin `>= 1` is a mild design requirement.

Their tiles are colour quadruples by definition. Item 3 therefore improves the scale-collapse bound
`D_0 = 3` of `self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale` to `D_0 = 1` for these sets.
Zoom `N = 2` (for example, Ollinger's 104-tile set, recalled from DRS) is never side-local, since every
position would be a corner and `S` could not be injective.

## What this says about a finite certificate

- A rigidity certificate for a side-local fixed-point set needs no scale. It has to prove that edges
  sharing no tile commute, using only single-tile relations (F1) and (F2).
- A bounded machine search is out of reach for an explicit DRS set. The zoom must fit a universal
  computation of `O(log N)` bits, and DRS write that they "cannot provide explicitly an aperiodic tile
  set of a reasonably small size".
- So no MSI job was run. The certificate must be a proof schema that propagates commutation through the
  wires and the computation zone.
- Item 4 is the first-order test such a proof must pass. The computation must never let two differences
  meet only along an agreeing edge: every divergence has to be carried along differing edges. In DRS,
  that means head divergence connects all differing input columns.

## Lesson for general BH

- **The hierarchy gives no scale advantage, down to scale zero.** For fixed-point tiles, rigidity is
  exactly non-contextuality of the tile set, read as a planar constraint system in which each variable
  (an edge) lies in exactly two constraints (faces).
- **Consequences for E2.**
  - A proof must propagate commutation between edges that share no tile, through single-tile relations.
  - A kill needs only one pair of tilings whose difference set is disconnected along differing edges,
    at any level of the hierarchy. It needs no width, and it then kills every scale.
- **Design rule for rigid simulations:** "no silent interfaces". Every divergence must be carried along
  differing edges.
- **Spark (not used).** Arkhipov (arXiv:1209.3819, recalled, not re-read) shows that planar
  two-constraint-per-variable parity systems have no quantum advantage. Whether planarity forces
  commutation of FLEFs for rigid-looking tile sets is the natural contextuality question.
