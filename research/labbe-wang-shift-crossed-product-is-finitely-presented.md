---
rg: 2
id: labbe-wang-shift-crossed-product-is-finitely-presented
kind: claim
title: The crossed-product algebra of Labbé's minimal aperiodic Wang shift over a finite field is finitely presented
distinct_from:
  labbe-shift-derived-full-group-is-finitely-presented: that asks whether the derived topological full group is finitely presented, a group question; this asks whether the coefficient algebra LC(Omega_U, F_q) x| Z^2 is finitely presented, which by quantum rigidity is a question about operator-valued local tilings.
  ledrappier-crossed-product-is-finitely-presented: that settles rigidity for a permutive SFT with a fixed point; this asks for rigidity of a minimal aperiodic self-similar SFT, whose crossed product is simple.
---

**OPEN.** Let `Ω_U` be Labbé's minimal aperiodic Wang shift (`minimal-aperiodic-wang-shift-exists`)
and `q` a prime power. Then `R_U = LC(Ω_U, F_q) ⋊ Z^2` is finitely presented. By
`sft-crossed-product-fp-iff-quantum-rigid`, this is equivalent to `D`-quantum rigidity of `Ω_U`
for some `D`.

**Payoff.** `R_U` is finitely generated and simple, since the action is free and minimal. It has a
unital rank model by Følner truncation, and so no halvable corner. Rigidity would make it a
finitely presented infinite-dimensional simple algebra over a finite field with a faithful rank
function. It would then be the gate (a) instance for
`sofic-fp-simple-kazhdan-group-from-fp-simple-ring`, and `EL_n(R_U)` would be `F_q`-linear sofic
and Kazhdan. Simplicity and the rank model are to be written up. Gates (b) and (c) stay open.

**Refutation.** A non-commuting operator-valued local tiling of Labbé's tiles. By
`labbe-shift-is-wall-rigid`, for large `D` it must be genuinely contextual, with no two-dimensional or
finitely filtered piece.

**Current reduction.** For `D >= D_0` the local tiling algebra has an idempotent commutator ideal `J_D`.
This claim holds iff `J_D = 0` for some `D` (`labbe-shift-is-wall-rigid`). Route in:
`labbe-crossed-product-fp-via-wall-rigidity`, through the open `wall-rigid-z2-sft-is-quantum-rigid`.

## Attempts

- **Periodic models.** Useless in either direction: `Ω_U` has no finite orbit (peer Theorem A in
  `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`). Classical finite models cannot
  refute rigidity, and none are needed to prove it.
- **Periodic quantum tilings: live refutation target.** Operator-valued periodic tilings would refute
  rigidity at their scale (`periodic-quantum-tilings-refute-quantum-rigidity`). For `D >= D_0` every
  composition factor would have dimension `>= 3`. None is known, and none was searched for.
- **Entropy walls: dead.** `Ω_U` is self-similar, so it has zero entropy. For a minimal SFT, a wall
  certificate with a finite side forces positive entropy
  (`research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md`, Proposition 4).
  So `positive-entropy-sft-crossed-products-are-not-fp` does not apply.
- **Structure of `Ω_U`: imported** (`labbe-shift-is-a-toral-rotation-coding`, from the TeX source of Labbé,
  arXiv:1903.06137).
  - `Ω_U` is the coding of `x + φ^(-2) n` through a Markov partition. That rotation is the maximal
    equicontinuous factor, the fibre cardinalities are `{1, 2, 8}`, and `Ω_U` is strictly ergodic.
  - The boundary segments point in the directions `(1,0)`, `(0,1)`, `(1,-1)`, `(1,-φ)`.
- **Infinite walls: dead** for `D >= D_0` (`labbe-shift-is-wall-rigid`).
  - Nearby torus points differ along crossing networks of fault sheets. Far ones differ syndetically. Within
    a fibre the differences are unions of full fault lines, with finite clusters excluded by entropy.
  - So two-basis certificates, and every family on `k^2` or with a finite filtration, commute.
- **Permutive propagation: dead as it stands.**
  - In Labbé's 19 tiles, left and right colours determine the tile (19 distinct pairs). Left and bottom do
    not (tiles 2 and 6 share `(F, P)`), and neither do right and top (tiles 0 and 1 share `(F, O)`).
  - Heuristically no recoding is triangle-permutive. `Ω_U` has four nonexpansive fault directions,
    including the irrational `(φ, 1)`, while a triangle-permutive SFT should be expansive off its three
    side directions. The last point is not checked.
- **Genuinely quantum families: open, and now the whole question.** Contextual constraint systems such as
  the magic square have operator solutions with no classical counterpart.
  - By `sft-wall-rigidity-iff-idempotent-commutator-ideal` these are exactly the remaining obstructions.
  - Frame analysis in dimension 3 kills loops through two-letter bands, but not triangles of frames glued
    through scalar rays.
  - Undecidability results for constraint systems suggest that no general algorithm decides rigidity; that
    is a heuristic, not a proof for this shift.
- **Group finite presentation implies this claim (ex2-labbe-relation-climbing, 2026-09-13).** Route
  `labbe-crossed-product-fp-via-group-fp`, for `q` prime to 15. It does not fire, because
  `labbe-shift-derived-full-group-is-finitely-presented` is open. Read in reverse, a noncommuting family
  at every scale here also refutes finite presentation of Labbé's derived full group
  (`zd-derived-full-group-fp-forces-quantum-rigidity`).
