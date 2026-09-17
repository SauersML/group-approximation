---
rg: 2
id: brin-thompson-nv-a-t-menable-via-triangular-split
kind: route
title: "Split the Haagerup property of nV along the undistorted triangular subgroup T_n: a non-cubical cnd function proper on cosets, plus a cnd function proper on T_n"
target: brin-thompson-groups-nv-are-a-t-menable
requires:
  - haagerup-splits-as-coset-plus-subgroup-properness
  - brin-thompson-nv-cnd-proper-modulo-triangular-subgroup
  - brin-thompson-nv-cnd-proper-on-triangular-subgroup
---

**Route.** Let `n ≥ 2` and `H = T_n`. By `haagerup-splits-as-coset-plus-subgroup-properness`,
`nV` has the Haagerup property if and only if both of the following hold.

- **R1 (transversal).** `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`: a cnd function
  proper modulo `T_n`.
- **R2 (fibre).** `brin-thompson-nv-cnd-proper-on-triangular-subgroup`: a cnd function on `nV`
  proper on `T_n`.

The sum `ψ_1 + ψ_2` is then a proper cnd function. Both prerequisites are also necessary, so
this route loses nothing: a counterexample to either one refutes the target.

**Why along `T_n`, and what breaks from `V` to `2V`.**
- *For `V = 1V`.* Farley's wall count is proper, and every infinite-order element grows linearly
  in the exponent cocycle (hyperbolic periodic points). The split is trivial (`H = 1`).
- *For `2V`.* The baker's map moves exponent between coordinates, and the Callard–Salo element `f`
  is distorted, `|f^N| = O(log^4 N)`. So every commensurating action is bounded on `⟨f⟩`, and
  Farley's proof has no analogue (Callard–Salo Corollary 1.2).
- *The split isolates the break.* `T_n` consists of the elements that preserve the coordinate
  tower `C^n → C^{n−1} → ... → C`, so exponent cannot flow into lower coordinates. Every
  infinite-order element of `T_n` is undistorted
  (`brin-thompson-triangular-subgroup-is-undistorted`). R2 carries the fibre content (Brothier's
  Problem B for `Γ = V, Z`). R1 carries all of the distortion.
- *Proven obstruction on R1.* By `brin-thompson-nv-no-cubical-action-proper-mod-triangular`, no
  commensurating action, CAT(0) cube complex or wall space is proper modulo `T_n`, or modulo any
  undistorted subgroup. So R1 needs a cnd function growing polylogarithmically and unboundedly on
  `⟨f⟩`. Farley-type walls for R1 combined with Problem B for R2 is a dead class.

**Where to attack next.**
- R1: infinite weighted sums of wall counts, or cocycles from non-commensurating representations
  (for example Koopman-type representations on `L²` of a space of charts with a scale-dependent
  measure). A successful R1 must beat the dichotomy with infinitely many active `⟨f⟩`-orbits.
- R1, refutation side: a sequence `g_k` in infinitely many cosets of `T_n` that is "uniformly
  compressed" (for example, conjugates of powers of `f`, which are all distorted) would refute R1
  through a coarse-embedding or compression bound. This is the natural test computation.
- R2: its `n = 2` fibre case is Problem B for `Γ = V`.
