---
rg: 2
id: toms-conflict-free-face-labellings-never-exist
kind: claim
title: Conflict-free missed-face labellings of a cube partition never exist, so ruling them out cannot prove relative Hex R1(3); octant-jack and symmetry-broken SAT searches for F(3)
artifacts:
  - experiments/toms-relative-hex-2026-09-19/face_form_sat.py
  - experiments/toms-relative-hex-2026-09-19/face_form_sat_sym.py
  - experiments/toms-relative-hex-2026-09-19/jack_sat.py
  - experiments/toms-relative-hex-2026-09-19/results.json
distinct_from:
  toms-spanning-defect-is-superadditive: that amplifies one face counterexample into linear defect and gives the plain SAT model; this proves a labelling lemma that kills the conflict-free-labelling route to R1(3) and adds symmetry-broken and octant-jack searches.
  toms-level-two-spanning-reduces-to-relative-hex: that reduces F(3) at max delta = 2 to R1(3) and refutes R1(2); this shows the labelling obstruction proposed for R1(3) is present in every configuration, including the R1(2) counterexample, so it carries no information.
  toms-two-level-spanning-holds-in-every-dimension: that proves (S) for max delta <= 1 by fills and Phragmen-Brouwer; this is a degree statement about missed-face labels, true for every partition regardless of levels.
---

**ESTABLISHED** (internal derivation, unreviewed; proof
`toms-conflict-free-face-labellings-never-exist-proof`). The computations are exact SAT runs
(pysat Cadical153), unreviewed. `R1(3)` and `F(3)` stay **OPEN**.

**Setting.** Subdivide `I^N` into the product cell complex with `n` intervals per coordinate.
Its cells are the products of vertices and open intervals. For a cell `c` and a face
`F = {x_nu = s}` of the cube, write `n_F` for the outward normal (`-e_nu` if `s = 0`,
`+e_nu` if `s = 1`). A *missed-face labelling* assigns to each cell `c` a vector
`l(c) in {+-e_1, ..., +-e_N}` with `l(c) != n_F` whenever `c` lies in `F`. It is
*conflict-free* if no cell `c` and cell `c'` with `c` in the closure of `c'` have
`l(c) = -l(c')`.

**Theorem.**
1. *Labelling lemma.* No missed-face labelling of `I^N` is conflict-free, for any `N >= 1`
   and any `n`.
2. *Partitions.* Let `I^N` be partitioned into finitely many connected unions of cells, each
   missing at least one face of the cube. However each piece `Omega` picks a face
   `F(Omega)` that it misses, some two pieces with touching closures picked the two opposite
   faces of one coordinate. For a cell-constant usc `delta` and its level components, the
   lower-dimensional cell of such a pair has the strictly larger level.
3. *The route is vacuous.* The next step recorded on
   `toms-simple-algebra-realizes-no-leaf-average-rank` (w14-113) was to prove `R1(3)` by
   ruling out conflict-free missed-face colourings of adjacent components in a grown normal
   form. By part 2 such colourings do not exist for any partition. That includes the slit-wall
   counterexample to `R1(2)` and the controls that the SAT model finds satisfiable. So their
   absence cannot imply `R1(3)`. Any proof must use the counts: level `t` components fail
   `t + 1` coordinates, and `R1(2)` fails because level 2 there needs only two.

**Computation** (`results.json`; `N = 3`, `max delta = 2`, `n` intervals per coordinate).
- *Symmetry breaking.* `face_form_sat_sym.py` adds lex-leader constraints for all 47
  non-identity symmetries of the cube, which is sound (every orbit keeps its lex-least member).
  It reproduces the known answers. `N = 2, n = 3` and `N = 3, n = 2` are UNSAT. The `R1(2)`
  control `N = 2, n = 4, cap 2` is SAT, so the breaking kills no model. `N = 3, n = 3`
  (343 cells) was still undecided at the 20-minute cap, with both full and truncated
  breaking, on a machine at load about 35 on 4 CPUs. Symmetry breaking alone does not decide
  `F(3)` at `n = 3`, so `n = 4` was not attempted.
- *Octant jack.* `jack_sat.py` is the growth normal form with all eight corner blobs present.
  The eight closed octants carry level 2, and `R` is a thin neighbourhood of the three
  midplanes `W`. Levels `{0, 1}` are free on the cells of `W`. SAT would give a genuine `F(3)`
  counterexample (thicken along the normal fibres of `W`). The results:
  - `n = 2` (61 cells of `W`): UNSAT in 0.02 s.
  - `n = 4` (217 cells): UNSAT in 13.6 s.
  - `n = 6` (469 cells): undecided at the 20-minute cap.
  - The variant with level 2 allowed on `W` is unsound, because it drops the contact between
    that level 2 and the blobs. It is trivially SAT and carries no information.
  So no jack-type counterexample exists at these resolutions.

**Next.** Replace single labels by set-valued ones. A level-`t` component carries `t + 1`
missed coordinates. The lemma should be sharpened to a Ky Fan style count of alternating
chains with those sets, which is where `R1(2)` (sets of size 2 at level 2) and `R1(3)`
(size 3) differ.
