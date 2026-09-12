---
rg: 2
id: small-leavitt-invariant-output-windows-have-finite-separations
kind: claim
title: Small ball windows over the Leavitt unit group carry no invariant-output strict pair, by finite images of their table groups
distinct_from:
  strict-pairs-transfer-to-table-realizations: that is the transfer theorem, whose Corollary 3 turns a finite image of a window's table group into a rule-free exclusion; this is its computed instance on 44 explicit windows, with replayable witnesses.
  leavitt-units-carry-injective-invariant-output-automaton: that is the open existence problem for an invariant-output strict pair over the Leavitt unit group; this excludes the pairs whose symmetry and memories lie in 44 explicit ball windows.
  two-cell-window-differences-die-in-host-abelianization: that is an abelian lattice test on the canonical table host of a design with a two-cell window; this uses the ambient product tables of invariant-output windows and nonabelian finite images, PSL(3,2) included, where every abelian test fails.
artifacts:
  - research/artifacts/gottschalk-small-window-screen-2026-09-12.md
  - experiments/gottschalk-small-presentations/window_table_screen.py
  - experiments/gottschalk-small-presentations/runs/res-a.json
  - experiments/gottschalk-small-presentations/runs/res-b.json
---

**ESTABLISHED** by `small-leavitt-window-separation-certificates`.

Let `G = L_(F_2)(1,2)^x`. For a finite generating list `X` of units, radii
`r_m, r_s`, and a unit `h` of prime order `p`, put

    S = B_(r_s)(X),     M = <h> . B_(r_m)(X),

balls in `X u X^-1`. Let `U` be the table group with generators `x_a`,
`a in S u M`, `x_1 = 1`, and relators `x_s x_m = x_s' x_m'` whenever `sm = s'm'`
in `G`, and `x_k x_m = x_(km)` for `k in <h>`, `m in M`.

**Theorem.** For each of the 44 windows in the table of the artifact, some
homomorphism from `U` into a finite group sends `x_h` to a nontrivial element. The
windows are:
- ball windows over Thompson units, low-depth transvections, the four GL(4,2) atlas
  charts, and mixtures of these, at radii `1:1, 1:2, 2:1, 2:2` or `1:1, 1:2, 2:1`,
  with `h` of order 2 or 3;
- the nine-leaf windows `E_ij(1)` plus the compressors `cu, cv`, with `h = E_01(1)`,
  or with `p3` added and `h = p3`, at radii `1:1, 1:2, 2:1`.

The images are:
- a character to `Z/p` in 35 windows;
- a permutation image of degree at most 7 in the other 9, onto PSL(3,2) for the
  nine-leaf windows.

**Consequence.** No injective automaton over `G`, with any finite alphabet and any
local rules, has output invariant under `<h>` together with memories `M' <= M` and
`S' <= S` with `hM' = M'`, for any of these windows. The certificate would realize
its window data in the finite image with `x_h != 1`, and by
`strict-pairs-transfer-to-table-realizations` (Corollary 3) such a pair is not
strict there, a contradiction.

**Not covered.**
- The window `eld-full-order2` at radii `1:1`: the 30 `E_ij(r)`,
  `r in {1, s0, s1, t0, t1}`, with `cu, cv`. It survives characters, and every
  2-quotient of class at most 3 (orders `2^140` and `2^1435`) kills `x_h`. The PSL(3,2)
  quotient search did not finish within 45 minutes, so the window is unresolved.
- Larger radii, other symmetries `h`, and memories not contained in these balls.

The claim does not bear on `leavitt-unit-group-nonsurjunctive` beyond excluding
these windows.
