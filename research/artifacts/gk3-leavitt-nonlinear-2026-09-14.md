# Nonlinear strict automata over the binary Leavitt unit group: mechanism, filter, gap

Date: 2026-09-14. Lane `gk3-leavitt-nonlinear`. `G = R^x`, `R = L_(F_2)(1,2)`.
Target: a nonlinear strict pair over `G`, or the exact obstruction.

**Verdict:** not decided. No strict pair was found. This lane landed:
- the rule-free filter `two-rectangle-surjunctive-images-kill-all-designs` (0363ccee5);
- the hand computation `leavitt-rooted-defect-window-carries-no-strict-design`
  (e39a422ba, moved to a route in 0b43ab3fc);
- the screen claim `small-leavitt-windows-carry-no-strict-design`. Seven windows are dead
  for every design, and three are undecided within the search bounds.

## 1. What "reading compressed copies" can mean for an automaton over `G`

An automaton over `G` reads `x(g m)` for `m` in a finite memory `M` of group elements.
The Leavitt isometries `s_0, s_1` are not units, so they never enter a memory. What
enters is a unit that agrees with an isometry on a corner.

- **Thompson units realize prefix replacements.** For complete prefix codes
  `(d_1..d_k)` and `(e_1..e_k)`, the unit `sum_i S[e_i] T[d_i]` acts on the corner
  `[d_i]` as the partial isometry `S[e_i] T[d_i]`. Its inverse is `sum_i S[d_i] T[e_i]`.
  The nine-leaf compressor `cu` of `openai-nine-leaf-leavitt-configuration` acts on
  `[alpha_i]` as "append 0". It is a unit only because it also sends `beta_i` to
  `alpha_i 1` and `nu_i` to `zeta_i`. That complement is the defect of realizing an
  isometry by a unit.
- **In the group the compression is a strict conjugation inclusion.** Conjugation by
  `cu` sends `E_ij(r) = 1 + S[alpha_i] r T[alpha_j]` to `E_ij(s_0 r t_0)`. So
  `cu Gamma cu^-1 < Gamma` properly, with `Gamma = EL_alpha(R)`.
- **The only equivariant use of a strict inclusion is on coset shifts.** The map
  `g Gamma -> g u^-1 Gamma` is well defined exactly when `u Gamma u^-1 <= Gamma`. It
  is equivariant and surjective, and its fibres are the cosets of `u^-1 Gamma u / Gamma`.
  Pulling back along it is a strict equivariant injection on `A^(G/Gamma)`
  (`compressed-coset-shifts-carry-strict-equivariant-embeddings`). Two facts block it:
  - full shifts map only constantly into coset shifts with infinite stabilizers
    (`full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`);
  - a finite subgroup admits no strict conjugation inclusion, since conjugation is
    injective on a finite set.
  So a strict pair on the free shift cannot be a pullback of a compression. It has to
  produce the missing pattern through the rules, which is the invariant-output or
  hinge form of `leavitt-units-carry-injective-invariant-output-automaton` and
  `defect-window-automaton-over-leavitt-units`.

## 2. The two-rectangle table group decides a window

For a window `(S, M)` in `G`, let `T` have a letter per element of `S u M` and relators
from both rectangles:
- `x_s x_m = x_s' x_m'` when `s m = s' m'`;
- `x_m x_s = x_m' x_s'` when `m s = m' s'`.

- **Universal realization.** `x_a -> a` maps `T` onto `<S u M>` with the same forward
  and reverse tables. By Lemma 3 of
  `research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md`, every
  design on the window has the same strictness status over `T` as over `G`.
- **Filter.** If a homomorphism from `T` into a surjunctive group keeps the distinct
  reverse products apart, every design on the window is surjective over `G`. This is
  `two-rectangle-surjunctive-images-kill-all-designs`. Unlike Corollary 3 of
  `strict-pairs-transfer-to-table-realizations`, it needs no Garden-of-Eden window, so it
  screens general designs and not only invariant-output ones.
- **Necessary condition.** A strict window needs a reverse hinge word, nontrivial in
  `G`, that dies in every sofic image of `T`. Sofic images combine by direct products.

## 3. The most direct defect window, by hand

Take `a = cu c^-1 cu^-1`, with `c` the `x_0` of Thompson's `F` on the cylinder `[1000]`,
so `a` lies in `V_(0001) <= Gamma` and has infinite order. Take `l = E_01(1)`, an
involution, since `(S[alpha_0] T[alpha_1])^2 = 0`. Put `S = {1, a, a^-1, a l}` and
`M = {1, l, a}`; this realizes the rooted identification `(a l^-1, l) ~ (1, a)` of the
defect node.

- **Forced coincidences.**
  - Forward: `(1,a) = (a,1) = (al,l)`, `(a,l) = (al,1)`, `(a^-1,a) = (1,1)`.
  - Reverse: `(1,a) = (a,1)`, `(a,a^-1) = (1,1)`.
  - They give `x_(al) = x_a x_l`, `x_l^2 = 1` and `x_(a^-1) = x_a^-1`.
- **Result.** If `G` has no further coincidence in either rectangle, then
  `T = <x_a> * <x_l | x_l^2> = Z * Z/2`, which is residually finite. The window is then
  dead for every design, whatever the alphabet.
- **Status.** The absence of further coincidences, such as `a l a = l` or
  `a^2 = a^-1 l`, is what `defect-direct-E01` in the screen certifies by exact
  normal-form products. Not yet run.

This matches the "small core" death recorded in the defect node, now for all designs
on the window at once.

## 4. Screen and results

**Results** (MSI jobs 790307 and 791209; witnesses replayed on MSI and locally in dual mode, 1214
products cross-checked).

| window | letters / relators | reverse classes | verdict |
|---|---|---|---|
| control-gl2-1-1 | 3 / 20 | 6 | dead: `<S u M>` has order 6 |
| thompson-aw-1-1 | 3 / 12 | 10 | dead: PSL(3,2) images separate 10 of 10 |
| thompson-aw-2-1 | 9 / 40 | 20 | dead: 20 of 20 |
| thompson-aw-1-2 | 9 / 40 | 20 | dead: 20 of 20 |
| transvections-1-1 | 5 / 26 | 23 | dead: 23 of 23 |
| defect-direct-E01 | 4 / 6 | 10 | dead: 10 of 10, agreeing with Section 3 |
| defect-ball-1-1 | 6 / 24 | 30 | dead: 30 of 30 |
| defect-nested-E01 | 7 / 12 | 31 | undecided: GAP timeout (simplified 5 / 2) |
| eld1-cu-1-1 | 8 / 44 | 59 | undecided: GAP timeout (simplified 7 / 12) |
| eld1-cu-c-1-1 | 10 / 76 | 83 | undecided: GAP timeout (simplified 8 / 18) |

Every separating image found is onto PSL(3,2) on 7 points. The two defect windows are dead:
the defect `d` sits in the memory, yet the table group has finite images separating all
reverse products. The undecided windows are the ones containing the six `E_ij(1)` of
`Gamma` together with the compressor, where the rectangle relators carry
elementary-matrix commutation relations.

**Method.**

`experiments/gk3-leavitt-nonlinear/general_window_screen.py`, MSI outputs under
`/scratch.global/sauer354/gk3-leavitt-nonlinear/runs/`.

- **Stage 0.** A finite subgroup `<S u M>` is dead.
- **Stage 1.** GAP, run through `sage -gap` as in the earlier small-window screen:
  - Tietze-simplify `T`;
  - search for quotients onto small simple and symmetric groups, then low-index
    permutation actions;
  - keep each image that separates more reverse classes.
- **Verification.** Witnesses are permutation images of the original letters, and
  `--verify` replays relators and separation in Python.
- **Windows.**
  - Control: the ball `B_1({u,v,w})`.
  - Thompson balls: `{a, A, w}` at radii 1:1, 2:1, 1:2.
  - Transvections: radius 1.
  - Nine-leaf: `E_ij(1)` with `cu`, and with `cu, c`.
  - Defect-direct and nested defect windows.
  - The defect ball `B_1({E_01(1), cu, c})` with `d_01`.

## 5. Exact gap

- **Undecided windows.** `defect-nested-E01`, `eld1-cu-1-1` and `eld1-cu-c-1-1` hit the
  GAP time limit. The next step is a longer run with targeted images:
  - the GL(4,2) / GL(6,2) position-dependent corner images of
    `small-leavitt-invariant-output-windows-have-finite-separations`, which realize the
    nine-leaf products;
  - PSL(3,2) and PSL(3,4) images of the `E_ij(1)`.

  A window with no separating image is a candidate, not a counterexample. For such a window
  the question becomes whether some reverse hinge word lies in the sofic radical of `T`.
- **Larger windows.** Survivors are expected only where the rectangle relators encode a
  Kazhdan presentation plus nesting (`nested-rigid-defects-force-nonsurjunctivity`).
- **Rules.** For survivors, a SAT search for rules whose minimal forward partition
  forces those relators and whose reverse partition needs a surviving hinge. The
  abstract census belongs to lane `gk3-strict-census-4`. Here it would run only on
  surviving windows over `G`.
- **Roots.** `leavitt-unit-group-surjunctive` and `leavitt-unit-group-nonsurjunctive`
  are unchanged.
