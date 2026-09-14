# Thompson V: calibrating free-gluing searches against planted controls

Date: 2026-09-13. Lanes `solve-v-planted-search` (sections 1--4, permutation side; the lane stopped
before writing its results, and lane `hl-v-approximation` harvested them) and `hl-v-approximation`
(section 5, unitary side). All computation ran on MSI (agsmall, one core per task). Code and raw
result lines are in `experiments/thompson-v-models/`:
- permutation side: `vtc.c`, `vtc.sbatch`, `results_vtc_720595.txt`; `vrepair.c`, `vrepair.sbatch`,
  `results_vrepair_721016.txt`; `gen_ctrl2.py`, `gen_ctrl2.log`, `rel_CTRL2.txt`, `vctrl2.sbatch`,
  `results_vctrl2_721360.txt`;
- unitary side: `glue_hs.py` (job 720734, `results_vhsglue_720734_summary.json`) and `glue_hs2.py`
  (`glue_hs2.sbatch`, job 731687; `glue_hs2_ctrl2.sbatch`, job 732611; `results_vhs2_731687.json`,
  `results_vhs3_732611.json`).

This follows `thompson-v-free-gluing-annealing-2026-09-13.md`, whose annealer solved the planted
control only at `k = 48`. The claims used are `thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words`,
`thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words` and
`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`.

## 1. A correction about the planted control

The control group is `G_ctrl = (S4 *_<a> S3) / <<u_1, ..., u_4>>`, where the four words are trivial
in `S5` under `a = (0 1)`, `b = (1 2 3)`, `c = (0 4)` (`gen_ctrl.py`). So `S5` is a quotient.

**Small exact models are forced.** Let `H <= S5` meet every conjugate of `<a,b> = S4` and of
`<a,c> = S3` trivially. Then the right action of `S5` on the cosets `H\S5` is an exact free gluing
of size `120/|H|`: `Hg.s = Hg` means `g s g^-1 in H`, so `s` lies in `g^-1 H g ∩ S4 = 1`, and
likewise for `S3`.
- **Which H qualify.** The orders of `S4` and `S3` are divisible only by 2 and 3, so a subgroup of
  order prime to 6 qualifies. In `S5` these are `1` and the cyclic groups of order 5.
- **Consequence.** `C5` gives a transitive exact free gluing of size 24, and disjoint unions give
  exact gluings at every `k` divisible by 24.
- **So "solving the control at k" says little about large models.** A search that assembles
  24-point components solves the control at every `k` without building one large consistent
  structure, and `V` has no such components (it has no nontrivial finite actions). Every solution
  below is reported with its component structure.

**A second control without small components** (`gen_ctrl2.py`, seed 1, `gen_ctrl2.log`, `rel_CTRL2.txt`).
- **The group.** `G = PSL(2,17)`, of order 2448, on the projective line. The script finds `a, b, c`
  with `<a,b> = S4`, `<a,c> = S3`, `<a,b> ∩ <a,c> = <a>` and `<a,b,c> = G`. The four words have the
  lengths of `r5..r8` (26, 28, 26, 37) and are trivial in `G`.
- **Which components.** All involutions of `G` are conjugate, and so are all elements of order 3
  (checked by the script). `<a,b>` contains both kinds, so a subgroup `H` meeting every conjugate
  of `<a,b>` and `<a,c>` trivially has order prime to 6. The element orders are 1, 2, 3, 4, 8, 9, 17,
  so `H` is trivial or of order 17, and exact gluings through `G` have components of 144 or 2448
  points. This says nothing about other finite quotients of `G_ctrl2`.
- **An exact CTRL2 gluing in standard form is built and checked** in `glue_hs2.py`
  (`ctrl2_exact_gluing`): `G` acts on the 144 cosets of an element of order 17, and relabeling the
  six free `<a,b>`-orbits onto the standard blocks gives `C` with `c^2 = (ac)^3 = 1` and all four
  CTRL2 words exactly `I` (in the reversed word convention; forward gives defect `sqrt 2`).

## 2. Searches

**`vtc.c`: exact depth-first search with scanning.**
- **State.** `a` and `b` are fixed as in `vglue.c`: block `j` holds points `24j..24j+23`, with a
  free `S4`-action on each block. `c` is a partial fixed-point-free involution with `c(x) != a(x)`.
- **Propagation.** Each new `c`-edge triggers a Felsch-style scan, forwards and backwards, of every
  relator instance through it. A scan with one gap deduces `c` there; a scan closing wrongly, or an
  illegal deduction, is a conflict. `(ac)^3` is always scanned, so completed states are free gluings.
- **Symmetry.** New blocks enter canonically, removing the `S4 wr S_m` symmetry of `(a, b)`. In
  transitive mode a completed state is transitive.
- **Branching.** `heur 0`: first undefined point. `heur 1`: the point ending the most nearly complete
  scans. `heur 2`: among the six best-scored points, the one with fewest surviving candidates.

**`vrepair.c`: repair-move annealing.**
- **State space.** As in `vglue.c`: `c = tau^-1 c_0 tau` with `tau in C(a_0)`, so all short relators
  hold exactly.
- **Repair move** (probability `1 - noise`): pick a violated instance and a `c`-letter of it, and
  conjugate `c` by the pair swap commuting with `a` that closes that letter. **Noise move**: a random
  pair flip or swap.
- **Acceptance.** Metropolis on the number of violated instances; schedule `P1` (`T` from 2 to 0.05,
  noise 0.1) or `P2` (`T = 0.5`, noise 0.05). A run stops at 0.

## 3. Permutation calibration

Best mean fraction of points moved by the four words, three seeds per cell unless stated; `comp` is
the component structure of the best state.

**`vtc`, exact transitive search** (4 restarts of `2 * 10^7` nodes each; job 720595, and job 721360
tasks 24--25):
- **CTRL** at `k = 48, 72, 96, 120`: every run, with all three heuristics, ended at the node limit
  with no solution.
- **CTRL2** at `k = 144`: the same.
- **V** at `k = 48`: the node limit again. The search did not exhaust the space.

This is consistent with section 1: the small exact CTRL gluings are unions of 24-point components,
not transitive. It also shows the search is too weak to find the transitive exact gluings that exist
at `k = 120` (CTRL) and `k = 144` (CTRL2).

**`vrepair`** (job 721016, control CTRL = `S5`). One value per seed; `comp` describes the best state.

| k | CTRL `P1` | CTRL `P2` | V `P1` | V `P2` |
| --- | --- | --- | --- | --- |
| 48 | 0, 0, 0 (comp 2, largest 24) | 0.78, 0.70, 0.78 | 0.75, 0.75, 0.75 (comp 2, largest 24) | 0.84, 0.83, 0.86 |
| 120 | 0.82 (comp 2, largest 96), 0.40 (comp 5, largest 24), 0.13 (comp 5, largest 24) | not finished, 0.86, 0.85 | 0.81, 0.84, 0.86 | 0.86, 0.86, 0.88 |
| 240 | 0.87, 0.88, 0.86 | not finished, 0.86, 0.86 | 0.88, 0.89, 0.87 | not finished |

**`vrepair` on CTRL2** (job 721360):
- **CTRL2:** best 0.90--0.92 at `k = 144` and 0.93--0.94 at `k = 288`, never solved.
- **V:** 0.87--0.89 at `k = 144`, and 0.89--0.90 at `k = 288` (`P1`; the `P2` runs were not finished).

**Reading.**
- Every CTRL success is a union of 24-point components, as section 1 predicts. The nearest approach
  at `k = 120` (0.13) is five components with largest 24.
- On the control without small components the repair annealer never gets below 0.90, while `V`
  scores slightly lower. So the permutation searches are **uncalibrated beyond small components**,
  and their `V` plateau carries no information about soficity.

## 4. What the permutation side shows

- **No evidence either way about sofic approximations of `V`.** The searches find exact models only
  when the planted group has 24-point components, which `V` cannot have.
- **Calibration target for any future permutation search:** solve CTRL2 at `k = 144` from random
  starts before reading anything into a `V` plateau.

## 5. Unitary calibration

**Search space.** Form 4 of `thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words`: gluings
`(A_0, B_0, W^* C_0 W)` of size `N = 24k`, with `W` in the commutant of `A_0`, so every short relator
holds exactly. The loss is the mean over the four words of `||r - I||_2^2 = 2 - 2 Re tr r`, with an
exact commutant gradient. Job 720734 checked the gradient against finite differences:
predicted `-0.0059401611`, numeric `-0.0059401611`. Random starts sit at 1.94--2.03.

**Methods** (`glue_hs.py`, job 720734; `glue_hs2.py`, jobs 731687 and 732611), all from Haar-random
commutant starts:
- `descent`: adaptive Riemannian descent. Job 720734 ran 3000 iterations. Jobs 731687 and 732611 ran
  4000 at `N = 120, 144` and 2000 at `N = 240, 288`.
- `restart`: 40 descents of 150 iterations from independent starts, then a polish of the best one.
- `anneal`: descent interleaved with random commutant rotations `exp(sigma Om)`, with `sigma` from 0.3
  to 0.01 and a Metropolis acceptance rule at temperature 0.05 to `1e-4`, then 1500 polish iterations.

Job 731687 ran the first revision of `glue_hs2.py` (md5 `5c116263...`). The landed file (md5
`1780b668...`, run by job 732611) differs only by the added `CTRL2` branch.

**Controls, checked inside every run.**
- `CTRL`: the `S5` words of section 1, exact at `N = 120` in both word conventions. This control has
  24-point components.
- `CTRL2`: the `PSL(2,17)` words, with the exact gluing built and checked at `N = 144` and `288`
  (defect 0 in the reversed convention).
- `planted` (job 720734): `V`'s words raised to their orders in a finite quotient `Q` of the amalgam
  (`|Q|` = 24, 72, 120, 360), so the words are longer (52--148 letters). Exact at `N` divisible by `|Q|`.

**Job 720734** (mean squared defect, 3000 iterations):

| set | N = 24 | 48 | 72 | 96 | 120 | 144 | 192 | 240 | 360 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| V | 1.20--1.28 | 1.22--1.24 | | 1.22--1.23 | | | 1.22 | | |
| planted | 0.67--0.73 | 0.72 | 0.72 | 0.72 | 0.70 | 0.71--0.72 | 0.72 | 0.70 | 0.71 |
| null | | 0.99, 1.21 | | 0.99, 1.23 | | | | | |

The null values of 0.99 are degenerate runs where two words collapse and one sits at 2.

**Basin test** (job 720734). Start from the exact planted solution conjugated by `exp(eps Om)`, with `Om`
a random commutant skew-Hermitian matrix of operator norm 1:
- at `eps = 0.1` and `0.3` descent converges to `1e-13` in under 500 iterations, at `N = 72` and `120`;
- at `eps = 1` it stops at 0.51--0.53, and at `eps = 3` at the generic 0.70--0.71.

**Jobs 731687 and 732611** (mean squared defect, one value per seed):

| set | N | descent | restart | anneal |
| --- | --- | --- | --- | --- |
| CTRL (exact at this N) | 120 | 1.196, 1.198 | 1.191, 1.193 | 1.183, 1.184 |
| CTRL | 240 | 1.194, 1.195 | 1.193, 1.194 | not finished |
| CTRL2 (exact at this N) | 144 | 1.270, 1.271 | 1.272, 1.270 | 1.269, 1.266 |
| CTRL2 | 288 | 1.275, 1.274 | not finished | not finished |
| V | 120 | 1.218, 1.219 | 1.219, 1.216 | 1.214, 1.203 |
| V | 144 | 1.222, 1.215 | 1.215, 1.218 | 1.207, not finished |
| V | 240 | 1.221, 1.221 | not finished | not finished |

In every cell the largest per-word HS defect is 1.13--1.17, and `c^2 = (ac)^3 = 1` holds to `1e-13`.

**Reading.**
- **No method solves either control from generic starts, at any `N`.** The best control run (CTRL,
  anneal, 1.183) is as far from 0 as the `V` runs.
- **The ordering follows the words, not the models.** `V` (1.20--1.22) lies between CTRL (1.18--1.20)
  and CTRL2 (1.27--1.28). Both controls have exact gluings at these sizes; `V` has none at any size.
- **The failure is global, not local.** Descent converges from within operator-norm distance about 0.3
  of an exact solution. From distance 1 or more it lands on the same plateau as a Haar start.
- **So the unitary plateau carries no information about hyperlinearity of `V`,** just as the
  permutation plateau of section 3 carries none about soficity.

## 6. Exact gap

- **No calibrated search exists on main.** Permutation searches (`vglue`, `vrepair`, `vtc`) and unitary
  ones (`hs_probe`, `glue_hs`, `glue_hs2`) all fail from generic starts. No numerical statement about
  approximations of `V` is supported in either direction until a search solves CTRL2 (`N = 144`
  unitary, or `k = 144` permutation) from generic starts.
- **Exact controls are structurally unlike V.** Every control with exact gluings factors through a
  finite quotient. `V` has no nontrivial finite-dimensional unitary representation
  (`thompson-v-has-no-nontrivial-fd-unitary-representation`), so its near-solutions are approximate at
  every `N`. A control whose calibration transfers to `V` would be a quotient of `S4 *_C2 S3` with no
  nontrivial finite-dimensional representations and with known approximate models. This lane
  identified none.
- **Theory: nothing new.** The gluing criteria stand. A uniform lower bound (so `V` is not hyperlinear)
  and a near-solution family (so `V` is hyperlinear) are both still open. The data give no pattern to
  extract, because `V` shares its plateau with controls that do have exact models.
- **Not finished at harvest time.** Tasks 10, 11 and 20--23 of job 731687; tasks 8--11 and 17 of job
  732611; tasks 9, 15 and 33--35 of job 721016; tasks 21--23 of job 721360. All are repeats at larger
  `N` of methods that already fail calibration at smaller `N`.
