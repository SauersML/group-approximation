# Overfold merges on covers of the Sym base B_1: first cover census

Worker swarm-0917-w22-w22-fp-last1 (census-computation), September 20, 2026.
Target: `fpbs-mal-overfold-merges-never-help` (O), which states
`deep_j(Q) = law_j(Q)`. The newest route to the Bernoulli floor (w21-fp-pull,
`fpbs-mal-depth-floor-from-sym-base-overfold-domination`) needs only the
restriction (O|B): `deep_j ≥ c_1 · law_j` on finite transitive covers of the
base `B_j = Cay(Sym(j+2))`, with `a ↦ (0 1)` and `b ↦ (0 1 ⋯ j+1)`.
w21-fp-pull tested blocks on the bases themselves and wrote: "No proper cover
of `B_j` has been tested." This note is that test at `j = 1`.

## 1. Method

Code: `experiments/fpbs-overfold-sym-covers-2026-09-17/`.

- `covers.py` builds `B_j` as the right-regular level of `Sym(j+2)` using
  `struct_search.cayley`.
- A `k`-sheeted cover is given by permutation voltages in `Sym(k)` on the
  `2|B_j|` edges of the Schreier graph. The voltages are gauge-fixed to be
  trivial on a BFS spanning tree, so every connected `k`-sheeted cover
  appears at least once.
  - At `j = 1`, `k = 2`, there are `7` free edges, so `2^7 = 128` voltage
    choices.
- For each transitive cover `Q`:
  - It checks property (E): every component of `Γ_j(Q)` maps injectively to
    `Q`.
  - It exports the depth-`j` instance with
    `../fpbs-overfold-exact-c-2026-09-17/export.py`.
  - It runs `rel`. The file `rel.c` is copied verbatim from
    `experiments/fpbs-overfold-midn-2026-09-17/rel.c`, the w21-fp-break
    solver on main.
- `rel` decides the relative form. For every set `P` of `s ≤ smax` overfold
  seeds, it checks `lawneed(cl(P)) ≥ law − s`.
  - A line `VIOLATION` would be an exact certified `deep_j < law_j`.
  - When `law − 1 ≤ smax`, a clean run proves `deep_j(Q) = law_j(Q)`
    exactly. This is the reduction proved in
    `research/artifacts/fpbs-overfold-midn-2026-09-20.md` on main.
- `canon` gives a BFS canonical form. `--dedupe` keeps one cover per
  isomorphism class of `F(a,b)`-sets.

## 2. Results

### 2.1 The bases themselves

| base | `n` | `j` | (E) | `law_j` | `rel` result |
|---|---|---|---|---|---|
| `B_1 = Cay(Sym 3)` | 6 | 1 | holds | 3 | clean for `s ≤ 2`: `deep = law` exact |
| `B_2 = Cay(Sym 4)` | 24 | 2 | holds | 12 | clean for `s ≤ 2` (181,569 sets `P`); `s = 3` timed out at 300 s |

### 2.2 All 2-sheeted covers of `B_1`, `j = 1`

The run is `experiments/fpbs-overfold-sym-covers-2026-09-17/all_j1_k2_s3.txt`.

- There are 128 voltage choices. 127 of them give a transitive cover; the
  remaining one is the trivial double cover.
- These 127 covers fall into 31 isomorphism classes.
- Property (E) holds on all 127, so every overfold seed crosses between
  `L_1`-orbits, as on the base.
- Among the 31 classes, the law values are distributed as follows:
  - `law 3`: 8 classes;
  - `law 4`: 14 classes;
  - `law 5`: 5 classes;
  - `law 6`: 4 classes.
- `smax = 3` covers the `law ≤ 4` classes exactly.
- The `law ≥ 5` classes were rerun at `smax = 4`, in
  `lawge5_j1_k2_s4.txt`:
  - The 5 classes with `law 5` are EXACT. Each needs `s = 4` sets: 24,165,570
    or 12,082,785 of them.
  - The 4 classes with `law 6` are clean for all `s ≤ 4`, on 4,027,595 or
    12,082,785 sets at `s = 4`.
- **VIOLATION lines: 0.** No saving occurs at any `s`; every histogram is
  `0:N`.

- On the 4 `law 6` classes, clean runs at `s ≤ 4` leave one possible
  counterexample: a pure-overfold witness of size exactly `law − 1 = 5`.
  That case was then run exactly at `s = 5` with `run_law6.sh`, split over 4
  processes by the first seed. The outputs are `law6_{0,1,2,3}_s5.txt`.

Each output file lists its cover's PA and PB.

| class | auts | lawful seeds | overfold seeds | orbit reps | `s = 5` sets | VIOLATION |
|---|---|---|---|---|---|---|
| `law6_0` | 12 | 12 | 132 | 11 | 128,883,040 | 0 |
| `law6_1` | 12 | 12 | 132 | 11 | 128,883,040 | 0 |
| `law6_2` | 4 | 10 | 132 | 33 | 386,649,120 | 0 |
| `law6_3` | 4 | 8 | 132 | 33 | 386,649,120 | 0 |

**Theorem (computer-checked, `j = 1`).** For every connected 2-sheeted cover
`Q` of `B_1 = Cay(Sym 3)`, we have `deep_1(Q) = law_1(Q)`. This covers all
127 transitive covers and all 31 isomorphism classes, with `law_1` between
3 and 6. On each class, `rel` was run for every `s ≤ law − 1`, and the w21
exact reduction then gives equality.

- Together with the base (`law 3`, exact), (O|B) holds at `j = 1` with
  `c_1 = 1` on every cover of degree at most 2.
- `rel` recorded no saving (histogram bin `0`) in any of these runs.
- At most `1.03 · 10^9` closures were needed in total.

### 2.3 Double covers of `B_2`, `j = 2`

- A double cover of `B_2` has `n = 48`, and its depth-2 instance has
  `V = 960`.
- `rel` does not even finish computing `law_2` in 300 s. It was killed at the
  time limit.
- No data was obtained here.

## 3. Where it stands

- **What this shows.**
  - This is the first test of (O|B), and of (O), on proper covers of a Sym
    base. It gives no counterexample.
  - `deep_1 = law_1` holds exactly on every connected double cover of `B_1`,
    all 31 classes.
  - No overfold seed ever saves a merge, at any set size, alone or mixed
    with lawful seeds.
  - Every cover satisfies (E). So the crossing structure that (O|B) was
    designed to exploit persists under covering at `j = 1`.
- **Where it dies.**
  1. Only `j = 1` and degree `≤ 2` are exact.
     - `B_2` already has `law_2 = 12`. It is clean only for `s ≤ 2`, and
       `s = 3` timed out at 300 s.
     - On double covers of `B_2` (`V = 960`), `rel` does not finish computing
       `law` itself (Section 2.3).
     - So the regime that (O|B) needs, `j → ∞` with covers of every degree,
       is untouched.
  2. The data is finite-size, so it bounds no `θ_j` and gives no `c_1 > 0`.
     - It moves belief toward (O|B) with `c_1 = 1`.
     - It does not discharge the route's proof obligation.
  3. The exact cost at `s = law − 1` grows like `C(#overfold, law − 1)`.
     - The automorphism-orbit reduction built into `rel` saves only a
       constant factor.
     - The `law 6` classes took `1.3` or `3.9 · 10^8` closures each, at about
       10–30 wall-minutes on 4 shared cores.
     - `law ≈ 12` at `j = 2` is out of reach. A proof, or a search that
       builds witnesses instead of enumerating them, is needed there.
- **Suggested next step.**
  - Build an incremental `rel`, reusing prefix closures, with a
    `lawneed`-free goal test when `s = law − 1`.
  - Then sample large `s` with `maxP` on `B_2` and its double covers, looking
    for a witness rather than exactness.
