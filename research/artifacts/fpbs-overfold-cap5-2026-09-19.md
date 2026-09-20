# Exhaustive five-seed search on the open law-6 overfold levels (2026-09-19)

Worker: swarm-0917-w19-w19-fp-break (belief breaker, minimal-counterexample).
Target node: `fpbs-mal-overfold-merges-never-help`, statement (O):
`deep_j(Q) = law_j(Q)` for every finite `F(a,b)`-set `Q`.

Code and outputs: `experiments/fpbs-overfold-cap5-2026-09-17/`.

Build commands (the binaries are not kept):

- `gcc -O3 -march=native -fopenmp -o deep5 deep5.c`, and the same for
  `deep5fp` and `beam`;
- `beamw` is `beam` built with `-DWIDE`;
- `gcc -O2 -fopenmp -o lcheck lcheck.c`.

## 1. Question

After w17 (`research/artifacts/fpbs-overfold-exact-c-census-2026-09-19.md`),
the undecided Cayley levels of the 54-level census with the smallest gap
between the known lower bound and `law` were:

| instance | `Q` (Cayley action of `⟨α, β⟩`) | `j` | `n` | `V` | `law` | known before |
|---|---|---|---|---|---|---|
| inst24a | `(0,1,3,2),(1,2,0,3)` | 1 | 24 | 192 | 6 | `deep ≥ 5` |
| inst24b | `(1,2,3,0),(0,2,3,1)` | 1 | 24 | 192 | 6 | `deep ≥ 5` |
| j2law8 | `(0,2,3,1),(1,2,0,3)` | 2 | 12 | 240 | 8 | `deep ≥ 3` |
| j2law6a | `(0,1,2,4,3),(1,0,3,2,4)` | 2 | 12 | 240 | 6 | `deep ≥ 3` |
| j2law6b | `(0,1,2,4,3),(1,0,3,4,2)` | 2 | 12 | 240 | 6 | `deep ≥ 3` |

inst24a and inst24b are the w17 exports in
`experiments/fpbs-overfold-exact-c-2026-09-17/`. The three j=2 levels are
exported with the same `export.py` (one seed per single-seed closure class,
followed by the lifted automorphisms) as `inst12j2_law8.txt`,
`inst12j2_law6a.txt` and `inst12j2_law6b.txt` here. The 21 wide levels of §4
are re-exported on the fly by `sweep_wide.py` into `wide/`, which is not
kept.

On inst24a and inst24b, `deep ∈ {5, 6}`, so a 5-seed witness decides (O).

This is not the whole open list. The `j = 1` census
(`census_cayley24_j1_cap3.txt`) also leaves six levels with `law ≥ 8` at
`deep ≥ 4` only (`V = 8n ≤ 192`):

- `(0,1,3,2),(1,2,3,0)`, `n = 24`, law 8;
- `(0,2,3,1),(1,2,0,3)`, `n = 12`, law 8;
- `(0,2,3,1),(1,2,3,0)`, `n = 24`, law 8;
- `(1,2,3,0),(0,3,1,2)`, `n = 24`, law 12;
- `(0,2,1,4,3),(1,2,3,0,4)`, `n = 20`, law 10;
- `(0,2,3,4,1),(1,2,4,3,0)`, `n = 20`, law 10.

§3b treats the smallest of them, which has `V = 96`.
The j=2 levels have the widest known gaps, up to `8` versus `3`.

## 2. Solver `deep5.c`

`deep5.c` is a parallel (OpenMP) rewrite of the w17 solver `deep.c`, using
the same instance format (`export.py`) and the same search.

- The search is a breadth-first search over fold-closed partitions of
  `Γ_{j+1}(Q)`. Each state is canonicalised under the lifted automorphisms
  of `Q`. Level `k` holds every closure of at most `k` seeds, one seed per
  single-seed closure class.
- It is complete: every set of `k` merges has the same fold-closure as some
  path of `k` single-seed closures. Symmetric states have equal depth, so the
  quotient loses no candidates.
- The goal test asks whether `ker(m) ⊆` the closure, i.e. whether every
  `m`-fibre lies inside one block.
- New in `deep5.c`:
  - closures and canonical forms are computed in parallel, in chunks of 4096
    states;
  - the last level is only tested, never stored;
  - each stored state records its provenance (parent, seed, automorphism).
    On a goal, the chain is unwound into literal seed pairs of the original
    `Γ_{j+1}(Q)`, each flagged lawful or overfold. The literal seed set is
    then rechecked from the discrete partition (`RECHECK ... YES/NO`).

**Validation.**

- On the order-12 level `inst12.txt`, cap 4 gives level sizes
  `12 / 828 / 30595` and 4405680 level-4 extensions
  (`validate_inst12_cap4.txt`). This is the same as `deep.c`
  (`experiments/fpbs-overfold-exact-c-2026-09-17/run12_j1_cap5.txt`).
- Lawful-only mode reaches its goal at exactly `law = 6` there, with the
  recheck `YES` (`validate_inst12_law.txt`).
- Lawful-only mode gives `law = 8, 6, 6` on the three j=2 instances, all
  with the recheck `YES` (`law_j2.txt`). This matches the w17 census.

**Low-memory variant `deep5fp.c`.** The machine is shared, and the first
inst24a cap-5 run of `deep5` was OOM-killed at 87% of level 5
(`run24a_cap5_oomkilled.txt`). A second `deep5` run, with the hash load
factor raised from 1/2 to 3/4, was stopped by hand after level 3 because
less than 2 GB was free (`run24a_cap5_deep5_stopped.txt`).

- `deep5fp` keeps the last stored level (`maxlevel − 1`) as 128-bit
  fingerprints, made of two independent 64-bit hashes, plus provenance. This
  is 28 bytes per slot instead of `V + 12`.
- When that level is expanded, each state is rebuilt exactly as
  `canon(closure(parent, seed))`, the same deterministic computation that
  produced it. So the expansion is identical to `deep5`'s.
- The only possible deviation is a fingerprint collision between two
  distinct states. That would drop one of them, with probability about
  `N²/2^129 < 10^-24` for `N ≈ 10^7`.
- It reproduces `deep5` exactly on `inst12` in two runs:
  - cap 4 with all seeds, where level 3, the rebuilt level, has the same
    level sizes and extension count;
  - lawful-only cap 6, with the same `law = 6` witness and recheck `YES`,
    unwound through the fingerprint level.

  The outputs are `validate_fp_inst12_cap4.txt` and
  `validate_fp_inst12_law.txt`. Each differs from its `deep5` counterpart
  only in the thread count on the header line.

## 3. inst24a and inst24b at cap 5 (exhaustive)

Both levels have 288 seed representatives (one per single-seed closure
class) and 24 lifted automorphisms.

| instance | level 1 | level 2 | level 3 | level 4 | level-5 extensions | goal within 5 | so |
|---|---|---|---|---|---|---|---|
| inst24a | 12 | 1704 | 142,906 | 8,777,155 | 2,527,820,640 | **no** | `deep = 6 = law` |
| inst24b | 12 | 1704 | 142,906 | 8,777,114 | 2,527,808,832 | **no** | `deep = 6 = law` |

**inst24a** (`run24a_cap5.txt`, `deep5fp`, about 90 minutes on 4 shared
cores):

- Every closure of at most 5 seeds was tested, and none contains `ker m`.
  So `deep ≥ 6`, and with `deep ≤ law = 6` this gives `deep = law`. (O)
  holds on inst24a.
- The level-5 extension count is exactly `8,777,155 × 288`, so every stored
  level-4 state was expanded.
- **No fingerprint loss.** The OOM-killed full-key `deep5` run
  (`run24a_cap5_oomkilled.txt`) stored exactly `8,777,155` level-4 states,
  the same number as the fingerprint set. A collision could only lower that
  count, so the fingerprints are injective on this level and the search is
  exact, not merely correct with high probability.
- Before it was killed, that run had covered 7,606,272 of the 8,777,155
  level-4 states (87%) at level 5 with no goal, which is consistent.

**inst24b** (`run24b_cap5.txt`, `deep5fp`, about 50 minutes):

- No closure of at most 5 seeds contains `ker m`. So `deep = 6 = law`, and
  (O) holds on inst24b.
- The level-5 count is exactly `8,777,114 × 288`.
- The fingerprint check is `run24b_fullkey_level4.txt`: a full-key `deep5`
  run, stopped once its level 4 was stored. It stored exactly `8,777,114`
  level-4 states, the same as the fingerprint set, so here too the
  fingerprints are injective and the search is exact.

**Consequence.**

- All three `j = 1` census levels with `law = 6` (inst12 from w17, and
  inst24a and inst24b here) have `deep = law = 6`.
- Every `j = 1` census level with `law ≤ 6` is now decided, with
  `deep = law`.
- Still open exhaustively:
  - the six `j = 1` levels with `law ≥ 8` listed in §1;
  - the three `j = 2`, `V = 240` levels, where only `deep ≥ 3` is known.

## 3b. The `j = 1`, law-8 level of `(0,2,3,1),(1,2,0,3)` at cap 6 (exhaustive)

This is the smallest of the six open `law ≥ 8` levels: `n = 12`, `V = 96`,
144 seed representatives, and 12 lifted automorphisms. It is exported as
`inst12j1_law8.txt`.

- **`law = 8` exactly.** The lawful-only `deep5` search reaches the goal at
  level 8, with recheck `YES` (`law12j1_law8.txt`). This agrees with the
  census.
- **Exhaustive search to 6 seeds** (`run12j1law8_cap6.txt`, `deep5fp`):

  | level | 1 | 2 | 3 | 4 | 5 | level-6 extensions |
  |---|---|---|---|---|---|---|
  | states | 12 | 806 | 30,655 | 795,082 | 14,630,853 | 2,106,842,832 |

  No goal is reached within 6 seeds. So `deep ≥ 7`, up from the census
  bound `deep ≥ 4`, against `law = 8`. The level-6 count is exactly
  `14,630,853 × 144`.
- **Fingerprints injective.** A full-key `deep5` run, stopped after level 5
  (`run12j1law8_fullkey_level5.txt`), stores the same `14,630,853` states,
  so the result is exact.
- **Beam, heuristic.**
  - At `B = 20000` (`beam12j1law8_B20000_r1.txt`) the goal is reached at
    `8 = law`, with a witness of 4 overfold + 4 lawful seeds (recheck
    `YES`). The minimum defect is `8` at level 7, the same as along the
    lawful path.
  - At `B = 10^6` (`beam12j1law8_B1e6_r2.txt`), levels 1–4 are not
    truncated, so their minimum defects `53, 45, 38, 30` and the level-5
    minimum `23` are exact. The beam then reaches `15` and `8` at levels 6
    and 7, and the goal at `8 = law`, with 5 overfold + 3 lawful seeds
    (recheck `YES`).
  - No beam state at level 7 is within one seed of the goal.
- Only `deep = 7` would be a counterexample to (O) here. Exhaustive cap 7
  is out of reach on this shared machine. Level 6 would have to be stored:
  on the order of `10^8` canonical states and several GB even as
  fingerprints, followed by about `10^10` closures.

## 4. Beam search on the j=2 levels (heuristic, not exhaustive)

`beam.c` (compiled as `beam`, and as `beamw` with `-DWIDE` for `V ≤ 512`)
keeps, at each level, the `B` distinct canonical states of smallest kernel
defect. The kernel defect is `Σ_fibres (#blocks meeting the fibre − 1)`,
which is `0` exactly at the goal. Ties are broken by a seeded random key.
A goal is always rechecked on the literal seed set. Beam results give
upper bounds on `deep`, never lower bounds.

- **The three j=2 levels with `V = 240`** (all seeds, `B = 2000`): the beam
  reaches the goal at exactly `law` (8, 6, 6), and every witness is lawful.
  On j2law8 the defect falls `144 → 128 → 108 → 92 → 72 → 56 → 36 → 20 → 0`.
- **The 21 j=2 Cayley levels with `V > 256`** that the w17 census skipped
  (`sweep_wide.py`, output `sweep_wide_B1000.txt`):
  - `law` comes from a lawful-only beam of width `10^6`. It never
    truncated, so all 21 values of `law` are exact, with recheck `YES`.
    Values: `law = 4` (3 levels), `5` (7), `6` (4), `8` (3), `10` (2),
    `12` (2).
  - The all-seed beam (`B = 1000`, rng 1) found no witness below `law` on any
    of the 21 levels. The witness it returned at `law` used 0 overfold seeds
    every time.
  - So there is no counterexample among the easy targets. The beam is
    heuristic, so (O) is not decided on these levels.

## 5. Forcing overfold seeds: witnesses and the (O-step) obstruction

`beam ... force` bans lawful seeds at level 1, so every witness contains an
overfold seed. On j2law8:

- Level 1 overfold-only keeps the defect at `144`, as Lemma A predicts:
  a single overfold seed merges no lawful pair.
- From level 2 on, the defect follows the lawful path (`108` at level 2).
  The goal is reached at `8 = law` (rngs 1, 2 and 3, `B = 2000`), with
  witnesses of **6 overfold + 2 lawful** seeds, both with recheck `YES`
  (`wit_j2law8_force_r1.txt`, `force_j2law8_r2.txt`).
- So overfold seeds can replace lawful seeds one for one, but on this level
  they never beat `law`.

**`lcheck.c`: exact `ℓ` over all subsets.** For a seed set `P`, `ℓ(P)` is
the least number of lawful seeds whose closure contains `cl(P) ∩ ker m`
(w17-follow). `lcheck` computes `ℓ` exactly for every subset of a given
set of at most 16 seeds. It uses a breadth-first search over the lawful
single-seed closure classes with no symmetry reduction, because the target
is not invariant. It then tests:

- (O-rel): `ℓ(P) ≤ |P|`;
- (O-step): some `s ∈ P` has `ℓ(P) ≤ ℓ(P−s) + 1`;
- (O-pair), new: some `s` has `ℓ(P) ≤ ℓ(P−s) + 1`, or some pair `{s,t}` has
  `ℓ(P) ≤ ℓ(P−s−t) + 2`.

(O-pair) still implies (O-rel) by induction on `|P|`, using `ℓ({s}) ≤ 1`.

`repcheck.py` confirms that the instance's 12 lawful representatives are
all 12 nontrivial lawful single-seed closure classes. So the search is
complete and `ℓ` is exact.

| witness | subsets | O-rel viol. | max `ℓ(P) − ‖P‖` | O-step viol. | O-pair viol. | `ℓ(overfold part)` |
|---|---|---|---|---|---|---|
| `wit_j2law8_force_r1` | 256 | 0 | 0 | 7 | 0 | 6 (6 seeds) |
| `wit_j2law8_force_r2` | 256 | 0 | 0 | 7 | 0 | 6 (6 seeds) |
| `wit_j2law8_force_r3` | 256 | 0 | 0 | 7 | 0 | 6 (6 seeds) |

Files: `lcheck_j2law8_force_r{1,2,3}.txt`; the beam logs are
`force_j2law8_r{2,3}.txt`.

On j2law6a and j2law6b the forced beam (`B = 2000`) finds no goal within
`6 = law` seeds. It stalls at defect 32 (`force_j2law6a_r1.txt`,
`force_j2law6b_r1.txt`). This is heuristic evidence that an overfold first
seed costs extra there.

**(O-step) is false (a counterexample, checked twice).** On j2law8, the
Cayley level of `(0,2,3,1),(1,2,0,3)` at `j = 2` (`V = 240`, `law = 8`),
take the overfold seeds `s = (9, 80)` and `t = (215, 58)`. They lie over
different vertices of `Q` (6 and 9).

- `ℓ({s}) = ℓ({t}) = 0`, since `cl(s) ∩ ker m` is discrete. This is Lemma A.
- `ℓ({s,t}) = 2`:
  - none of the 192 lawful pairs `(u, v)` with `m(u) = m(v)` covers
    `cl({s,t}) ∩ ker m` on its own;
  - the two lawful seeds `(2, 69)` and `(2, 133)` do cover it.
- So `ℓ(P) ≤ ℓ(P − x) + 1` fails for both `x ∈ P = {s,t}`.

The same holds for `(3,34),(28,51)` and for `(10,99),(153,160)`. This is
checked by `lcheck` and, independently, by `ostep_verify.py`, a separate
Python union-find fold closure that tests every lawful pair, not only the
representatives (`ostep_verify_j2law8.txt`).

The mechanism is general. Two overfold seeds, each inert on its own by
Lemma A, can together close up a lawful pair, and that lawful pair can
need two lawful seeds to cover. In the r2 witness, the pair
`(65,128),(123,128)` shares the endpoint `128`.

- Any proof of (O) by adding one seed at a time with a one-seed budget
  (exchange or matroid-type induction on `|P|` through `ℓ`) must fail:
  the budget is broken after two steps.
- The induction has to add overfold seeds two at a time, or charge a pair
  2 at once.
- On both witnesses the 6 overfold seeds split into three such pairs, each
  with `ℓ = 2`. The largest drop `ℓ(P) − ℓ(P−A)` is `2|A|` for `|A| ≤ 3`
  (`jumps` line), so `ℓ` is not 1-Lipschitz in `|P|`.

**(O-rel) survives, tightly.**

- It holds on all 256 subsets of each of the three forced witnesses, and in
  the exhaustive runs of §6.
- `ℓ = |P|` is attained, for example by the 6-overfold part and by the full
  8-seed witness.
- An adversarial climb (`lcheck ... climb k iters rng`) maximises `ℓ(P)`
  over sets of `k` overfold representatives by random replacement.
  - It ran for `k = 2..8` and `k = 10`, 4000 iterations and 3 rngs each
    (`climb_j2law8.txt`).
  - It found at best `ℓ = k − 1`. At `k = 10` it covers the whole kernel,
    so `ℓ = law = 8`.
  - It is a weaker adversary than the forced beam, which reaches
    `ℓ = |P|`.

## 6. Exhaustive `ℓ` on all seed sets of size ≤ 3 (j=2, `V = 240`)

`lcheck inst pairs` enumerates every single seed representative and every
unordered pair of representatives: 12 lawful and 1044 overfold, so 558,096
sets. `lcheck inst triples` enumerates every triple of overfold
representatives. The first seed is taken up to the 12 lifted automorphisms,
which preserve `m` and hence `ℓ`, giving 87 orbit representatives. That is
47,276,061 triples.

| level | `P` | `ℓ = 0` | `ℓ = 1` | `ℓ = 2` | `ℓ ≥ 3` | O-rel viol. | O-step viol. |
|---|---|---|---|---|---|---|---|
| j2law8 | 1 overfold | 1044 | 0 | 0 | 0 | 0 | 0 |
| j2law8 | 2 overfold | 542,502 | 1836 | **108** | 0 | 0 | **108** |
| j2law8 | 1 lawful + 1 overfold | 0 | 12,528 | 0 | 0 | 0 | 0 |
| j2law8 | 2 lawful | 0 | 0 | 66 | 0 | 0 | 0 |
| j2law8 | 3 overfold | 46,755,494 | 487,566 | 33,001 | **0** | 0 | **3219** |
| j2law6a | 2 overfold | 542,610 | 1836 | 0 | 0 | 0 | 0 |
| j2law6a | 3 overfold | 46,784,379 | 490,647 | 1035 | 0 | 0 | 0 |
| j2law6b | 2 overfold | 542,610 | 1836 | 0 | 0 | 0 | 0 |
| j2law6b | 3 overfold | 46,785,057 | 488,574 | 2430 | 0 | 0 | **531** |

On j2law6a and j2law6b, the single-seed rows and the lawful rows are the
same as on j2law8. Files: `pairs_j2law8.txt`, `pairs_j2law6a.txt`,
`pairs_j2law6b.txt`, `triples_j2law8.txt`, `triples_j2law6a.txt`,
`triples_j2law6b.txt`.

What this shows:

- **(O-rel) holds exhaustively for `|P| ≤ 2` on all three levels, and for
  overfold-only `|P| = 3`.** For overfold seeds it is strict:
  `ℓ ≤ |P| − 1` whenever `|P| ≤ 3`. Pairs reach `ℓ = 2` only on j2law8.
- **`ℓ` is not subadditive.** 108 overfold pairs on j2law8 have
  `ℓ({s,t}) = 2 > 0 = ℓ({s}) + ℓ({t})`.
- **Synergy of order three.** 3219 overfold triples on j2law8 and 531 on
  j2law6b have `ℓ(T) = 2` while every sub-pair has `ℓ = 0`.
  - So `ℓ` is not bounded by any sum of pair terms either.
  - On these triples, (O-step) fails, and (O-pair) holds only because
    `ℓ(T) = 2 = ℓ({x}) + 2`.
- **A lawful seed absorbs an overfold seed.** Every pair of one lawful and
  one overfold seed has `ℓ = 1`: together they never produce kernel
  content that a single lawful seed cannot cover. (The covering lawful seed
  need not be the given one.)
- **The data match the conjecture `ℓ(P) ≤ 2⌊|P|/2⌋` for overfold-only `P`.**
  - It is exhaustive for `|P| ≤ 3`.
  - The forced witnesses attain it at `|P| = 4` and `|P| = 6`.
  - It would say that overfold seeds pay for kernel merges only in pairs.
  - It is an observation, not a claim.

## 7. Where it dies, and what survives

**Established here** (each exact, with a complete computation):

1. **(O-step) is false.** On j2law8, the pair of overfold seeds
   `(9,80),(215,58)` has `ℓ = 2`, while each seed alone has `ℓ = 0`. This
   is checked twice, by `lcheck` and by `ostep_verify.py`.
2. **`ℓ` is not subadditive,** and it has order-3 synergies. The counts are
   in the §6 table.
3. **(O-rel) holds** for all `|P| ≤ 2`, and for overfold `|P| = 3`, on the
   three j=2, `V = 240` levels. **(O-pair) holds** on the same sets and on
   all subsets of the three forced witnesses.
4. **(O) holds on inst24a and on inst24b:** `deep = law = 6` on both. So
   every `j = 1` census level with `law ≤ 6` has `deep = law`.
5. **On the `j = 1` law-8 level `(0,2,3,1),(1,2,0,3)`, `deep ≥ 7`** (the
   census had `deep ≥ 4`). So `deep ≥ law − 1` there.

**Heuristic only:** the beam results of §4 and §5, and the climb.

**Dead:**

- The w17-follow step lemma (O-step).
- More generally, every proof of (O) or (O-rel) by one-seed-at-a-time
  induction through `ℓ` with a unit budget, or through subadditivity of `ℓ`
  (matroid-rank or exchange arguments).
- Pair-sum bounds on `ℓ`.

**Survives:**

- (O-rel), with (O-pair) as the replacement step lemma: some `A ⊆ P` with
  `|A| ≤ 2` has `ℓ(P) − ℓ(P − A) ≤ |A|`.
- (O) itself. No counterexample exists on any transitive level decided so
  far.

A counterexample hunt for (O-rel) must use overfold sets with `|P| ≥ 4`.
