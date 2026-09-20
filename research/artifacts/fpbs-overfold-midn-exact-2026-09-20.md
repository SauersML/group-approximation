# Exact mid-n tests of (O) by the overfold-plus-lawful decomposition

Target: `fpbs-mal-overfold-merges-never-help` (O), deep_j(Q) = law_j(Q).
Author lane: swarm-0917-w21-w21-fp-break (census-computation), 2026-09-20.
Code and raw outputs: `experiments/fpbs-overfold-midn-2026-09-17/`.

## 1. The reduction used

Fix a level Q and depth j, in the pullback model of `pb.py` and the
instance format of `experiments/fpbs-overfold-exact-c-2026-09-17/export.py`.
There is one seed per single-seed closure class of same-fibre pairs, and
each seed carries its lawful flag.

Let cl(T) be the fold closure of a seed set T. The goal is cl(T) ⊇ ker m.
The goal is monotone in T. A witness T of size k splits as T = P ⊔ L, with
P overfold and L lawful. Define

    lawneed(X) = min { |L| : L lawful, cl(X ∪ L) ⊇ ker m }.

Then deep_j(Q) < law_j(Q) holds iff there are s >= 1 and an overfold set
|P| = s with

    lawneed(cl(P)) <= law - 1 - s.

The case s = 0 is excluded by the definition of law. Padding a smaller
witness with lawful seeds keeps it a witness, which is why the bound
law - 1 - s suffices.

So, for any smax,

    (no violation for all s <= smax)  and  law <= smax + 1   ==>   deep = law   exactly.

For law > smax + 1 the same run shows that every witness of size law - 1
has at least smax + 1 overfold seeds.

`rel.c` implements this. P[0] runs over one representative per
automorphism orbit of single-seed closures; this is valid because the
closure of a set depends only on the closure classes of its members, and
lifted automorphisms preserve fibres and lawfulness. The other members run
over all later overfold seeds when Aut is trivial, and otherwise over all
other overfold seeds. lawneed is decided by plain enumeration of lawful
B-subsets, or by BFS with state dedupe.

A reported VIOLATION is a literal seed set of size < law reaching the
goal, so it would be an exact counterexample to (O).

Cross-checks:
* On the order-12 Cayley level `inst12.txt`, rel gives law 6 and no
  violation for s <= 3. This agrees with deep.c.
* On a random n = 20, j = 1 law-4 level, rel reports deep = law = 4.
  deep.c independently finds no goal to level 3 and the goal at level 4.

## 2. Results

No run reported a VIOLATION.

### 2.1 Exact deep = law on random transitive levels

Each level Q is given by two uniformly random permutations of [n], kept
when their action is transitive (`midn.py`). A level whose run finishes
all s <= min(smax, law - 1) is certified to have deep = law exactly.

| file | j | n | levels | law histogram | s range | largest single-level test | exact |
|---|---|---|---|---|---|---|---|
| `rand_j1_n20.txt` | 1 | 20 | 300 | 2:3, 3:228, 4:67, 5:2 | s <= law-1 | 94,966,795 P's with s = 4 (each law-5 level) | 300/300 |
| `rand_j1_n30.txt` | 1 | 30 | 5 (run stopped for CPU) | 4:5 | s <= 3 | 5,935,160 P's with s = 3 | 5/5 |
| `rand_j2_n12.txt` | 2 | 12 | 40 | 2:25, 3:13, 4:2 | s <= law-1 | 189,104,244 P's with s = 3 (each law-4 level) | 40/40 |

For scale: the earlier random `smallk.py` census at j = 1 used n = 14.
Here the certified levels reach law 5, and the witness space tested runs
to about 10^8 sets per level.

**Structured levels: PSL(2,p) on the projective line** (`struct_midn.py
psl`, Q = P^1(F_p), a and b random Moebius maps, j = 1). Law
distributions from the first pass:
* p = 13 and p = 19: law 2 to 4;
* p = 23: mostly 4;
* p = 29: 4 (14 levels), 5 (3), 6 (3).

So high law needs structure. Random levels at n <= 30 almost never
exceed 5.

`psl23_j1_law5.txt` holds 30 levels at p = 23 (n = 24, V = 192), with law
histogram 3:3, 4:25, 6:2; it has no law-5 level. The two law-6 levels
were run with s <= 3 (`psl23_j1_law6_s3.txt`). Each has 264 overfold
seeds and trivial lifted Aut, and is clean at every s <= 3, including
3,031,864 P's at s = 3. On these levels, therefore, every 5-seed witness
has at least 4 overfold seeds. The two levels give identical counts and
may be isomorphic.

### 2.2 The w19 law-8 level

The instance is `inst12j1_law8.txt`, copied from local commit
`d011e9593c` of lane w19; it is not on origin/main. It has V = 96,
n = 12, 144 seeds (12 lawful, 132 overfold), 12 lifted automorphisms and
11 overfold orbit representatives. Its law is 8. w19 showed deep >= 7 by
an exhaustive level-6 BFS, so the only open case is deep = 7. That case
needs a 7-seed witness with s >= 1 overfold seeds and 7 - s lawful seeds.

`rel inst12j1_law8.txt 5 0 fast part 4` was run in 4 parts:

| s | P's tested (sum over the 4 parts) | parts | violations |
|---|---|---|---|
| 1 | 11 (= the 11 orbit reps) | 4 + 2 + 4 + 1 | 0 |
| 2 | 1,441 | 524 + 262 + 524 + 131 | 0 |
| 3 | 93,665 | 34,060 + 17,030 + 34,060 + 8,515 | 0 |
| 4 | 4,027,595 | 1,464,580 + 732,290 + 1,464,580 + 366,145 | 0 |
| 5 | 128,883,040 (= 11 * C(131,4)) | part 3 of 4 (`law8_s5_p3.txt`) + parts 0,1,2,4,5,6 of 8 (`law8_s5_q*.txt`, `run_law8_s5.sh`) | 0 |

Parts 0-2 of the 4-way split were stopped after s = 4. Part 3 finished
s = 5; it covered P[0] indices r ≡ 3 mod 4. The 8-way rerun covers the
residues r mod 8 in {0,1,2,4,5,6}. Together these are all 11 reps
(rep counts per file: 1 + 2,1,2,2,1,2), and each rep gives C(131,4)
P's at s = 5.

The lawful seed count is NL = 12 <= 14, so lawneed is decided by exact
enumeration of lawful subsets of the relevant size, not by the capped BFS.
The counts match the orbit bookkeeping: each rep contributes C(131, s-1)
P's.

**Consequence (certified computation).** On `inst12j1_law8`, every seed
set of size 7 that reaches the goal has at least 6 overfold seeds, so at
most 1 lawful one. With w19's deep >= 7, a counterexample deep = 7 < 8 on
this level must be a 7-set with at most 1 lawful seed.

This squeezes the w19 lead from the other side. w19's beam search found
law-8 witnesses with many overfold seeds. The present run shows that
overfold seeds cannot be mixed with lawful ones in small numbers to beat
the law. The only surviving shapes are almost purely overfold. A search
for deep = 7 can therefore be confined to two cases:
* 6 overfold seeds plus 1 lawful seed;
* 7 overfold seeds alone.

Running `rel` at s = 6 and s = 7 decides deep on this level exactly.
After the orbit reduction that is 11 * C(131, s-1) P's per s: about
3.3 * 10^9 at s = 6 (12 lawful completions each) and 6.9 * 10^10 at
s = 7 (one closure each). At the measured rate of about 1.2 * 10^4 P's
per CPU-second at s = 5, s = 6 needs at most about 3 CPU-days and s = 7
at most about 2 CPU-months. These are upper bounds, since there are fewer
lawful completions per P at larger s. So s = 6 is feasible for a dedicated run; s = 7 would need
a better pruning, for example a class-count bound.

### 2.3 Observations on the saving

In exact mode on `inst12.txt` (law 6), one overfold seed never lowers
lawneed at all (ell = 0). For |P| <= 3 the saving obeys
ell = law - lawneed(cl(P)) <= |P| - 1. The fast-mode runs record only
the bin "saving <= 0", i.e. lawneed(cl(P)) >= law - |P|, and every tested
P landed in it.

### 2.4 Annealing calibration (heuristic, not used for any claim)

`anneal.c` minimizes the number of merges still missing, over k-seed sets
of all types. On `inst12` (law 6 = deep):
* k = 6: it finds witnesses in 9 of 10 restarts;
* k = 5: in 5 restarts it never gets below 13 missing merges.

So annealing can find size-law witnesses, but its failure at law - 1 is
no certificate. It is recorded only as a tool for future hunts on levels
too large for `rel`.

### 2.5 What this does and does not change

* (O) survives every exact test of this size. The 300 random n = 20
  levels include law-5 levels, where the witness space of size law - 1 is
  far past what the earlier BFS censuses reached.
* The w19 counterexample hunt narrows further; see 2.2.
* Nothing here is a proof, and random levels at these n have small law.
  Belief-changing counterexamples, if they exist, most plausibly sit at
  large law on structured levels, which is where 2.2 points.
