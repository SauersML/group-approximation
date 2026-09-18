# The binary hierarchy machine on MSI: exact doubling on hierarchical tapes, failure on counter-letter junk (lane bh-free-18, 2026-09-18)

**Status: computation report, no claim.** This validates the design in
`research/artifacts/gq-bh-bh-free-18-binary-hierarchy-design.md`, aimed at `bs12-embeds-in-brin-thompson-2v`
through `renormalizable-thompson-elements-give-baumslag-solitar`. The scripts are `binary_hier.py` (machine,
lazy symbolic certificate), `bh_run.py` (driver), `bh_lazy_par.py` and `bh_cbj2.py` (searches over the unspecified
entries), all in the lane's MSI directory.

How the runs were made:
- Validation runs: single-core, seconds each.
- Two brute-force passes (the E scan of §3 and a first criterion scan): 16 processes each, run directly on a shared
  node. That broke the MSI rules, and both were stopped.
- Everything after them: one SLURM job at a time, including the two SAT jobs 1327013 and 1327358 (4 cores, at
  most 30 minutes each).

## 1. What the machine is

- Letters `0, a, b`.
- 10 moving states `A P X T S` × `{→, ←}`.
- Reading rules may consult one neighbour: the right one for the `→`-reading group, the left one for its mirror.
- For each neighbour value, the reading map is a bijection. So the machine is reversible with a local inverse.
- The design fixes 10 rules per neighbour value and leaves 5 of them free. A **fill** is a choice of bijection for
  the free rules, one for each neighbour value: `120^3 = 1,728,000` fills in all.
- The target sets are those of the design (§2 there):
  - `Y` = {`A` on a nonzero cell} ∪ {`S` on `0` with a nonzero next cell};
  - `A ⊆ Y`;
  - `φ` deletes one cell next to the head.

## 2. On hierarchical tapes the design is correct

Runs start from the all-zero tape, for 4·10^5 steps. The table covers 8 of the 10 start states. From `T→` and `T←`,
the default fill runs ballistically and never meets `Y`. That is harmless for the criterion, since `U` lives on `Y`.

| quantity | result |
|---|---|
| `Y`-counts | exactly doubling: `Y = 2^j` is reached at time `≈ 6.67·2^j` |
| maximal gap between visits to `Y` | 12 at every level |
| head range | grows by exactly one cell per level (range `[-17, 2]` after `2^15` visits) |
| tower pattern along the orbit | `A - A - A - …`, strictly alternating |
| `φ U² = U φ` | holds at all 4,494 `A`-points of the orbit from `A→` |

**One correction to the design.** The `b`-branch of `A` must require a `0` behind the `b`:
`A→` on `b` is in `A` only if the left neighbour is `0`, and mirrored for `A←`. Without that condition, the check
`φ(A) ⊆ Y` fails on 8 local patterns. With it, the exhaustive checks `P` and `P⁻¹` pass.

## 3. Exhaustive local certificate (all configurations, symbolic unread cells)

**Fill-independent checks.**
- `R` (reversibility): PASS.
- `P`, `P⁻¹`: PASS.

**Global entry bound E (every configuration enters `Y` within 40 steps).** It fails for every fill scanned:
- all 14,400 mirror-symmetric fills (`π_1 = π_2`);
- 1,008,000 of the 1,728,000 fills (a brute-force pass, stopped partway).

For the default fill, every failing configuration uses at least one free rule. E is **not** needed by the renormalization criterion
(`U` only has to be defined on the clopen set `Y`), so it was dropped from the criterion search.

**Criterion checks with the default fill.** The checks are:
- `T`: `U y ∉ A` and `U² y ∈ A` for `y ∈ A`;
- `C2`: exactly one of `z`, `U⁻¹ z` lies in `A`;
- `I`: `φ U² = U φ`;
- returns in both directions capped at 40.

`T` fails on 7,276 local patterns. The first ones are long `b`-blocks: `b^7 0 [A→ on b] b b`, where the return
exceeds 40 steps or `U² y ∉ A`.

## 4. Search over all fills for the criterion (R, T, C2, P, P⁻¹, I)

**Calibration.** On the default fill, the lazy searcher and the direct certificate give the same verdict (`T`).

**SLURM job 1322168.** Lazy chronological backtracking: an entry is branched on only when a certificate computation
consults it.
- 500,000 nodes.
- 108,982 dead leaves, **all dead at `T`**.
- No fill passes.
- Incomplete: 1,529 subtrees were left unexplored because of thrashing on entries irrelevant to the failure.

**SLURM job 1325378.** Complete search with conflict-directed backjumping and a store of learned nogoods. A failure
nogood is the exact set of free-rule facts that the failing computation consulted.
- Cancelled by the lane at 57,000 nodes (415 s), because the learned-nogood store (29,454 entries) made each node
  slower. No fill passed. The search is incomplete (§6).

## 5. Where it fails, and what that means

The first failing patterns contain long blocks of the counter letter `b`. Whether the hierarchical orbits ever
contain such blocks was not checked.

On those blocks the head's behaviour is decided entirely by the free rules:
- `A→` on `b` turns into `S←`;
- `S←` on `b` next to `b` is a free rule.

The criterion needs `U` to return within bounded time on **every** such pattern, and to alternate `A`/`non-A`.
It also needs `U` to have **no periodic point at all**: a periodic point of period `p` in `A` gives, through `φ`, one
of period `p/2`, and so on down. So on the `b`-background the machine must *start a hierarchy of its own*, exactly
as it does on the `0`-background.

That is the ballistic-machine lesson (`ballistic-machine-runs-give-periodic-points`) in a sharper form:
**every letter a counter writes is itself a background the machine must turn on.**

In SMART_m this is paid for by completeness. On every tape, every level-0 move has an infinite chain of parent
moves, and every nonzero letter can serve as a move boundary. The binary design lacks exactly this: its §4 lists
the parentless patterns. §6 shows that no fill supplies the missing parents.

## 6. Complete decision: no fill works (SLURM job 1327013)

**The encoding.** The search is a lazy SAT encoding, run as a counterexample-guided loop (`bh_sat.py`).
- *Variables:* the 15 free positions, each an output, all different for each neighbour value.
- *Clauses:* nogoods. A nogood is the set of free-rule facts `(neighbour, input, output)` that one failing
  certificate computation consulted. That computation is deterministic given those facts, so it fails for **every**
  fill containing them.
- *Search:* one DFS over the fill tree:
  - every assignment is checked against the clauses indexed by its fact;
  - clauses added later are rechecked against the prefix whenever a level resumes, which gives backjumping;
  - the certificate runs only at full fills that survive;
  - each failure adds the subset-minimal nogoods of **all** failing configurations of the first failing check.
- The search is complete.

**Calibrations (same job).**
1. *Planted negative:* the check `P` with the uncorrected `A` of §2. Verdict UNSAT on the first leaf, with an empty
   nogood, as it must be: that failure does not depend on the fill.
2. *Hierarchical tapes:* the check is the tower and `φ U² = U φ` at every `A`-point of the zero-tape orbits (3,000
   steps from each of 8 states), with the DFS value order reversed so that the default fill comes last. Verdict SAT on
   the first leaf. These orbits consult **no** free rule at all: the hierarchy runs entirely on the 10 fixed rules.
3. *Soundness:* random completions of 10 learned nogoods. All 10 fail again.

**Result.** Verdict **UNSAT** for the full criterion (R, T, C2, P, P⁻¹, I, with returns capped at 40).
- 188 fills were evaluated and 376 nogoods learned, eliminating all 1,728,000 fills in 287 s.
- Nogood sizes: 10 of size 1, 38 of size 2, 78 of size 3, 130 of size 4, 96 of size 5, 24 of size 6.
- The smallest nogoods are single facts: with a nonzero right neighbour, `S→` reading `b` must not continue as `X←`.
  The fixed rule covers only a `0` there, the case "an `R_R` ended at its home in an S-parent". This looks like
  pattern 2 of the design's §4 (an `R` whose home has a nonzero cell beyond it), but that was read off by hand, not
  checked.
- **Correction.** An earlier draft of this section inferred "no small set of free rules is contradictory" from
  search depths of 8–13. That was wrong: depth is not nogood size, and single facts are already fatal.

**Scope.** The result holds for this rule format:
- 3 letters, radius-1 reads;
- the 10 fixed rules per neighbour value;
- `Y`, `A` and `φ` as in §1;
- returns of at most 40 steps. Hierarchical gaps are 12. A fill whose junk returns are longer than 40 steps is not
  excluded.

Within that scope, the fixed rules must change: completing them is impossible.

## 7. A fourth letter as a marker (SLURM job 1327358): undecided

**The machine.** The fixed rules stay, and a fourth letter `c` counts as nonzero. Every rule that reads `c`, or whose
neighbour is `c`, is free (`bh4_sat.py`). Each neighbour value now has 10 free inputs mapping bijectively onto 10
free outputs, 5 of which write `c`, giving `(10!)^4 ≈ 1.7·10^26` fills. This is the most general marker the rule
format allows. For example, "write `c` on a `b`-run" is one fill.

**Seeding.** Every 3-letter nogood transfers unchanged: its failing tape contains no `c`, and it consults the same
rules. So the search starts from the 376 clauses of §6, which job 1327358 recomputed and matched exactly.
Consequence: a working marker must be written by one of the old free inputs, on the old junk.

**Calibrations (same job).**
- planted: UNSAT at once;
- zero-tape orbits: SAT on the first leaf;
- soundness: random completions of 6 transferred and 8 learned nogoods all fail again.

**Result: TIMEOUT after 1,150 s, so undecided.**
- 3,464 fills were evaluated and 8,499 nogoods learned; no fill passed.
- The learned nogoods are large: most have 8–11 facts, out of 40 variables. So in this search the failures on
  marker junk are spread over many rules, not concentrated in a few.
- Deciding this space needs a stronger solver (a real CDCL encoding of the local certificate) or a hand-designed
  marker, not more of this loop.

**Lesson for general BH.** The binary wall for `BS(1,2)` in Brin–Thompson hosts is not the hierarchy. It is
*completeness*, and completeness can now be decided.

What works:
- A reversible one-head machine with radius-1 reads runs an exact binary hierarchy on its fixed rules alone. The
  zero-tape orbits consult no free rule.
- On those orbits it has exact doubling, gap 12 and `φ U² = U φ`, checked over 15 levels.
- That is evidence against the growing-control-information conjecture of
  `research/artifacts/gq-affq-binary-two-head-design.md`. It is numerical, not a proof.

What fails:
- A height-`m` renormalization forbids periodic points. So every background the machine can write, including its own
  counter letters, must restart a hierarchy.
- A lazy SAT encoding of the local certificate proves that no completion of this rule table does that (§6).

The transferable method:
- freeze the hierarchy rules and leave the junk rules free;
- decide the junk by learning clauses from the rule facts each failing computation consulted;
- carry the clauses over unchanged to every alphabet extension (§7).

For renormalization witnesses (BS, dilation groups, `Aff(Q)` stepping stones), design the junk first. The hierarchy
is the cheap part.
