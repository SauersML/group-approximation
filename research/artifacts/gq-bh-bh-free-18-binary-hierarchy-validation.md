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
- Everything after them: one SLURM job at a time.

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
the parentless patterns. The searches so far find no fill that supplies the missing parents on `b`-blocks, but they are not complete
(§6).

## 6. Status of the complete search, and the next step

- **Not decided.** No fill passing the criterion was found among the 500,000 chronological nodes and the 57,000
  backjumping nodes. Every dead leaf in both searches was a `T` failure.
- The learned nogoods stay large: the search depth stays at 8–13 of the 15 free entries. So no small set of free
  rules is contradictory by itself. If an obstruction exists, it is spread over many rules, not local to a few.
- **Caveat.** Returns were capped at 40 steps (hierarchical gaps are 12). A fill with longer junk returns would be
  missed.
- **Next step.** Decide the fill problem with an indexed nogood store (watched facts) or a SAT encoding of the
  local certificate. If no fill exists, change the fixed rules instead: add a letter that marks `b`-runs, so that
  a `b`-block becomes the boundary of a legitimate parent move.

**Lesson for general BH.** The binary wall for `BS(1,2)` in Brin–Thompson hosts is **not** in the hierarchy. A
reversible one-head machine with radius-1 reads realizes an exact binary hierarchy on hierarchical tapes: exact
doubling, bounded gaps, and a radius-1 renormalization `φ U² = U φ`, with no growing control information. That is evidence against the hierarchical form of the conjecture in
`research/artifacts/gq-affq-binary-two-head-design.md`: numerical over 15 levels, plus the hand recursion of the
design; not a proof. What
remains is *completeness*: a height-`m` renormalization forbids periodic points, so every background the machine can
write, including its own counter letters, must restart a hierarchy. For renormalization witnesses (BS, dilation
groups, `Aff(Q)` stepping stones), design the junk first. The hierarchy is the cheap part.
