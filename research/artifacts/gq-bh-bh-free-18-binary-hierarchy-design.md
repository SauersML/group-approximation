# A binary move hierarchy for a one-head reversible machine, and where it still fails (lane bh-free-18, 2026-09-18)

**Status: design notes, no claim.** This artifact records a hand design aimed at `bs12-embeds-in-brin-thompson-2v`
through `renormalizable-thompson-elements-give-baumslag-solitar`, together with its one remaining gap. Nothing here
has been run.

## 1. The type calculus is forced

Work in the SMART paradigm: a move of level `k` crosses or returns over an interior `0^k` between two boundary cells.
Take its interior to be all zeros at the start and at the end of the move. A level-`(k+1)` move is two level-`k`
sub-moves on the interior minus one **extra cell**, plus bounded junctions.

**Cost rules.** If first sub-moves with a start cost could nest, their costs would add up to a walk. The same holds
for last sub-moves with an end cost. So:
- first sub-moves must have zero start cost;
- last sub-moves must have zero end cost.

A crossing has its extra cell next to one of its ends, so it pays at that end. There are two crossing types:
- **E**, which pays at the end (its extra cell is next to its end);
- **S**, which pays at the start (its extra cell is next to its start).

A return **R** puts its extra cell on the far side and pays nothing. By `crossing-move-hierarchies-have-odd-branching`:
- a crossing splits into one crossing and one return;
- a return splits into two crossings or into two returns.

The rules above then leave exactly one substitution:

```text
E -> E R        S -> R S        R -> E S        (and mirror images)
```

This is **not** the Jacobsthal scheme `C -> C R, R -> C' C` of the gq-nv-obstruct search. There the return goes
out and back with the same crossing type. Here it goes out with E and comes back with S.

The leaf counts satisfy `N_E(k+1) = N_E + N_R`, `N_R(k+1) = N_E + N_S`, `N_S(k+1) = N_R + N_S`. So every level-`k`
move has exactly `2^k` leaves.

## 2. The first-junction collision, and how a peek resolves it

**The collision.** Both E and R begin with E. At the end of that first E, the machine stands on a fresh `0` and must
choose between two continuations:
- extend: the parent is E;
- turn: the parent is R.

**The peek resolves it.** Step once more and read the next cell. In the extension case that cell is the parent's end
cell, which is `0`. In the turn case it is R's far boundary, which is a home.

This needs every home to be nonzero, so the parents write their counters as homes: `a` in E-parents and `b` in
S-parents. The alphabet is `{0, a, b}`, with 10 moving states and 10 reading states. Arrows point in the direction
the state moves.

| rule | meaning |
|---|---|
| `A→' 0 → P→` ; `A→' a/b → S←` (keep) | E ended on a fresh cell: peek. A leaf `R_L(0)` hit its far boundary: go back. |
| `P→' 0 → X←` ; `P→' a/b → T←` (keep) | extend ; turn |
| `X←' 0 → write a, A←` | the E-parent's counter; start `R_R` with its home here |
| `T←' 0 → S←`, only if the right neighbour is nonzero | the turn: the return's second half starts |
| `S→' 0 → write b, A→` | the S-parent's counter; start `R_L` |
| `S→' a → write 0, A→` | an `R_R` ended at its home in an E-parent: reset and leave |
| `S→' b → write 0, S←`, only if the right neighbour is `0` | an `R_R` ended at its home in an S-parent: reset and start the last S |
| mirror rules with left neighbours | |

**Checks by hand.**
- On hierarchical configurations the recursions close: `E→(k+1) = E→(k) J1 R_R(k) J2a`, `R_R(k+1) = E←(k) turn S→(k)`,
  and `S→(k+1) = start R_L(k) J2b S→(k)`.
- The leaves are `Y` = {`A` on a nonzero cell} ∪ {`S` on `0` with a nonzero next cell}. Each level-`k` move contains
  exactly `2^k` of them, and the junctions are bounded, so there is no walk.
- The level-1 renormalization table has the same shape as SMART's:
  - at `A→` on a nonzero cell with a `0` to its right, delete that `0`;
  - at `A→` on `b` with a nonzero cell to its right, delete the head cell, move the head left, and change the state to `S→`.

## 3. Reversibility needs a radius-1 read (lesson)

In the one-cell Kari–Ollinger format, "S starts on a `0` cell" has two predecessors:
- the turn, where the cell was `0`;
- an S-parent's reset, where the cell was `b`.

Separating them with states and letters regresses: `r + 1` variants would have to fit into `r` letters. The
neighbour separates them at once:
- after a turn, the right neighbour is R's far boundary, which is nonzero;
- after a reset, it is the S-parent's start cell, which is `0`.

The turn guarantees its own condition on every tape, not only on hierarchical ones: `T←` only ever arrives from a
cell that `P→'` has just read as nonzero. So the matching splits into bijections, one for each value of the
neighbour. There are 20 specified entries out of 30 in each block, and the 10 unused targets can be filled bijectively.

**This is outside every class searched so far.** Those searches used one-cell matchings.

## 4. The gap: completeness

In SMART, every level-`0` move has an infinite chain of parents on **every** tape. Here two local patterns have no
parent:
1. an `E→(k)` with `k ≥ 1` that ends on a nonzero cell;
2. an `R` whose home has a nonzero cell on its far side from the domain.

The first pattern is also reached from the second: after J2a, the head reads the E-parent's end cell. On such tapes
the fill rules take over and the hierarchy breaks. The set of fully hierarchical tapes is closed but not open, so it
cannot simply be discarded.

**What would close the design:** letters and rules that give both patterns a legitimate parent, as SMART_m's `x`/`y`
families do. The first pattern needs E as a non-first sub-move ending on a boundary. The second needs a third role
for R.

After that, the exhaustive local certificate of `research/artifacts/gq-bh-bh-free-18-odd-smart-certificate.md` would
decide the result outright:
- entry and return bounds;
- the tower `Y = A ⊔ UA`;
- the bijection φ;
- `φU² = Uφ`.

A pass would give `BS(1,2) ≤ 3V`.
