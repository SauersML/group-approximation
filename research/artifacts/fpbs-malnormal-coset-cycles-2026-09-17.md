# Coset cycles over a malnormal free stage

Supporting notes for `fpbs-malnormal-coset-cycles-bounded-syllables`.

## 1. Why this is the right question

Detour-packing repair works like this. Keep the new generator `t` on a random
set `U`. At a point `x`, rebuild the `t`-edge through a detour whose `t`-edges
all start in `U`. It proves `relC(E_F; E_H) = 0` when there are infinitely
many disjoint detours with a bounded number of `t`-edges each (artifact
`research/artifacts/fpbs/small-cancellation-family.md` (2.4), where `N(R)` is
infinite for a finite `R`). The alternative is superexponential packing growth
(its (2.5) with `h = infinity`).

If this held over the stage pair `(F_2, <a, b a b^{-2}>)` of `Gamma_mal`, the
stagewise bound `C <= 2 + sum_n relC_n` would give fixed price for
`Gamma_mal`. The conjugation trick is unavailable there because the stages are
malnormal. The infinite-contact criterion is unavailable because it needs a
finite-cost graphing, which makes it circular for this purpose.

## 2. Stallings graph of `H = <a, b a b^{-2}>`

The loop `b a b^{-1} b^{-1}` folds, at the base vertex, the two outgoing
`b`-edges. The folded based graph has 3 vertices: `a: 0->0`, `b: 0->1`,
`a: 1->2`, `b: 1->2`. So `m = 3` and `D = 9`.

## 3. Computation

`experiments/locally-free-finite-cost-2026-09-17/coset_cycles.py` enumerates
closed coset-graph words with `k` `b`-edges and pairwise distinct vertex
cosets. It searches syllables of generator length at most `L`.

    k=2 L=6 cycles=2 max|h|=0 bound=10
    k=3 L=3 cycles=6 max|h|=4 bound=19
    k=3 L=4 cycles=6 max|h|=4 bound=19

- **`k = 2`.** The two solutions are the backtracking pairs `b B` and `B b`.
  The script does not exclude repeated edges, and these are not simple cycles.
  Malnormality leaves no genuine 2-cycle.
- **`k = 3`.** The count is stable as `L` grows. The six solutions are the
  triangle `T(u) = {e(u), e(bu), e(au)}` from `ba = c b^2`, read from its three
  starting edges in two orientations. The largest syllable is `c` (length 4),
  well inside the proven bound.

## 4. What remains

The syllable bound makes a simple cycle's total length `O(k^2)`. That allows
`exp(O(k^2))` cycles, so this route does not show that the packing growth rate
`h` is finite.

On a line, intervals with pairwise overlaps at most `D` have total length at
most `2 * span + 2kD`: at each point only two long intervals can pass. If the
same linear bound held for tree polygons, the count would be
`exp(O(k (D + |t|)))`. Then `h < infinity`, and detour packing would give at
most `relC <= exp(-h) > 0`. That would end the whole detour-packing class at
malnormal stages.

In a tree, however, many long sides can pass through a short common star
region, so the line argument does not transfer directly. This linear bound is
the precise open step.
