import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickEulerReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The global Euler count: the counting step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-41.

`ExtremalJordanPickEulerCountStatement` (lane gl-p10-39) asks for three walk darts that are
pairwise not linked by face classes and first turns.  Its proof has two parts: (a) Euler's
formula on the genus-0 walk map, and (b) a counting step.  This file proves (b) and the planarity
input of (a).  What is left is the count of classes itself.

**The counts.**
* `extremalJordanPickCount_linked K` is the finset of linked classes of walk darts.  `#L` is its
  card.
* `extremalJordanPickCount_outside K` is the finset of face classes of darts outside `K.faces`.
  `#O` is its card.
* `extremalJordanPickCount_nonFirstAt K x` counts the non-first passages at the vertex `x`.  This
  is `n_x`.  The vertex of a passage `d → next d` is `vertexOf (α d)`.
* `extremalJordanPickCount_excess K` is `Σ_x (n_x - 1)`, with truncated subtraction, summed over
  the vertices of the walk.

**Proved here.**
* **Genus 0** (`extremalJordanPickCount_walkMap_planar`, `extremalJordanPickCount_walkMap_euler`).
  The walk map `P` is a connected restriction of the planar diagram map, so `V - E + F = 2` on it.
* **At most two outside classes** (`extremalJordanPickCount_outside_le_two`).  This comes from
  `ExtremalJordanPickThreeTwoOutside`.
* **`excess ≥ 2`** (`extremalJordanPickCount_two_le_excess`).  `¬ K.FirstTurns` gives a non-first
  passage.  The proved local lemma `n_x ≥ 1 ⇒ n_x ≥ 3` then gives `n_x ≥ 3` at its vertex.
* **Extraction** (`extremalJordanPickCount_three_of_two_lt`).  Three linked classes give three
  pairwise unlinked walk darts.
* **The counting step** (`extremalJordanPickCount_count_of_euler`).  Suppose
  `2 + excess ≤ #L + #O` and `#O ≤ 2`, so that `excess ≥ 2`.  Then `#L ≥ 3`, except when
  `excess = 2`, `#O = 2` and `#L = 2`.  The parity clause rules that case out.

**The isolated Statement** `ExtremalJordanPickCountEulerStatement`.  Under the premises of
`ExtremalJordanPickEulerCountStatement`, two things hold:
* `ExtremalJordanPickCountEulerBound K`, which is Euler's bound `2 + excess ≤ #L + #O`;
* `ExtremalJordanPickCountParity K`, which says that `excess = 2 → #O ≠ 2`.

**LOUD (strength).**  The residual is a conjunction of two count facts.  It implies the count
statement (`extremalJordanPickCount_count_of_euler`).  It is NOT implied by it, since the count
statement says nothing about cards.  So as a proposition it is STRONGER than the count statement,
NOT weaker and NOT equivalent.  It is strictly smaller in proof content.
* The counting step, the extraction of three darts, `#O ≤ 2`, `excess ≥ 2` and the planarity of
  the walk map are all proved here.
* Only the count of classes on the planar walk map is left.
* Both clauses are true on every model instance (truth check below).  The bound is the weak half
  of an identity that holds with equality.  The parity clause is the case `excess = 2` of a
  general parity law.

**Truth check** (`SP/gl-p10-41/par.py`, outputs `par_m6.out`, `par_m7.out`, `par_m8b4.out`,
`par_m8b5.out`).  This uses the lane-34 model (`configs_b`): planar walk maps, not all passages
first, and every non-first passage crossed.
* Every instance satisfies the identity `#L + #O = 2 + excess`.
* Every instance satisfies the parity law `#O ≡ 1 + Σ_x (n_x - c_x) (mod 2)`.  Here `c_x` is the
  number of cycles, at `x`, of the return permutation `h` on the non-first passages.
* In the case `excess = 2`, `#O` is 1 or 3 and never 2.
* The count conclusion `#O ≤ 2 → #L ≥ 3` holds in every instance.

| darts | configurations      | `excess = 2`, `#O = 1` | `excess = 2`, `#O = 3` |
|-------|---------------------|------------------------|------------------------|
| ≤ 6   | 9,010               | 274                    | 1,267                  |
| ≤ 7   | 178,196             | 1,275                  | 8,274                  |
| ≤ 8   | 36,394 (degree ≤ 4) | 2,834                  | 11,809                 |
| ≤ 8   | 116,345 (degree ≤ 5)| 4,392                  | 25,536                 |

The naive parity `#O ≡ 1 + excess` fails: 79,453 instances at ≤ 7 darts break it.  So the cycle
count `c_x` is needed.

**Proof sketch of the residual** (not formalized).  The walk map `P` has walk darts and their
reversals.
1. By the proved alternation fact, the rotation at each vertex of `P` alternates between walk
   darts and reversals.  So each face of `P` is inside (all walk darts) or outside (all reversals).
   By `faceOf_eq_of_faceClass` and separation, these faces are the face classes.
2. So `#O` counts the outside faces of `P`.  `#L` counts the inside faces of `P`, glued along first
   passages.
3. Detach first passages one at a time by `PinchSplit` at the corner `(next d, α d)`:
   - at a vertex with `n_x = 0`, detach all passages but one;
   - at a vertex with `n_x ≥ 1`, detach all first passages.

   Each detach adds one vertex and keeps the edge count.  It glues two distinct inside faces,
   because a split of one face would force `χ = 4` on a connected map
   (`witnessStepGenus_split_not_connected`).  The outside faces are unchanged.
4. Euler's formula on the result gives the identity.
5. **Parity.**  Let `f(d) = α (σ_P d)` and `next = h ∘ f⁻¹` on walk darts.  The outside faces are
   the cycles of `f`, and `next` is a single cycle.  Comparing signs gives
   `#O ≡ m + 1 + #cycles(h) (mod 2)`, where `m` is the number of walk darts.
6. With `excess = 2`, one vertex has exactly three non-first passages.  At that vertex `h` is a
   derangement of 3 points, so it is a 3-cycle, and `#O` is odd.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/
