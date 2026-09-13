---
rg: 2
id: pl-interval-and-circle-groups-type-a-orbit-action-proof
kind: route
title: Interval matching gives one pair orbit for F(A,P) and 2-transitivity for T(A,P), with product and interval-group stabilizers
target: pl-interval-and-circle-groups-have-type-a-orbit-actions
requires:
  - pl-rearrangement-groups-have-two-transitive-orbit-actions
  - two-transitive-action-reduces-type-a-to-two-clauses
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target. `0 < q, q' < 1` by (R). We use Lemma 1 (matching) from the
proof of `pl-rearrangement-groups-have-two-transitive-orbit-actions`: for `u, v ∈ A`
and positive `a, b ∈ A` there is an increasing bijection `[u, u+a) → [v, v+b)` with
finitely many pieces `x ↦ px + c`, `p ∈ P`, `c ∈ A`, and breakpoints in `A`. It
extends continuously to the closed intervals, sending endpoints to endpoints.

For `a < b` in `A`, write `F[a,b]` for the increasing piecewise-linear homeomorphisms
of `[a,b]` with breakpoints in `A`, slopes in `P` and constants in `A`.

**Part 1: F(A,P).**

- *Faithful.* Each piece `[x_{i-1}, x_i]` contains the infinitely many points
  `x_{i-1} + (x_i − x_{i-1}) q^k` (`k ≥ 1`) of `A ∩ (0,1)`. An affine map fixing two of
  them is the identity.
- *One orbit of two-element subsets.* Given `x < y` and `x' < y'` in `A ∩ (0,1)`, Lemma 1
  on `[0,x] → [0,x']`, `[x,y] → [x',y']` and `[y,1] → [y',1]` gives `f ∈ F(A,P)` with
  `f(x) = x'` and `f(y) = y'`. The same argument with two intervals gives
  transitivity.
- *Stabilizers.* An element fixing `q'` restricts to elements of `F[0,q']` and
  `F[q',1]`, and any such pair glues to one, so `Stab(q') ≅ F[0,q'] × F[q',1]`. The map
  `x ↦ x/q'` (slope `1/q' ∈ P`) conjugates `F[0,q']` onto `F(A,P)`, and `x ↦ (x − q')/q`
  (slope `1/q ∈ P`, constant `−q'/q ∈ A`) conjugates `F[q',1]` onto `F(A,P)`. By
  transitivity every stabilizer is conjugate to `Stab(q') ≅ F(A,P) × F(A,P)`, which is
  finitely generated whenever `F(A,P)` is.
- *Type (A).* Clauses 1, 3 and 4 hold (clause 3 once `F(A,P)` is finitely generated),
  so the action is of type (A) exactly when clause 2 holds, i.e. `F(A,P)` is finitely
  presented, since that already gives finite generation.

**Part 2: T(A,P).**

- The rotations `r_c` (`c ∈ A ∩ [0,1)`) from that proof induce circle rotations, so they
  lie in `T(A,P)`, and `T(A,P)` is transitive on `A ∩ [0,1)`.
- An element of `T(A,P)` fixing `0` induces a circle homeomorphism fixing the base
  point; as a map of `[0,1)` it is an increasing bijection that is continuous. With
  piecewise-affine pieces and `f(x) → 1` as `x → 1`, it is exactly an element of
  `F(A,P)`. Conversely `F(A,P) ≤ T(A,P)`. So `Stab(0) = F(A,P)`.
- `F(A,P)` is transitive on `A ∩ (0,1)` by Part 1, so `T(A,P)` is 2-transitive on
  `A ∩ [0,1)`. Faithfulness is inherited from `V(A,P)`.
- By `two-transitive-action-reduces-type-a-to-two-clauses`, the action is of type (A)
  exactly when `T(A,P)` is finitely presented and `F(A,P)` is finitely generated.

**Consequences.** Zaremsky's Corollary B, `type-a-action-gives-boone-higman-for-subgroups`,
gives solvable word problem and a finitely presented simple overgroup for every subgroup
of an acting group with a type (A) action. Membership in the permutational class holds by
definition. ∎
