---
rg: 2
id: hyde-lodha-periodic-simple-groups-are-not-amenable-proof
kind: route
title: Proof that Hyde–Lodha's periodic simple group Q_2 is not amenable
target: hyde-lodha-periodic-simple-groups-are-not-amenable
requires: []
artifacts:
  - GroupApproximation/GroupTheory/HydeLodha/GammaTwoCoreMoves.lean
  - GroupApproximation/GroupTheory/HydeLodha/GammaTwoLambda.lean
  - GroupApproximation/GroupTheory/HydeLodha/GammaTwoPeriodic.lean
---

Suppose `Q_2` is amenable. Write `x·f` or `f(x)` for the action; only monotonicity is
used, so the side convention does not matter.

1. **The circle action.** Every `f ∈ Γ_2` commutes with `τ(t) = t + 1`
   (Definition 1.2), so it induces a homeomorphism `f̄` of `S^1 = R/Z`, and `f -> f̄`
   is a homomorphism. `Q_2` acts continuously on the compact space `S^1`, so by
   amenability there is a `Q_2`-invariant Borel probability measure `mu` on `S^1`.
   Identify `S^1 \ {0̄}` with the open interval `(0, 1)`.
2. **Compression inside `(0, 1)`.** Let `0 < a < b < 1`.
   - The subgroup `5Z[1/6]` is dense in `R`, so each residue class of `Z[1/6]` modulo
     `5Z[1/6]` is dense. Choose `q ∈ Z[1/6] ∩ (b, 1)` and `p ∈ Z[1/6] ∩ (0, a)` with
     `q - p ∈ 5Z[1/6]`.
   - The 1-periodic copy of `F_6'` lies in `Q_2` (`commutator_perCore_le_gammaTwo`; it
     is the derived subgroup of the periodic `F_6 ≤ Γ_2`, Proposition 1.4(2)). It moves
     a point of `Z[1/6] ∩ (0, 1)` to any point of `(0, 1)` in the same residue class
     (`exists_perCore_apply`, Hyde–Lodha Proposition 3.5 for one point). Let `P` be such
     an element with `P(q) = p`.
   - `P` is increasing and fixes the integers, so it preserves `(0, 1)` and
     `P(b) < P(q) = p < a ≤ b`. Since `P(b) < b` and `P` is increasing,
     `P^m(b) < P^(m-1)(b) < ... < P(b) < a` for all `m ≥ 1`.
   - So `P^m([a, b]) = [P^m(a), P^m(b)]` lies in `(0, a)` for `m ≥ 1`, and the arcs
     `P^m([a, b])`, `m ≥ 0`, are pairwise disjoint: `P^k([a,b]) ∩ P^j([a,b]) =
     P^j(P^(k-j)([a,b]) ∩ [a,b]) = ∅` for `k > j`.
   - They all have mass `mu([a, b])` and lie in a space of total mass 1, so
     `mu([a, b]) = 0`.
3. **The measure is the atom at `0̄`.** `(0, 1)` is a countable union of intervals
   `[a, b]` with `0 < a < b < 1`, so `mu((0, 1)) = 0` and `mu = δ_(0̄)`.
4. **`Q_2` moves `0̄`.** `Γ_2` contains `λ` with `λ(0) = 5/18` (Proposition 3.4;
   `lamPerm_mem_gammaTwo`, `lamPerm_zero`). If every element of `Q_2` fixed `0̄`, then,
   because `Q_2` is normal in `Γ_2`, every element `λ̄ ḡ λ̄⁻¹` of `Q_2` would fix
   `λ̄(0̄)`, which is `5/18 = 10/36 ∈ Z[1/6] ∩ (0, 1)`. But the residue class of `5/18`
   modulo `5Z[1/6]` has other points in `(0, 1)`, and `F_6' ≤ Q_2` moves `5/18` to them
   (step 2). So some `g ∈ Q_2` has `ḡ(0̄) != 0̄`. (This is also Hyde–Lodha Lemma 3.9(2),
   `exists_mem_unit_of_not_int`.)
5. **Contradiction.** Invariance gives `mu({ḡ(0̄)}) = mu({0̄}) = 1` with
   `ḡ(0̄) != 0̄`, which is impossible for a probability measure.

So `Q_2` is not amenable. `Γ_2` contains `Q_2`, and subgroups of amenable groups are
amenable, so `Γ_2` is not amenable either.

Simplicity and finite presentation of `Q_2` were not used; they are what make the
group relevant to `fp-infinite-simple-amenable-group`. ∎
