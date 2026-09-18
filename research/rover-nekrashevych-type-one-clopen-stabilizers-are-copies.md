---
rg: 2
id: rover-nekrashevych-type-one-clopen-stabilizers-are-copies
kind: claim
title: In a Rover--Nekrashevych group the elements supported in a type-one clopen set form a copy of the group, and type-one partition stabilizers are virtually direct powers of it
distinct_from:
  full-binary-cantor-groups-have-copy-stabilizers: that is the binary case d = 2 for any full overgroup of standard V; this is every arity d >= 2 for V_d(G), where only clopen sets of type 1 (cone count 1 mod d-1) are copies.
  thompson-v-coset-stabilizers-contain-copies-of-v: that records that the copies make coset peeling circular for finiteness properties; here the copies are used for Sigma-invariants with the finiteness of the group assumed, which is not circular.
---

**ESTABLISHED (proof in `rover-nekrashevych-type-one-clopen-stabilizers-are-copies-proof`; unreviewed).**

Let `G <= Aut(T_d)` be self-similar, `d >= 2`, `k = d − 1`, `C = X^N` and `Γ = V_d(G)`.

- `Γ` is the set of homeomorphisms `h` of `C` with a **table**: cone partitions `C = ⊔ u_i C = ⊔ v_i C` and `g_i in G`
  with `h(u_i w) = v_i g_i(w)`.
- A nonempty clopen `A` has **type 1** if it is a disjoint union of `n ≡ 1 mod k` cones. For `d = 2` every nonempty
  clopen set has type 1.
- `Γ_A = {h in Γ : h = id on C \ A}`.

1. **Type is well defined and `Γ`-invariant.** Every cone decomposition of `A` has the same count mod `k`, and `h(A)`
   has the type of `A` for `h in Γ`.
2. **Copies.** If `A` has type 1, there is a homeomorphism `φ: A -> C` with `h -> φ h φ^{-1}` an isomorphism
   `Γ_A -> Γ`.
3. **Fullness.** If `h in Γ` and `h(A) = A`, then `h_A` (`h` on `A`, `id` off `A`) lies in `Γ_A`.
4. **Partition stabilizers.** Let `P = {B_1, ..., B_n}` be a partition of `C` into clopen sets. Let `Γ_P` be its
   setwise stabilizer, and `K_P` the subgroup fixing every block. Then:
   - `K_P = Γ_{B_1} × ... × Γ_{B_n}` (internal direct product);
   - `|Γ_P : K_P| <= n!`.

   If every `B_i` has type 1, then `K_P ≅ Γ^n`.
5. **Transitivity.** `V_d <= Γ` acts transitively on ordered `n`-tuples `(B_1, ..., B_n)` forming a partition of `C`
   into type-1 clopen sets, for each `n`.
6. **Living characters.** If `Φ in Hom(Γ,R)` is nonzero, then `Φ|_{Γ_A} != 0` for every nonempty clopen `A`.

## Attempts

- 2026-09-18 (swarm-0917-w7-w7-z-last1): proved directly with tables. Item 6 uses
  `rover-nekrashevych-characters-are-sum-invariant`.
