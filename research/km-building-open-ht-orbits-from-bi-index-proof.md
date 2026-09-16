---
rg: 2
id: km-building-open-ht-orbits-from-bi-index-proof
kind: route
title: Point stabilizers and set stabilizers of finite subsets in multiply transitive actions have infinite index and few double cosets, which the building-open dichotomy forbids
target: km-building-open-subgroups-have-infinite-ht-orbits
requires:
  - km-building-open-subgroups-have-infinite-bi-index
artifacts:
  - research/artifacts/km-building-open-subgroups-bi-index-2026-09-16.md
---

Artifact §4. Write (A), (A'') for the dichotomy of `km-building-open-subgroups-have-infinite-bi-index`
and its quotient form. The preimage in `Λ` of any subgroup of `Γ` containing `Γ_V` contains
`Λ ∩ V`, so (A'') applies to such subgroups of `Γ`.

**(a)** `Γ_ω` has index `|Ω| = ∞`. Its double cosets correspond to the orbitals, of which there
are finitely many. If `Γ_ω ⊇ Γ_V`, (A'') is contradicted.

**(b)** Suppose a `Γ_V`-orbit `A` has `m ≤ k` points, and let `M_A` be the setwise stabilizer of
`A`. Then `Γ_V ⊆ M_A`.
1. **Infinite index.** On an infinite set, `2k`-transitivity gives `j`-transitivity for every
   `j ≤ 2k`, by extending tuples. So `Γ` is transitive on `m`-subsets and
   `[Γ:M_A] = |Ω^{(m)}| = ∞`.
2. **Few double cosets.** `M_A`-double cosets correspond to `Γ`-orbits on pairs of `m`-subsets.
   Let `(A_1,A_2)` and `(A_3,A_4)` be pairs with `|A_1 ∩ A_2| = |A_3 ∩ A_4|`.
   - Some bijection `A_1 ∪ A_2 → A_3 ∪ A_4` sends `A_1` to `A_3` and `A_2` to `A_4`.
   - It is realized in `Γ`, because `|A_1 ∪ A_2| ≤ 2k`.

   So there are at most `m+1` such orbits, and `|M_A\Γ/M_A| ≤ m+1`.
3. This contradicts (A'').

**(b')**
- **Orbits of `Γ_V`.** Apply (b) for every `k`.
- **Finite-index subgroups.** If `L ≤ Γ_V` has index `r` and a finite orbit `Lω`, then `Γ_Vω` is
  a union of `r` translates `g_iLω`, so it is finite. This contradicts the first part.
- **Building-open subgroups.** If `M ⊇ Γ_V` and `L ≤ M` has finite index, then `L ∩ Γ_V` has
  finite index in `Γ_V`, and each of its orbits lies in an orbit of `L`. So every orbit of `L` is
  infinite by the previous item.
- **Index form.** It is orbit-stabilizer.

**(c)**
1. The pulled-back action of `Λ` is primitive, so the preimage `M̃` of `Γ_ω` is maximal in `Λ`.
2. If `O = closure_G(M̃)` is open, then `Λ ∩ O` is a subgroup containing `M̃`.
   - If `Λ ∩ O = Λ`, then `O = G` by density.
   - Otherwise `Λ ∩ O = M̃` by maximality, so `M̃` is building-open with `V = O`. It has infinite
     index and finitely many double cosets, contradicting (A).

**(d)**
1. If `O = closure_G(H̃)` is open, then `M = Λ ∩ O ⊇ H̃` is building-open.
2. `|M\Λ/M| ≤ |H̃\Λ/H̃| = |H\Γ/H| < ∞`, so `[Λ:M] < ∞` by (A).
3. **Index transfer.** The map `λM ↦ λO`, `Λ/M → G/O`, is well defined because `M ⊆ O`.
   - **Injective.** `λO = λ'O` gives `λ^{-1}λ' ∈ Λ ∩ O = M`.
   - **Surjective.** Every open coset `gO` meets the dense subgroup `Λ`.

   So `[G:O] = [Λ:M] < ∞`.

**Explicit members.** For `S_q`, apply the above with `N = Z` and `V = B` (Borel), or
`V = Fix_G(F)` for a finite set `F` of chambers. These are open by [CM] l.826, and
`Λ ∩ Fix_G(F) = Fix_Λ(F)`, since the action of `G` extends that of `Λ`. ∎
