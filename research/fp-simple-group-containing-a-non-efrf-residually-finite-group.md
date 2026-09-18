---
rg: 2
id: fp-simple-group-containing-a-non-efrf-residually-finite-group
kind: claim
title: Some finitely presented simple group contains a finitely generated residually finite group that is not effectively residually finite, for example one of Rauzy's lamplighter amalgams L(A)
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
distinct_from:
  effective-residual-finiteness-separator-for-boone-higman: that is the separator theorem whose open side this is; this is the existence statement that Boone–Higman forces.
  rf-decidable-groups-embed-in-decidable-fg-branch-groups: that asks for a residually finite branch host of Rauzy's groups with solvable word problem; this asks for a simple host, which is never residually finite, so the two questions are independent.
  fp-simple-group-with-kazhdan-subgroup-of-non-residual-centre: that is the Kazhdan central-residual monster; this is the effectivity monster. Both are predicted by Boone–Higman and neither is known.
---

**OPEN.** Boone–Higman implies it: embed Rauzy's `L(A)` (arXiv:2002.02540, Theorem 2).

**Statement.** Some finitely presented simple group `S` has a finitely generated residually finite subgroup `H` that is not effectively residually finite. Equivalently, `H`'s depth function exceeds every recursive function (Rauzy §3, for `H = L(A)`).

## Constraints on any construction for `H = L(A) = L *_{U_A} L`

Here `L = Z/2 ≀ Z = ⟨a, ε⟩`, `u_i = a^i ε a^(-i)`, `U_A = ⟨u_i : i ∈ A⟩`, and `A` is Rauzy's recursive, profinitely closed, not effectively closed set. Both `A` and its complement are infinite. These are elementary lane proofs.

1. **Reduction.** `L(A)` has index 2 in `L *_{U_A} (U_A × Z/2)`. By `pbh-coset-wreaths-iff-identity-edge-hnns`, `L(A)` lies in `B_A`, and so in a finitely presented simple group, iff there are a group `M ∈ B_A` containing `L` and an element `m ∈ M` with `C_L(m) = U_A`.
   - For the index-2 statement, the kernel of `L *_{U_A} (U_A × ⟨τ⟩) → Z/2` (sending `τ ↦ 1` and `L ↦ 0`) is `L *_{U_A} τLτ ≅ L(A)`.
   - For "only if", `C_L(τ) = U_A` in that amalgam, by normal forms.
2. **No virtual retract.** `U_A` is not a virtual retract of any group `D ⊇ L`.
   - Suppose `ρ : D₀ → U_A` retracts a finite-index `D₀ ⊇ U_A`. Then `a^n ∈ D₀` for some `n ≥ 1`.
   - Since `A` is infinite, it contains `i < j` with `j ≡ i` mod `n`. Then `ρ(u_j) = ρ(a^(j−i)) ρ(u_i) ρ(a^(j−i))^(-1) = ρ(u_i)`, because `U_A` is abelian.
   - But `ρ` fixes `u_i ≠ u_j`, a contradiction.
   - So the virtual-retract cases of (e) never apply.
3. **No standard clopen stabilizer.** Take a realization of `L` by homeomorphisms whose lamp supports `R_i` are disjoint and converge to points `p_±` as `i → ±∞`, like the standard copy in Thompson's `V`.
   - Fix a clopen `U`. If `p_+ ∈ U`, some neighbourhood of `p_+` lies in `U`, so `R_i ⊆ U` for all large `i`. If `p_+ ∉ U`, some neighbourhood of `p_+` misses `U`, so `R_i ∩ U = ∅` for all large `i`. Either way `u_i` preserves `U` for all large `i`, and likewise for `i → −∞`.
   - So the lamp part of every clopen stabilizer, and of every finite-index overgroup of one, is cofinite.
   - `U_A` is not of that form, because the complement of `A` is infinite. The clopen-stabilizer wreath lemma (`wreaths-over-clopen-stabilizer-cosets-lie-in-b-a`) therefore cannot be applied to such realizations.
4. **What is left.** One needs a host element `m` whose commutation with the lamp `u_i` computes membership `i ∈ A`. Examples:
   - a reversible-machine element of `nV` or of a twisted Brin–Thompson group, which runs Rauzy's halting-time construction along the lamp positions;
   - a lamp configuration `m ∈ Q^Z` over a non-abelian `Q`, with `m_i ∈ C_Q(x)` iff `i ∈ A`, together with a finitely presented `B_A` host of `⟨L, m⟩`. Such a host is not known.

## Lesson for general BH

- **What fails.** Lamp placements by a fixed geometric pattern reach only trivial amalgamation sets: finite ones via retracts, cofinite ones via clopen stabilizers in V-type realizations. That covers V-type realizations, virtual retracts and clopen stabilizers.
- **What a successful host needs.** A group element whose commutation pattern is a computation. This is the same "compiler" ingredient (a hard rule inside the host, not in constants) that the complexity wall and the definability cap demand.
