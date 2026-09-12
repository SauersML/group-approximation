---
rg: 2
id: quotientless-hyperbolic-via-sp21-simple-quotient-bound
kind: route
title: Two Olshanskii quotients surjective on deep finite-index subgroups kill every simple quotient of a lattice with finitely many non-congruence ones
target: hyperbolic-group-without-finite-quotients
requires:
  - sp21-lattice-few-alternating-and-large-rank-quotients
  - sp21-bounded-rank-simple-quotients-almost-all-congruence
  - normal-subgroups-of-arithmetic-lattices-are-congruence-open
  - olshanskii-g-subgroup-quotient-theorem
---

Let `Γ` and `r` be as in `sp21-lattice-few-alternating-and-large-rank-quotients`,
with `Γ <= G(O)` of finite index. `Γ` is torsion-free, cocompact, hence
non-elementary hyperbolic, and `E(Γ) = 1`. Take the finite prime set `S` from
the proof of `normal-subgroups-of-arithmetic-lattices-are-congruence-open`, so
that (SA), (QS) and (FR) hold off `S`, and write `Γ̄ = Γ̄_S × ∏_(𝔭 ∉ S) G(O_𝔭)`.

**Surjection trick.** If `φ: Γ ->> G_1` and `φ(Δ) = G_1` for a normal
`Δ ⊴ Γ`, then `Γ = Δ · ker φ`. So `ker φ` maps onto `Γ/Δ`.

**Step 0: finitely many bad simple images.**
- **Non-congruence simple quotients.** Rank `<= r`: finitely many by
  `sp21-bounded-rank-simple-quotients-almost-all-congruence`. Alternating, or
  rank `> r`: finitely many by hypothesis. Sporadic: finitely many, since `Γ` is
  finitely generated.
- **Simple quotients of `Γ̄_S`.** Finitely many. Its open pronilpotent subgroup
  dies in a nonabelian simple quotient, and `Γ^ab` is finite.

Let `χ_1,...,χ_s: Γ ->> S_j` list all of these, together with one proper
congruence quotient so the list is nonempty. Put `Δ_1 = ∩ ker χ_j`, of finite
index.

**Step 1: the first quotient.**
- `Δ_1` is non-elementary with `E(Δ_1) = 1`, so it is a G-subgroup.
- `olshanskii-g-subgroup-quotient-theorem` (2) gives `φ_1: Γ ->> G_1`,
  non-elementary hyperbolic, with `φ_1(Δ_1) = G_1`.
- `M_1 = ker φ_1` maps onto `Γ/Δ_1`, so `M_1 != 1` and `M_1 ⊄ ker χ_j` for all
  `j`.
- `φ_1` is bijective on conjugacy classes of finite-order elements, so `G_1` is
  torsion-free.

**Step 2: the bad primes.**
- Let `P_1` be the set of `𝔭 ∉ S` at which every element of `M_1` is central
  mod `𝔭`. It is finite, by step (a) of the openness proof applied to one
  `1 != m in M_1`.
- Put `Δ_2 = Δ_1 ∩ ∩_(𝔭 in P_1) ker(Γ ->> G(O/𝔭)/Z)`. Its image in `G_1` has
  finite index, so it is a G-subgroup.
- Olshanskii again gives `φ_2: G_1 ->> G_2`, non-elementary hyperbolic, and
  surjective on the image of `Δ_2`.
- Put `M = ker(φ_2 φ_1) ⊇ M_1`. Then `M` maps onto `Γ/Δ_2`. So `M` is not
  central mod any `𝔭 in P_1`, and `M ⊇ M_1` is not central mod any other
  `𝔭 ∉ S`.

**Step 3: congruence density.** Let `N` be the closure of `M` in `Γ̄`.
- Steps (a) and (b) of the openness proof give `N ⊇ ∏_(𝔭 ∉ S) G(O_𝔭)`.
- Step (c) makes `π_S(N)` open and normal in `Γ̄_S`. If it were proper, it would
  lie in a maximal open normal subgroup whose simple quotient is one of the
  `χ_j`, contradicting `M ->> Γ/Δ_1`.
- So `N = Γ̄`.

**Step 4: no finite quotients.** Let `Γ/N'` be a finite simple quotient of
`G_2 = Γ/M`, so `N' ⊇ M`.
- If `N'` is congruence, its closure is open with the same quotient and contains
  `N = Γ̄`, so `N' = Γ`. That is impossible.
- Otherwise `Γ/N'` is some `χ_j` with `M ⊄ ker χ_j`, which is also impossible.

Every nontrivial finite group has a simple quotient, so `G_2` has no nontrivial
finite quotient. It is non-elementary hyperbolic, hence infinite. `QED`
