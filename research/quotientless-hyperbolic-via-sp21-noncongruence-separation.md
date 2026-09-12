---
rg: 2
id: quotientless-hyperbolic-via-sp21-noncongruence-separation
kind: route
title: One Olshanskii quotient makes congruence openness apply, separation leaves finitely many simple quotients, a second Olshanskii quotient kills them
target: hyperbolic-group-without-finite-quotients
requires:
  - sp21-noncongruence-simple-kernels-separate-points
  - sp21-bounded-rank-simple-quotients-almost-all-congruence
  - normal-subgroups-of-arithmetic-lattices-are-congruence-open
  - olshanskii-g-subgroup-quotient-theorem
---

Let `Γ` and `r` be as in `sp21-noncongruence-simple-kernels-separate-points`, with
`Γ <= G(O)` of finite index. `Γ` is torsion-free and cocompact, so it is
non-elementary hyperbolic with `E(Γ) = 1`. It has property (T), so `Γ^ab` is
finite.

**Step 1: a proper torsion-free hyperbolic quotient.**
- `Γ` is residually finite. Pick a proper normal subgroup `Δ_0` of finite
  index. It is non-elementary, and `E(Δ_0) = 1` because `Γ` is torsion-free.
  With trivial `E`, both indices in part 1 of
  `olshanskii-g-subgroup-quotient-theorem` equal `1`, so `Δ_0` is a G-subgroup.
- Part 2 gives `φ_1 : Γ ->> H`, with `H` non-elementary hyperbolic and
  `φ_1(Δ_0) = H`. It is bijective on conjugacy classes of finite-order elements,
  so `H` is torsion-free.
- Put `M = ker φ_1`. From `φ_1(Δ_0) = H` we get `Γ = Δ_0 M`, so `M` maps onto
  `Γ/Δ_0 != 1`, hence `M != 1`.

**Step 2: `H` has only finitely many finite simple quotients.** A finite simple
quotient of `H` is `Γ/N` with `N ⊇ M`. By the classification it is abelian,
sporadic, alternating, or of Lie type.
- **Abelian.** `H^ab` is a quotient of the finite group `Γ^ab`, so there are
  finitely many.
- **Sporadic.** There are finitely many types, and a finitely generated group has
  finitely many epimorphisms onto each.
- **Lie type, rank `<= r`, `N` non-congruence.** Finitely many, by
  `sp21-bounded-rank-simple-quotients-almost-all-congruence`.
- **Lie type, `N` congruence.** Then `N` contains a principal congruence
  subgroup, so `N = Γ ∩ N̄` with `N̄` open and normal in `Γ̄`. Also `N̄` contains
  the closure of `M`, which is open by
  `normal-subgroups-of-arithmetic-lattices-are-congruence-open`. Such `N̄`
  correspond to normal subgroups of the finite group `Γ̄/closure(M)`, so there are
  finitely many.
- **Alternating, or rank `> r`.** Fix `1 != m ∈ M`. Every such `N` contains `m`,
  and by the separation claim only finitely many kernels of these types do.

**Step 3: kill them.** If `H` has no finite simple quotient, it has no nontrivial
finite quotient, and we are done. Otherwise, let `χ_1,...,χ_s` be the finite simple
quotients of `H` and put `Δ_1 = ∩ ker χ_j`, of finite index.
- `Δ_1` is a G-subgroup exactly as in Step 1, since `H` is torsion-free.
- Olshanskii gives `φ_2 : H ->> G`, with `G` non-elementary hyperbolic and
  `φ_2(Δ_1) = G`.
- Suppose `ψ : G ->> S` is a finite simple quotient. Then `ψ φ_2` is some `χ_j`,
  so it kills `Δ_1`. But `ψ(φ_2(Δ_1)) = ψ(G) = S != 1`, a contradiction.

So `G` has no finite simple quotient. Every nontrivial finite group has a simple
quotient, so `G` has no nontrivial finite quotient. `G` is non-elementary
hyperbolic, hence infinite. `QED`

**Remarks.**
- **What the congruence openness buys.** After one preliminary quotient
  `M != 1`, openness bounds the congruence simple quotients at once. So this
  route needs no congruence-density step, unlike
  `quotientless-hyperbolic-via-sp21-simple-quotient-bound`.
- **The strong contrapositive.** Steps 2–3 apply verbatim to every proper,
  torsion-free, non-elementary hyperbolic quotient `H = Γ/M`, using separation
  only at one `m ∈ M`. This gives the contrapositive recorded on the claim.
- **Inputs used without a node.** The classification of finite simple groups,
  and property (T) of cocompact `Sp(2,1)` lattices, are used as in the sibling
  route. No novelty is claimed for the argument pattern (Olshanskii, Lubotzky
  §4). Not Lean-verified.
