---
rg: 2
id: sp21-large-type-simple-images-quotient-proof
kind: route
title: Two Olshanskii quotients remove every abelian, sporadic, small, congruence and bounded-rank simple image of a Sp(2,1) lattice
target: sp21-lattice-quotient-with-only-large-type-simple-images
requires:
  - sp21-bounded-rank-simple-quotients-almost-all-congruence
  - normal-subgroups-of-arithmetic-lattices-are-congruence-open
  - olshanskii-g-subgroup-quotient-theorem
artifacts:
  - research/artifacts/nrfh-kazhdan-quotientless-2026-09-12.md
---

Fix `r`, `f` and `B`. The following are used without a node, as in
`quotientless-hyperbolic-via-sp21-noncongruence-separation`:
- `Γ` is non-elementary hyperbolic, with `E(Γ) = 1` because it is torsion-free;
- `Γ` has property (T), so `Γ^ab` is finite, and (T) passes to quotients;
- the classification of finite simple groups.

**Step 1: a proper quotient.**
- `Γ` is residually finite, so it has a proper finite-index normal subgroup
  `Δ_0`. `Δ_0` is non-elementary with `E(Δ_0) = 1`, so part 1 of
  `olshanskii-g-subgroup-quotient-theorem` makes it a G-subgroup.
- Part 2 gives `φ_1 : Γ ->> H`, injective on `B`, with `H` non-elementary
  hyperbolic and `φ_1(Δ_0) = H`. `φ_1` is bijective on conjugacy classes of
  finite-order elements, so `H` is torsion-free.
- Put `M = ker φ_1`. Then `Γ = Δ_0 M`, so `M` maps onto `Γ/Δ_0 != 1`, and
  `M != 1`.

**Step 2: the bad simple images of `H` are finitely many.** Call a finite simple
quotient `χ : H ->> S` *bad* if either:
- `S` is abelian, sporadic, of Lie type of rank at most `r`, or of order at most
  `f`; or
- `ker(χφ_1)` contains a principal congruence subgroup.

Each kind is finite in number.
- **Abelian.** `H^ab` is a quotient of the finite group `Γ^ab`.
- **Sporadic, or of order at most `f`.** There are finitely many isomorphism
  types, and a finitely generated group has finitely many epimorphisms onto each
  finite group.
- **Congruence kernel, of any type.** `ker(χφ_1) = Γ ∩ N̄`, where `N̄` is open and
  normal in `Γ̄` and contains the closure of `M`. That closure is open by
  `normal-subgroups-of-arithmetic-lattices-are-congruence-open`, so these kernels
  correspond to normal subgroups of the finite group `Γ̄/closure(M)`.
- **Lie type of rank at most `r`, non-congruence kernel.** Finitely many, by
  `sp21-bounded-rank-simple-quotients-almost-all-congruence`.

Put `Δ_1 = ∩ ker χ` over the bad `χ`, or `Δ_1 = H` if there are none. `Δ_1` has
finite index in the torsion-free group `H`, so it is a G-subgroup as in Step 1.

**Step 3: kill them.** Olshanskii gives `φ_2 : H ->> G`, injective on `φ_1(B)`,
with `G` non-elementary hyperbolic and `φ_2(Δ_1) = G`. As in Step 1, `G` is
torsion-free.
- Put `π = φ_2 φ_1`. It is injective on `B`, and `G` is Kazhdan as a quotient of
  `Γ`.
- Let `ψ : G ->> S` be a finite simple quotient. Then `ψφ_2 : H ->> S` has the
  same image `S`, and `ker(ψφ_2φ_1) = ker(ψπ)`.
- Suppose `S` has a bad type or `ker(ψπ)` is congruence. Then `ψφ_2` is a bad
  image of `H`, so it kills `Δ_1`. But `ψ(φ_2(Δ_1)) = ψ(G) = S != 1`, which is
  impossible.

**Conclusions.**
- **(2).** A nontrivial finite quotient of order at most `f` has a simple quotient
  of order at most `f`.
- **(3).** Let `Γ/N` be a nontrivial congruence quotient with `N ⊇ ker π`. It has
  a simple quotient whose kernel contains `N`, and hence a principal congruence
  subgroup, which is excluded. So `ker π · Γ(𝔞) = Γ` for every principal
  congruence subgroup `Γ(𝔞)`, i.e. `ker π` is dense in `Γ̄`.
- **(4).** Holds by Step 3.
- **Perfectness.** `G^ab` is a finite quotient of `Γ^ab`. It has no simple
  quotient, since any simple quotient of it would be abelian. So `G^ab = 1`.

`QED`
