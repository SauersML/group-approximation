---
rg: 2
id: torelli-groups-are-not-cat0-cocompact-stabilizers-proof
kind: route
title: "Pass to the fixed set of a normal finite-index core of the stabilizer, get a CAT(0) quotient group, and contradict the Solvable Subgroup Theorem with a Heisenberg group"
target: torelli-groups-are-not-cat0-cocompact-stabilizers
requires: [cat0-group-solvable-subgroups-are-virtually-abelian, outer-torelli-groups-finitely-generated, surface-torelli-fg-in-genus-at-least-three]
---

References to Bridson–Haefliger (BH) are to *Metric Spaces of Non-Positive
Curvature*, Part II.

## General theorem

Let `N ⊴ Γ` be finitely generated, and let `Γ` act by isometries on a proper CAT(0)
space `M`, cocompactly and with discrete orbits, with `x ∈ M` such that `Γ_x ∩ N`
has finite index in `Γ_x` and in `N`.

**Step 1: a normal core.** Put `T_0 = Γ_x ∩ N`, of index `k` in `N`. A finitely
generated group has only finitely many subgroups of a given finite index (each is
determined by the transitive action on its `k` cosets, and there are finitely many
homomorphisms `N -> Sym(k)`). For `γ ∈ Γ`, `γ T_0 γ^{-1} = Γ_{γx} ∩ N` is again a
subgroup of `N` of index `k`, since `N` is normal. So `N_1 = ∩_{γ ∈ Γ} γ T_0 γ^{-1}`
is a finite intersection, hence of finite index in `N`, and it is normal in `Γ`.
Every element of `N_1` fixes every point `γx`.

**Step 2: the fixed set.** Let `M' = Fix(N_1) = ∩_{h ∈ N_1} Fix(h)`. Each `Fix(h)`
is closed and convex (the displacement function of an isometry is continuous and
convex, BH II.6.2), so `M'` is closed and convex, and it contains the orbit `Γx`, so
it is nonempty. It is `Γ`-invariant because `N_1` is normal. With the induced metric
`M'` is a proper CAT(0) space. The nearest-point projection `π: M -> M'` exists, is
1-Lipschitz (BH II.2.4), and commutes with every isometry of `M` that preserves
`M'`, since it is defined metrically. If `M = Γ·K` with `K` compact, then
`M' = π(M) = Γ·π(K)`, and `π(K)` is compact. So `Λ := Γ/N_1` acts on `M'` by
isometries, cocompactly.

**Step 3: properness.** The orbit `Γx` is discrete. It is then closed: if
`γ_i x -> y`, the points `γ_i x` form a Cauchy sequence, so
`d(x, γ_i^{-1} γ_j x) = d(γ_i x, γ_j x) -> 0`; since `x` is isolated in `Γx`, this
forces `γ_j x = γ_i x` for large `i, j`, so `y ∈ Γx`. A closed discrete subset of a
proper space meets each ball in finitely many points. The stabilizer of `x` in
`Λ` is `Γ_x/N_1`, which is finite because `N_1` has finite index in `N ∩ Γ_x = T_0`
and `T_0` has finite index in `Γ_x`. Hence `{λ ∈ Λ : d(λx, x) <= R}` is finite for
every `R`: it is a finite union of cosets of the finite stabilizer. For any
`y ∈ M'`, `d(λy, y) <= r` implies `d(λx, x) <= r + 2d(x, y)`, so for each `y` and
`r` only finitely many `λ` move `y` by at most `r`. Thus `Λ` acts properly and
cocompactly by isometries on the CAT(0) space `M'`. This proves the "more precisely"
part.

**Step 4: the contradiction.** Let `S <= Γ/N` be solvable and not virtually abelian,
and let `E <= Λ` be its preimage under `Λ = Γ/N_1 -> Γ/N`, whose kernel `F = N/N_1`
is finite. `E` acts on `F` by conjugation, so `C = C_E(F)` has finite index in `E`.
`C ∩ F` is central in `C` and `C/(C ∩ F)` embeds in `S`, so `C` is a central
extension of a solvable group and is solvable. By the Solvable Subgroup Theorem
(`cat0-group-solvable-subgroups-are-virtually-abelian`) applied to `Λ`, `C` is
virtually abelian. So `E` is virtually abelian, and so is its image `S`: a
contradiction. Hence no such action exists.

## Torelli corollary

Take `Γ = G` and `N = T` as in the claim. The groups `T_n`, `IA_n` are finitely
generated for every `n` (`outer-torelli-groups-finitely-generated`), and `I_g`
(with at most one marked point or boundary component) for `g >= 3`
(`surface-torelli-fg-in-genus-at-least-three`; the marked-point case is the kernel of
`Mod(S_{g,*}) -> Sp_{2g}(Z)`, an extension of `I_g` by `π_1(S_g)`, both finitely
generated). A finite-index subgroup `G ∩ T` of a finitely generated group is
finitely generated. `G/T` embeds as a finite-index subgroup `Λ_0` of `GL_n(Z)` or
`Sp_{2g}(Z)`, because the ambient maps onto these groups (Nielsen's generators map
onto `GL_n(Z)`; `Mod -> Sp_{2g}(Z)` is surjective).

A non-virtually-abelian solvable subgroup of `Λ_0`: let `m = [GL_n(Z) : Λ_0]!`
(or the index in `Sp_{2g}(Z)`), so that `u^m ∈ Λ_0` for every `u` (the cosets
`u^i Λ_0`, `0 <= i <= index`, repeat). In `GL_n(Z)`, `n >= 3`, let `a = E_{12}^m`,
`b = E_{23}^m`, elementary matrices. They generate a subgroup of the unipotent
upper-triangular group, so it is nilpotent, hence solvable, and `[a, b] = E_{13}^{m^2}`
commutes with `a` and `b`. If it were virtually abelian, some powers `a^k, b^k`
(`k >= 1`) would commute, but `[a^k, b^k] = E_{13}^{k^2 m^2} ≠ 1`. In `Sp_{2g}(Z)`,
`g >= 3`, use the embedding `A -> diag(A, (A^T)^{-1})` of `GL_g(Z)` (it preserves the
standard symplectic form) and the same matrices inside `GL_3(Z) <= GL_g(Z)`, raised
to the power `m`. The general theorem applies.
