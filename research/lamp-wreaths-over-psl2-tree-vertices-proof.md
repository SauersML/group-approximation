---
rg: 2
id: lamp-wreaths-over-psl2-tree-vertices-proof
kind: route
title: The Möbius action puts PSL_2(Z[1/2m]) in the finitely presented full host V_2 of the Iwahori group, where the stabilizer of the ball Z_2 has index 3 in the vertex stabilizer
target: lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a
requires:
  - wreaths-over-clopen-stabilizer-cosets-lie-in-b-a
  - rational-iwahori-group-is-union-of-fp-self-similar-groups
  - pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori
  - rover-nekrashevych-finite-presentation-criteria
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

Direct proof (2026-09-18, lane bh-openq-papers). Not independently reviewed. Notation of
`pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori` with `p = 2`: `Y = Z_2 = ∂T_2`,
cones `a + 2^k Z_2`, canonical coordinates `φ_{a,k}(u) = a + 2^k u`.

**1. The host.** Let `K = Γ_2(m)`, the image in `PGL_2(Q)` of
`{[[α,β],[c,δ]] ∈ GL_2(Z[1/m]) : c ∈ 2Z[1/m]}`, acting on `Z_2` by Möbius maps. By items 1–2
of `rational-iwahori-group-is-union-of-fp-self-similar-groups`, `K` is a finitely presented
self-similar group. Let `D = V_2(K)`, the homeomorphisms of `Y` that on the cones of some
finite cone partition have the form `φ_{b,k'} ∘ γ ∘ φ_{a,k}^(-1)` with `γ ∈ K`.
- *Finitely presented:* (FP1, Scott) of `rover-nekrashevych-finite-presentation-criteria`.
- *Full.* Let `f` be a `D`-local homeomorphism of `Y`. By compactness `f` agrees with
  elements of `D` on the pieces of a finite clopen partition, which we refine to a cone
  partition that also refines the defining partitions of those elements. On a subcone
  `C = a·w` of a defining cone `a` of `d ∈ D`, self-similarity of `K` gives
  `d|_C = φ_{b·γ(w)} ∘ γ|_w ∘ φ_{a·w}^(-1)` with the section `γ|_w ∈ K`. So `f` has the defining
  form on every cone of a finite partition, and `f ∈ D`.
- *Clopen transitive.* `D ⊇ V_2(1)`, the binary Thompson group `V`, which gives a local map
  between any two nonempty clopen sets (as recorded in
  `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`).

**2. The embedding.** By item 6 of `rational-iwahori-group-is-union-of-fp-self-similar-groups`
(with item 3 of `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`),
`PGL_2(Z[1/(2m)]) ≤ D` through the Möbius action on `P^1(Q_2) = Z_2 ⊔ D_∞`, transported to
`Y` by the chart homeomorphism `ψ : P^1(Q_2) -> Y`, which places `Z_2` on the cone `0 + 2Z_2`.
So `G = PSL_2(Z[1/(2m)]) ≤ PGL_2(Z[1/(2m)]) ≤ D`, acting by `g ↦ ψ g ψ^(-1)`.

**3. The clopen and its stabilizer.** Let `U = ψ(Z_2) = 2Z_2`, a proper nonempty clopen subset of
`Y`. For `g ∈ G`, `g(U) = U` iff the Möbius map `g` satisfies `g(Z_2) = Z_2` in `P^1(Q_2)`.
- *Claim:* `Stab_G(U) = Γ_0` is the image of `{A ∈ SL_2(Z[1/m]) : c ∈ 2Z[1/m]}`.
- *Proof.* Take `A = [[a,b],[c,d]] ∈ SL_2(Z[1/(2m)])` with `g_A(Z_2) = Z_2`, and write `|·| = |·|_2`.
  - The pole `-d/c` is not in `Z_2`. If `|c| ≥ |d|` it would be, so `|d| > |c|` and
    `|cz + d| = |d|` for all `z ∈ Z_2`.
  - Hence `|g_A(x) - g_A(y)| = |ad - bc| |x - y| / |d|^2 = |x - y| / |d|^2`.
  - A bijection of `Z_2` onto itself that multiplies distances by a constant `λ` has
    `λ = 1`, since `Z_2` has diameter `1`. So `|d| = 1`, `|c| < 1`, `b = g_A(0)·d ∈ Z_2` and
    `a = (1 + bc)/d ∈ Z_2`.
  - The entries lie in `Z[1/(2m)] ∩ Z_2 = Z[1/m]`, because `m` is odd.
  - Conversely, if `A ∈ SL_2(Z[1/m])` with `c` even, then `ad = 1 + bc` is odd, so
    `|cz + d| = 1` on `Z_2`. Hence `g_A` maps `Z_2` isometrically into `Z_2`, and `g_A^(-1)`
    has the same form, so `g_A(Z_2) = Z_2`.
- *Index.* `Γ_0 ≤ H = PSL_2(Z[1/m])`, and `Γ_0` is the preimage of the image of the upper
  triangular subgroup under reduction `SL_2(Z[1/m]) -> SL_2(F_2)`. Since `m` is odd,
  `Z[1/m] -> F_2` exists. So `[H : Γ_0] ≤ [SL_2(F_2) : B(F_2)] = 3`.

**4. Conclusion.** Apply `wreaths-over-clopen-stabilizer-cosets-lie-in-b-a` with `D`, `G`, `U`,
`H` and `K = Γ_0` as above. `L ≀_{G/H} G ∈ B_A` for every `L ∈ B_A`, and it embeds in a
finitely presented simple group when `L` is finitely generated.

**5. The vertex description (not used above).** `H` is the stabilizer of `o = [Z_2 ⊕ Z_2]`. If
`A ∈ SL_2(Z[1/(2m)])` satisfies `A Z_2^2 = λ Z_2^2`, then `λ^2` is a unit, so `A ∈ SL_2(Z_2)`
and its entries lie in `Z[1/m]`. `Γ_0` is the stabilizer of the directed edge of the tree whose
shadow is `Z_2`.

**`Z^d ∈ B_A`.** `Z^d` embeds in `V` by elements with disjoint supports, and `V` has a type (A)
clopen action (`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`). ∎
