---
rg: 2
id: two-cell-core-deletions-need-a-unit-fox-coefficient-proof
kind: route
title: Proof that the two-cell core presentation has pi_2 = ZG on an explicit sphere, that admissibility is unimodularity of its cylinder row, and that one-cell deletion needs a unit coordinate, impossible when ab != 0
target: two-cell-core-deletions-need-a-unit-fox-coefficient
requires:
  - core-relation-elimination-bounds-relative-defect
  - relative-realization-is-relative-efficiency
  - non-proper-power-one-relator-complexes-are-aspherical
artifacts: []
---

Notation is as in the claim. All modules are left `ZG`-modules, and `ZG` acts on row vectors from the
left. Fox derivatives are evaluated in `ZG` through `F(B ∪ S) → G`, where `x ↦ φ(x)` for `x ∈ B`.
For a one-vertex 2-complex `⟨A | R⟩` with `π_1 = G`, the cellular chain complex of the universal
cover is `ZG^R → ZG^A → ZG`. The first map sends `ρ̃` to `Σ_a (∂ρ/∂a) ã`. Hence
`π_2 = H_2 = { Σ_ρ λ_ρ ρ̃ : Σ_ρ λ_ρ ∂ρ/∂a = 0 for all a ∈ A }`.

Two facts are used throughout.

- **(Schanuel)** Theorem 1 of `relative-realization-is-relative-efficiency`: a finite 2-complex
  `Y` with `π_1 Y ≅ G` and `χ(Y) = χ(G)` is aspherical.
- **(Lyndon)** By `non-proper-power-one-relator-complexes-are-aspherical`, `χ(G) = 2 - |S|`.

**Reduction to one vertex.** As in the elimination proof, collapsing a maximal tree of `C^1` and
then changing the free basis is a homotopy equivalence of 1-skeleta. It extends over the 2-cells,
bijectively and compatibly with attaching maps up to homotopy. So `C ≃ K_B = ⟨B | u_0, u_1⟩`.
Moreover `Y_1^B` is homotopy equivalent to the complex built on `C` with cylinders along the loops
`x ∈ B`, and the equivalence respects the 2-cell correspondence. Both the `π_2`-module and the
coefficient of a class on a given 2-cell orbit are preserved. The coefficient is the image under
`H_2(Ỹ) → H_2(Ỹ, Ỹ ∖ (open lifts of that cell)) ≅ ZG`. So it suffices to work with the one-vertex
complexes. By the swap lemma (Theorem 2(c) of `relative-realization-is-relative-efficiency`),
realizing `H` over `K_B` is the same as realizing it over `C`.

## Step 0: `π_1` and defect

`π_1(Y_1^B) = ⟨B, S | u_0, u_1, x = φ(x)⟩`. Eliminating `B` gives `⟨S | φ(u_0), φ(u_1)⟩`. Each
`φ(u_j)` is conjugate to `w^{±1}`, so this is `⟨S | w⟩ = G`. The restriction to `π_1 K_B = H` is
the inclusion, because `x ↦ φ(x)`. Also

`χ(Y_1^B) = 1 - (r + |S|) + (2 + r) = 3 - |S| = χ(G) + 1`.

## Step 1: `g ∉ H`

By definition `g = t_1 t_0^{-1}` satisfies `φ(u_1)^{ε} = t_1 w^{ε_0} t_1^{-1} = g φ(u_0) g^{-1}`.

Suppose the image of `g` in `G` lay in `H`. Then `g ∈ H̃ = π_1(X_H^1, v)`, which is the full
preimage of `H` in `F(S)`. Write `t_1 = h t_0` with `h ∈ H̃`. Lift the path labelled `t_1` from
`v` in the covering graph `X_H^1`. It first runs around the closed loop `h`, then along `t_0`, so
it ends at `v_0`. Hence `v_1 = v_0`.

Now `X` has one vertex and one 2-cell. So each vertex of `X_H` is the base vertex of exactly one
lift of the 2-cell (the lift whose boundary reads `w` from that vertex). Therefore `e_1 = e_0`,
a contradiction.

## Step 2: proof of (U1)

Let `Y' = Y_1^B ∖ e_1`. Its fundamental group is `⟨B, S | u_0, x = φ(x)⟩ = ⟨S | φ(u_0)⟩ = G`.
The map `π_1 Y' → π_1 Y_1^B` is the quotient by the class of `u_1`, which is already trivial:
`u_1 ≡ φ(u_1)` modulo the cylinders, and `φ(u_1)` is conjugate to `φ(u_0)^{±1}`. So `π_1 Y' → G`
is an isomorphism. Since `χ(Y') = χ(G)`, Schanuel shows that `Y'` is aspherical.

Now consider the pair `(Ỹ_1, Ỹ')`, where `Ỹ'` is the preimage of `Y'`. It is the universal cover
of `Y'`, since `π_1` is unchanged. Its long exact sequence reads

`0 = H_2(Ỹ') → H_2(Ỹ_1) → H_2(Ỹ_1, Ỹ') = ZG ẽ_1 → H_1(Ỹ') = 0`.

So the `e_1`-coefficient map `π_2(Y_1^B) → ZG` is an isomorphism. The generator is the unique
2-cycle with `e_1`-coefficient 1.

To identify it, look for `σ = ẽ_1 + λ ẽ_0 + Σ_x c_x r̃_x`. The relevant Fox derivatives are:

- `∂r_x/∂x' = δ_{xx'}`;
- `∂r_x/∂s = -x φ(x)^{-1} ∂φ(x)/∂s = -∂φ(x)/∂s` in `ZG`;
- `∂u_j/∂s = 0`.

The cycle equations are therefore

- (at `x'`) `∂_{x'} u_1 + λ ∂_{x'} u_0 + c_{x'} = 0`;
- (at `s`) `Σ_x c_x ∂φ(x)/∂s = 0`.

Substitute the first equation into the second and use the chain rule
`Σ_x (∂_x u)(∂φ(x)/∂s) = ∂φ(u)/∂s`. The second equation becomes

`∂φ(u_1)/∂s + λ ∂φ(u_0)/∂s = 0`.

For `V` trivial in `G` and any `k`, one has `∂(kVk^{-1})/∂s = k ∂V/∂s` and `∂(V^{-1})/∂s = -∂V/∂s`
in `ZG`. Hence `∂φ(u_1)/∂s = ε g ∂φ(u_0)/∂s`, and `λ = -εg` solves the system. This gives
`c_x = εg ∂_x u_0 - ∂_x u_1`, and `σ` generates. ∎

**Remark.** `c ≠ 0`. Otherwise `ẽ_1 - εg ẽ_0` would be a nonzero 2-cycle in the universal cover of
the aspherical complex `K_B`.

## Step 3: proof of (U2)

`Y_1^B ⊇ K_B` is a relative presentation with no extra vertices. By Theorem 2' of
`relative-realization-is-relative-efficiency`, the pair is admissible iff `π_2(Y_1^B)` is a direct
summand of `C_2(Ỹ_1, K̃) = ⊕_x ZG r̃_x`. The inclusion sends `σ ↦ c`. It is injective, since
`π_2 ≅ ZG` and `ZG` has no zero divisors (see Step 5; `c ≠ 0` suffices once `ZG` is a domain).

A cyclic free submodule `ZG c` is a direct summand of `ZG^B` iff some `ZG`-linear
`f: ZG^B → ZG` has `f(c) = 1`. Every such `f` has the form `e_x ↦ d_x`, so `f(c) = Σ_x c_x d_x`.
This is unimodularity. ∎

**Consistency check.** The augmentation is `ε(c_x) = (εa - b) p_x = -ε_0 · deg · p_x`, where
`deg = bε_0 - aε_1`. Unimodularity forces `deg · gcd_x(p_x) = ±1`. This recovers the degree-one
statement (3a) of `two-cell-injective-maps-realize-relative-eg-pairs`.

## Step 4: proof of (U3)

Let `P = P_y^B = Y_1^B ∖ r_y`, `Q = π_1 P`, and `N_y = ker(Q → G)`. Then `N_y` is the normal
closure of `r_y`, and `Q → G` is onto. Let `P̂ ⊂ Ỹ_1` be the preimage of `P`. It is the connected
cover of `P` with group `N_y`, so `H_1(P̂) = N_y^{ab}`. The pair sequence reads

`π_2(Y_1^B) = H_2(Ỹ_1) → H_2(Ỹ_1, P̂) = ZG r̃_y → H_1(P̂) → H_1(Ỹ_1) = 0`.

The first map is `σ ↦ c_y`. So `N_y^{ab} ≅ ZG / ZG c_y`.

- If `c_y` is a unit, then `N_y^{ab} = 0`, so `N_y` is perfect.
- Conversely, if `N_y` is perfect, then `ZG c_y = ZG`, so `d c_y = 1` for some `d`. In a domain
  where every element with a one-sided inverse is a unit (Step 5), `c_y` is then a unit.

If `P` presents `G`, then `N_y = 1`, and `χ(P) = χ(G)` makes `P` aspherical by Schanuel. Since `P`
contains `K_B`, this gives `RP(H,G)` by Theorem 2 of `relative-realization-is-relative-efficiency`.
Conversely, if `c_y` is a unit and `N_y = 1`, then `P` presents `G`. ∎

## Step 5: proof of (U4)

**Units.** Torsion-free one-relator groups are locally indicable (Brodskii 1984; Howie 1982). By
Higman's theorem (1940), for a locally indicable group `G` the ring `ZG` has no zero divisors and
only the trivial units `±k` (`k ∈ G`). Higman's argument also shows that one-sided inverses are
trivial units, since `ZG` is then a domain in which `ab = 1` forces `a, b` to be trivial units.
(Alternatively: group rings are directly finite, by Kaplansky.)

**Support.** Put `α = ∂_y u_0` and `β = ∂_y u_1`, both in `ZH`. As abelian groups,
`ZG = ⊕_{kH ∈ G/H} Z[kH]`. Here `εgα` is supported in the coset `gH`, and `β` in `H`. These cosets
differ by Step 1. So the support of `c_y = εgα - β` is the disjoint union of the supports of `gα`
and `β`, with no cancellation. Now `c_y = ±k` has support of size one. Hence either `α = 0` and
`β = ∓k ∈ ±H`, or `β = 0` and `εgα = ±k`, that is `α ∈ ±H`. Conversely, each of these makes `c_y`
a trivial unit.

**Degree-one form.** The augmentations are `ε(α) = [u_0]_y = a p_y` and `ε(β) = b p_y`.

- In the first case, `a p_y = 0` and `b p_y = ±1`. So `p_y = ±1 ≠ 0`, hence `a = 0` (and `b = ±1`).
- The second case gives `b = 0` in the same way.

So a unit coordinate forces `ab = 0`. As `B` and `y` were arbitrary, if `ab ≠ 0` then no
`P_y^B` presents `G`. By (U3) this is equivalent to saying that
`⟨S, y | λ(u_0), λ(u_1)⟩ → G` is not an isomorphism. ∎

## Step 6: proof of (U5)

Replace `r_x` by `r'_x = r_x · k ρ^{±1} k^{-1}`, where `ρ` is another relator. In the relation
module, `[r'_x] = [r_x] ± k[ρ]`. Rewriting `σ = Σ λ_τ [τ]` in the new relators changes only the
coefficient of `ρ`, which becomes `λ_ρ ∓ λ_τ k`. So:

- if `ρ = r_{x'}`, then `c_{x'} ↦ c_{x'} ∓ c_x k`;
- if `ρ ∈ {u_0, u_1}`, then `c` is unchanged.

Replacing `r_x` by a conjugate or an inverse multiplies `c_x` by a trivial unit on the right.
Steps 4 and 5 apply verbatim to any such modified cylinder system: deleting its cell `r'_y` presents
`G` iff `c'_y` is a unit and the kernel is trivial. The support argument of Step 5 used only that
`c_y` has the specific form `εgα - β` with `α, β ∈ ZH`. Column operations with `k ∉ H ∪ gH`
destroy that form. ∎

## Search (evidence only)

The scripts are in `experiments/two-cell-core-ratio-2026-09-17/`, and the outcomes are in its
`RESULTS.md`. They search for folded graphs carrying two distinct w-cycles with dependent homology
classes of ratio `a : b`, `ab ≠ 0`, `|a| ≠ |b|`. No instance was found. This proves nothing beyond
the enumerated range.
