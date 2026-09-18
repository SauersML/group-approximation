# Adversarial check: Tarocchi's question "Is [G_3, G_3] simple?" (`dendrite-rearrangement-group-g3-has-simple-commutator-subgroup`) (bh-refute, 2026-09-18)

This is a coordinator-assigned item. Verdict: **PASS**.

I re-derived the lane step, which is exactly what Tarocchi's Remark `rmk:3:comm:simple` says is missing: showing
that `τ_2τ_3 ∈ N`. The imported facts (E) and (R), and the generating set of `G'`, are taken from arXiv:2310.14660v3
as quoted. Tarocchi states that "every other step of the proof works" for `n = 3`.

## Checks

- **The `ρ_x` are elements.**
  - In `𝒟_3`, a cell `C(x)` expands into `x1` (in), `x2` (to the old terminal vertex) and `x3` (to a new leaf).
  - For `x = 12, 22, 312`, both `C(x2)` and `C(x3)` run from the centre of `C(x)` to leaves. So swapping them is
    a graph automorphism of an expansion, hence a rearrangement.
  - `Φ(ρ_x) = (1,0)`: one transposition at one branch point, and endpoint derivatives that cancel.
- **Step 1.**
  - `τ_2`, `ρ_12` and `σ = ρ_312` are supported in the branch `B` at the centre `q` of `C(3)` that contains `p_0`.
    `τ_2` fixes `C(3)` pointwise, and `C(312) ⊂ C(31)`.
  - `a = τ_2σ` and `b = ρ_12σ` have `Φ = 0`.
  - With `[a,b] = aba^{-1}b^{-1}` and `σ` central among these involutions, `[a,b] = τ_2ρ_12τ_2ρ_12 = ρ_22ρ_12 = Y`.
  - (E) gives `Y ∈ N`.
- **Step 2.** Compositions are right to left.
  - `c = τ_2τ_3` sends `C(2)` onto `C(1)`, so `c^{-1}ρ_12c = ρ_22` and `ρ_12cρ_12 = cY`.
  - For `g = τ_2ρ_12 ∈ G'`: `gcg^{-1} = (τ_2cτ_2)(τ_2Yτ_2) = c^{-1}Y`, using `τ_2cτ_2 = τ_3τ_2 = c^{-1}` and
    `τ_2Yτ_2 = ρ_12ρ_22 = Y`. The two factors of `Y` commute, having disjoint supports.
- **Step 3.** `G'/N = ⟨cN⟩` is abelian, so `c ≡ gcg^{-1} ≡ c^{-1}` and `c^2 ∈ N`. With `c^3 = 1` this gives `c ∈ N`.

## Attacks tried (all failed)

- **The conjugator `g` lying outside `G'`.** `Φ(g) = (1,0)+(1,0) = 0`.
- **`[a,b]` computed with the other commutator convention.** The result is the same, since everything here is an
  involution and `ρ_12`, `ρ_22` commute.

## Lesson for general BH

When all generators of `G'` but one torsion element `c` are known to lie in a nontrivial normal `N`, `G'/N` is
cyclic, hence abelian. Then any `g ∈ G'` that conjugates `c` to `c^{-1}` modulo `N` gives `c^2 ∈ N`, and odd order
finishes the argument. This is a reusable last step for simplicity of commutator subgroups of rearrangement
and full-group hosts, the step every BH host construction needs. It replaces "find a single rigid stabilizer
containing the whole cycle", which fails in low branching.
