---
rg: 2
id: orbit-finite-quotient-module-extension-fp-proof
kind: route
title: Present the extension by the relators of W, one lamp per orbit, stabilizer and double-coset commutators, and finitely many module relators
target: orbit-finite-quotient-module-extensions-are-fp
requires: []
---

Notation as in the claim. Let `W = <Y | R>` with `Y, R` finite. Let `T_i` be a finite
generating set of `H_i`, written as words in `Y`, and `D_ij` a finite set of
double coset representatives of `H_i \ W / H_j`, also written as words. Let
`κ_1, ..., κ_m` generate `K` as a module, and write each as a finite sum
`κ_l = Σ c_(l,q) e_(i_q, g_q H_(i_q))` with words `g_q` and `c_(l,q) ∈ {0, ..., p-1}`.

**Presentation.** Let `Γ^` be the group with generators `Y ∪ {x_1, ..., x_k}` and
relators

1. `R`;
2. `x_i^p` for each `i`;
3. `[x_i, t]` for `t ∈ T_i`;
4. `[x_i, d x_j d^(-1)]` for `d ∈ D_ij`;
5. `Π_q (g_q x_(i_q) g_q^(-1))^(c_(l,q))` for each `l`, in any fixed order.

This is finite.

**Step 1: `W` sits in `Γ^` as a retract.** Sending every `x_i` to `1` kills all
relators of types 2–5 and preserves `R`, so `Γ^ -> W` is a retraction of the evident
map `W -> Γ^`; hence `W <= Γ^` and `Γ^ = N ⋊ W` with `N` the normal closure of the
`x_i`.

**Step 2: conjugates are indexed by cosets.** For `g ∈ W` put `x_i^g = g x_i g^(-1)`.
Relators 3 give `h x_i h^(-1) = x_i` for every `h ∈ H_i` (induction on word length in
`T_i`), so `x_i^g` depends only on `g H_i`. The elements `x_i^(gH_i)` generate `N`.

**Step 3: `N` is abelian of exponent `p`.** Take `g, g' ∈ W` and write
`g^(-1) g' = h d h'` with `h ∈ H_i`, `d ∈ D_ij`, `h' ∈ H_j`. Then
`x_j^(g^(-1) g') = x_j^(h d) = h x_j^d h^(-1)`, and

    g^(-1) [x_i^g, x_j^(g')] g = [x_i, h x_j^d h^(-1)] = h [h^(-1) x_i h, x_j^d] h^(-1) = h [x_i, x_j^d] h^(-1) = 1

by relators 3 and 4. So all generators of `N` commute, and relators 2 make them of
order dividing `p`. Hence `N` is an `F_p`-vector space with a linear `W`-action.

**Step 4: `N` is a quotient of `V`.** By Steps 2–3 the map `e_(i, gH_i) -> x_i^(gH_i)`
extends to a surjective `F_p W`-module map `M -> N`. Relators 5 say that each `κ_l`
maps to `0`; since the kernel is a submodule, all of `K` maps to `0`. So `N` is a
quotient of `V = M/K`.

**Step 5: comparison.** In `V ⋊ W` send `Y` to `W` and `x_i` to the image of
`e_(i, H_i)`. Relators 1–5 hold there: `R` in `W`; `v_i` has order dividing `p`;
`H_i` fixes `e_(i, H_i)`; `V` is abelian; and `κ_l = 0` in `V`. So there is a surjection
`Γ^ -> V ⋊ W` that restricts to `N -> V`, which is inverse to the map of Step 4 on
generators. Hence `N ≅ V` and `Γ^ ≅ V ⋊ W`, which is therefore finitely presented.

**Consequence.** If `W` acts faithfully on `V`, an element fixing every point of `O`
fixes a spanning set, hence all of `V`; so `W` acts faithfully on `O`. Point
stabilizers on `W·v_i` are the conjugates of `H_i` (finitely generated), and
`W`-orbits on `W·v_i × W·v_j` are in bijection with `H_i \ W / H_j`. With `W`
finitely presented, BFFHZ's three conditions (arXiv:2503.21882, quoted verbatim on
`orbit-finite-affine-actions-are-type-a`) hold for `W` acting on `O`.
