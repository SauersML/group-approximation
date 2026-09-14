---
rg: 2
id: kl-p-square-system-equations-are-individually-solvable
kind: claim
title: Each equation of the p-power-index square system is solvable over the torsion-free subgroup, and so is every subsystem with pairwise disjoint unknowns
distinct_from:
  kl-p-power-index-reduces-to-p-nonsingular-square-systems: that builds the square system and shows injectivity of the coefficient group is equivalent to solvability of the whole system; this shows that single equations and variable-disjoint subsystems of it are always solvable over a torsion-free subgroup, so any obstruction lives on equations that share unknowns.
  kl-p-square-systems-are-connected-after-localization: that computes the incidence structure and rules out solving the system one new unknown at a time; this solves the parts of the system that do not interact.
  krstic-p-nonsingular-equations-inject-locally-p-indicable-groups: that solves the whole system when the subgroup is locally p-indicable; this needs only torsion-freeness but solves only non-interacting parts.
artifacts:
  - research/artifacts/hl-howie-systems-2026-09-13.md
---

Setting of `kl-p-power-index-reduces-to-p-nonsingular-square-systems`: `p` a
prime, `H <| G` with `Q = G/H` a finite `p`-group, `w in G * <t>` with
`m = deg_t(w)` prime to `p`, and the square system `{rho_q = 1 : q in Q}` over
`H` in the unknowns `Y = {y_x : x in Q}`. Assume `H` is **torsion-free**.

For each `q`, let `U_q ⊆ Y` be the set of unknowns occurring in `rho_q`, and let
the content `v_q in F(Y)` be the product of the unknown letters of `rho_q` in
order, with the coefficients deleted.

1. **Single equations.** If `v_q` is not a proper power in `F(Y)`, then the
   one-equation system `{rho_q = 1}` is solvable over `H`. Each `v_q` has
   exponent sum `m`, so at `m = ±1` this holds for every `q`.
2. **Variable-disjoint subsystems.** Let `S ⊆ Q` with the sets `U_q`,
   `q in S`, pairwise disjoint, and no `v_q` (`q in S`) a proper power. Then
   `{rho_q = 1 : q in S}` is solvable over `H`.
3. **Where a violation must sit.** Suppose `m = ±1` and `G -> G_w` is not
   injective. Then every single equation and every variable-disjoint subsystem
   of the square system is solvable over `H`, yet the whole system is not. After
   the gauge and localization of `kl-p-square-systems-are-connected-after-localization`,
   `U_q = {y_x : x in q Lambda}`, and two equations share an unknown exactly when
   `q^(-1) q'` lies in `Lambda Lambda^(-1)`. So the obstruction to
   Kervaire--Laudenbach over a torsion-free-by-finite-`p`-group coefficient group
   is carried by the edges of the Cayley graph of `Q` for
   `Lambda Lambda^(-1) \ {1}`. It is invisible to any argument that solves one
   equation at a time or amalgamates solutions of non-interacting equations over
   `H`.

## What it does and does not settle

- It isolates the gap in the torsion route: individual equations are already
  handled by Klyachko's multivariable theorem, which needs no locally indicable
  hypothesis. What is missing is compatibility of solutions across equations
  that share unknowns.
- It proves nothing about pairs of equations with a common unknown. Solving
  them one after another would need the one-relator solution groups
  `(H * F(U_q))/<<rho_q>>` to be torsion-free, or relatively free, over `H`.
  That is known under local indicability (Brodskii--Howie) but not for arbitrary
  torsion-free `H`; see the artifact.

**ESTABLISHED** through `kl-p-square-system-individual-solvability-proof`.
Elementary given the imports. Not independently reviewed; no novelty claimed.
