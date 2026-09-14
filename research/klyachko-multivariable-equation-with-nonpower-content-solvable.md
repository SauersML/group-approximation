---
rg: 2
id: klyachko-multivariable-equation-with-nonpower-content-solvable
kind: claim
title: One equation in several variables over a torsion-free group is solvable when its content is not a proper power
distinct_from:
  klyachko-kl-holds-for-torsion-free: that is the one-variable unimodular theorem; this is Klyachko's multivariable corollary, one equation with any number of variables whose variable-letter product is not a proper power in the free group.
  klyachko-kl-holds-when-all-coefficients-have-infinite-order: that allows torsion in the group away from the coefficients but handles one variable; this needs the whole group torsion-free and handles several variables at once.
artifacts:
  - research/artifacts/hl-howie-systems-2026-09-13.md
---

Let `G` be a torsion-free group and consider one equation

    g_1 x_(j_1)^(eps_1) g_2 x_(j_2)^(eps_2) ... g_n x_(j_n)^(eps_n) = 1,
    g_i in G,  eps_i in {1, -1},

in variables `x_1, x_2, ...`, indices `j_i` allowed to repeat. If the content
`prod_i x_(j_i)^(eps_i)` is not a proper power in the free group
`F(x_1, x_2, ...)`, then the equation is solvable over `G`: some overgroup of
`G` contains elements satisfying it.

**Consequence used on main.** If the exponent sum `sum_i eps_i` is `±1`, the
content is nontrivial and not a proper power, since `u^k` with `k >= 2` has
exponent sum divisible by `k`. So every one-equation, several-variable
unimodular equation over a torsion-free group is solvable over it.

**Scope.** This is one equation. It says nothing about two or more equations
sharing variables.

**ESTABLISHED** as a citation import through
`klyachko-multivariable-equation-citation`. Not independently reviewed.
