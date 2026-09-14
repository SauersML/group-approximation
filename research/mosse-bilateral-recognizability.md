---
rg: 2
id: mosse-bilateral-recognizability
kind: claim
title: Every primitive substitution with a non-periodic fixed point is bilaterally recognizable, and long factors desubstitute uniquely away from their borders (Mossé 1996, Theorems 1 and 2)
---

**ESTABLISHED (literature import).** Let `σ` be a primitive substitution with a non-periodic fixed point `u`, let `E_1 = {0} ∪ {|σ(u[0,p−1])| : p > 0}` be its natural cutting points, and let `L_u` be its language.

1. **Bilateral recognizability.** There is `L > 0` such that if `u[i−L,i+L] = u[j−L,j+L]` and `i ∈ E_1`, then `j ∈ E_1`.
2. **Unique desubstitution.** There is `L > 0` such that if `u[i−L,j+L] = u[i′−L,j′+L]`, then `u[i,j]` and `u[i′,j′]` have the same 1-cutting and come from the same word at the ranks `i` and `i′`.

Route: `mosse-bilateral-recognizability-citation`. Consumer: `constant-length-substitution-tower-partition`.
