---
rg: 2
id: algebraic-atiyah-determinant-tester-proof
kind: route
title: Apply the torsion-free universal tester to the permanent class, then extract the determinant failure
target: algebraic-atiyah-and-determinant-one-group-tester
requires:
  - algebraic-atiyah-with-determinant-closed-under-colimits
  - two-generator-fp-torsion-free-master-tester
  - torsion-free-directed-colimit-recursively-presented
  - two-generator-fp-torsion-free-universal-whitehead-container
---

**Equivalence.**  By
[[algebraic-atiyah-with-determinant-closed-under-colimits]], the class `A` of
torsion-free groups satisfying `SA` and `Det` is closed under subgroups and
under directed colimits with arbitrary structure maps.  Item 6 of
[[two-generator-fp-torsion-free-master-tester]] states that for every class
with these two permanence properties, the fixed two-generator finitely
presented torsion-free group `E` lies in the class iff every torsion-free
group does.  `E` is nonsofic and non-MF by the same node.  This gives the
displayed equivalence.

**Dichotomy.**  Assume `SA(E)`.  Let `H` be torsion-free and let `A` be as in
consequence 2 of the target.  By
[[torsion-free-directed-colimit-recursively-presented]],
`H = colim_i K_i` with every `K_i` finitely generated, recursively presented
and torsion-free.  By
[[two-generator-fp-torsion-free-universal-whitehead-container]], every `K_i`
embeds in `E`, so `SA(K_i)` holds by subgroup permanence.  Run Steps 4 and 6 of
`algebraic-atiyah-determinant-colimit-proof` on this system.  Write
`mu({0}) = dim ker r_A = N + eta` with `N` an integer and `0 < eta < 1`.  The
integers `mu_j({0})` satisfy `limsup_j mu_j({0}) <= mu({0})`, so eventually
`mu_j({0}) <= N`.  For the open set `(-1, lambda^2)`, weak convergence gives
`liminf_j mu_j((-1, lambda^2)) >= mu({0})`.  So for all large `j`

```text
mu_j((0, lambda^2)) >= N + eta - eta/2 - N = eta/2 > md log(kappa) / |log(c lambda)|.
```

Step 5(iii) of the colimit proof shows that `det_(N(K_j)) r_(rho(A_j)) >= 1`
would force the opposite inequality.  Hence `Det` fails for the integral
matrix `rho(A_j)` over `K_j <= E`.

**Nonsoficity of the failing stage.**  The determinant conjecture holds for
sofic groups (Lueck, arXiv:2102.04549v2, Remark 3.11), so such a `K_j` is not
sofic.  QED
