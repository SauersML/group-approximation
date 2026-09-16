---
rg: 2
id: gap-and-floor-compatible-syndrome-separation-proof
kind: route
title: Cover each frustrated pair by its neighborhoods and defeat the resulting local gap with high-girth test vectors
target: gap-and-floor-do-not-force-compatible-syndrome-effects
requires: []
artifacts:
  - research/artifacts/gap-floor-syndrome-separation-2026-09-16.md
  - experiments/gap-floor-syndrome-separation-2026-09-16/check_separation.py
---

## Why sufficient

The artifact gives the complete proof. It is ordinary mathematics, not a
Lean certificate.

1. **Joint effects.** The joint projectors of commuting `B_a` give effects
   `E_S=W^*Pi_S W>=0` with `sum_S E_S=I` and `W^*B_aW=sum_(S containing a)E_S`.
2. **Covering.** If `T` is frustrated, every feasible `S` meets `T`, so
   exactness gives `sum_(a in T) W^*B_aW>=sum_S E_S=I`.
3. **Local frustration certificate.** Local domination and occurrence at
   most `R` then give `I<=C_0 min(|T|,R) H_(U_T)`, where `U_T` is the union
   of the neighborhoods of `T`. The same argument works for gadget labels
   through a union map with multiplicity `M`.
4. **The graph (Lemma 4).** Sample `G(n,64/n)` with
   `n>=max(100,400*64^(g-1))`. A Chernoff and union bound over colorings,
   Chebyshev for the edge count, and Markov for short cycles and high-degree
   mass show that some sample has all of the following:
   - every coloring has more than `8(n-2)` monochromatic edges;
   - fewer than `64n` edges;
   - fewer than `4*64^g` short cycles;
   - high-degree mass below `0.64n`.

   Deleting one edge per short cycle and all edges at vertices of degree
   above `512` removes fewer than `1.28n` edges. The result has girth above
   `g`, degree at most `512`, and least monochromatic fraction at least `1/10`.
5. **Parameters (Proposition 5).** The kernel of a sum of terms on distinct
   tensor factors factorizes. So a fault set is feasible exactly when:
   - the edges outside it are properly two-colorable;
   - it meets every pair `{P_j,Q_j}`, because `ker P` and `ker Q_N`
     intersect trivially.

   Diagonal edge sums and the pair eigenvalue `2/(N^2+1)` give
   `s*=tau+m_c`, `lambda_min=(tau+2m_c/d)/m` and `C_min<=11`.
6. **Test vectors (Lemma 5A).** Let `U` contain at most `g` edge terms. Its
   edges form a forest, which has a proper coloring `x`. The vector
   `|x> tensor g_N^(tensor m_c)`, with `g_N=(N,-1)/sqrt(N^2+1)`, has energy
   `|U intersection Pairs|/(N^2+1)` for `H_U`.
7. **Counting (Theorems 6 and 8).** Apply step 3 to each pair. Each union of
   neighborhoods has more than `g` edge terms or at least `(N^2+1)/(2C_0)`
   pair terms. The pairs are disjoint and the total neighborhood size is at
   most `Rm=3Rm_c`, which gives `min(g+1,(N^2+1)/(2C_0))<=3R`.
8. **Kernel resolutions (Remark 8A).** A resolution effect summed over
   labels containing `a` is a contraction supported on `ran A_a`, hence at
   most `A_a/delta`.

The Python replay checks the pair algebra, feasibility on small instances,
the Petersen graph, and the numeric constants of step 4 exactly or by explicit
logarithms. It supplements the universal arguments and does not replace them.
