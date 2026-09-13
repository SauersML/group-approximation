---
rg: 2
id: fpbs-free-product-block-tree-spectral-proof
kind: route
title: Weight the Schur test by a Busemann function on the block tree and bound down paths by the type matrix
target: fpbs-free-product-cayley-graphs-have-critical-l2-gap
requires: []
artifacts:
  - research/artifacts/fpbs/docs/free-product-critical-l2-2026-09-12.md
---

Notation as in the target. Section 2 of the artifact has the full proof. There
are two imports, both quoted in arXiv:1804.10191:

- sharpness, the display before Proposition 2.3: for quasi-transitive graphs,
  `||T_p||_{1->1} < infinity` if and only if `p < p_c`;
- Corollary 2.6: `||T_p||_{2->2} >= (1-p)/(||A||_{2->2}(p_{2->2}-p))` for
  `p < p_{2->2}`.

1. **Block tree.** The elements and the cosets `gH_i` form a tree `Tr`, by the
   normal form theorem.
   - If `u^{-1}v = h_1 ... h_m` in normal form, then
     `tau_p(u,v) = prod_k a_{i_k,p}(h_k)`. Here `a_{i,p}(h)` is the probability
     that `e` and `h` are connected in `Cay(H_i,S_i)`.
   - Every open path from `u` to `v` passes the cut vertices of the geodesic in
     order. A self-avoiding one stays inside each block between them
     (Lemma 2.1).
2. **Type matrix.** Put `m_i(p) = sum_{h != e} a_{i,p}(h)`, `Q_{ij} = m_i [i != j]`
   and `m = (m_i)`. Then `chi_p = 1 + sum_{l>=1} 1^T Q^{l-1} m`, which is
   Kozáková's formula.
   - Below `p_c`, `chi_p < infinity` forces `rho(Q(p)) < 1` and `p m_i(p) < 1`.
   - Each `m_i` is lower semicontinuous and nondecreasing, hence left
     continuous. So `m_i(p_c) <= 1/p_c` and `rho(Q(p_c)) <= 1`.
   - Also `p_c < 1` (Lemma 2.2).
3. **Weight.** Fix an end of `Tr`, let `b` be its Busemann function, and put
   `phi = theta^{b/2}` on the elements. Each geodesic
   `u = g_0, B_1, g_1, ..., B_m, g_m = v` consists of `j` up steps, at most one
   across step, and then `l` down steps. Also `phi(v)/phi(u) = theta^{l-j}`.
4. **Bound.** Put `alpha = max_i sup_{h != e} a_{i,p_c}(h) < 1`, and fix
   `theta in (alpha,1)`.
   - Up steps are forced, and each contributes at most `alpha`.
   - An across step contributes at most `M = max_i m_i(p_c)`.
   - `l` down steps contribute at most `nM ||Q(p_c)^{l-1}||`.

   So `T_{p_c} phi <= lambda phi`, where
   `lambda = (1+M)(1 + nM theta C_theta)/(1 - alpha/theta)` and
   `C_theta = sum_{l>=0} theta^l ||Q(p_c)^l||`. Since `rho(Q(p_c)) <= 1`,
   `C_theta < infinity`.
5. **Schur test.** Let `K` be a nonnegative symmetric kernel, and suppose a
   positive `phi` has `K phi <= lambda phi`. Then `||K||_{2->2} <= lambda`, by
   Cauchy–Schwarz. So `||T_{p_c}||_{2->2} <= lambda`.
6. **Conclusion.** For `p < p_c`, step 5 with `phi = 1` gives
   `||T_p||_{2->2} <= chi_p`, and `chi_p` is finite by sharpness. So
   `p_c <= p_{2->2}`. If they were equal, Corollary 2.6 would make
   `||T_{p_c}||_{2->2}` infinite, contradicting step 5. Corollary 2.6 at `p = p_c`, with `||A||_{2->2} <= |S|`, gives the
   quantitative gap. The triangle condition follows from
   `nabla_{p_c}(v) = T_{p_c}^3(v,v) <= ||T_{p_c}||_{2->2}^3`.
7. **Example.** Let `H = H_3(Z)`, with a generating set `S_H` from Leemann–de la
   Salle (arXiv:2010.06020, Theorem `thm:main`), so that
   `Aut(Cay(H,S_H)) = H`. Let `K = Z/2`. (Section 3.)
   - Every simple cycle lies in one block.
   - A one-ended vertex-transitive graph has no cut vertex. So the `a`-edges are
     exactly the edges on no cycle, and every automorphism preserves labels.
   - So `Aut(X) = Gamma`, and `X` has no nonunimodular automorphism subgroup.
   - `X` contains `Z^2`, has cut vertices, and has `rho(X) >= 4/5` by Kesten's
     theorem applied inside `H`.
