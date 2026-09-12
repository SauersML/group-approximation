---
rg: 2
id: fournier-facio-rigid-defect-proof
kind: route
title: The compressors generate G from Gamma and push the centralizing copy J back onto a centreless simple group
target: fournier-facio-group-carries-rigid-defect
requires:
  - fournier-facio-torsion-free-skeleton
---

The skeleton (Fournier--Facio, arXiv:2608.02025, Section 2) gives:

- `Gamma` and `G` have property (T);
- `G = <Gamma, t_1, t_2>` and `t_i Gamma t_i^-1 <= Gamma`;
- `[Gamma, J] = 1` and `t_1 J t_1^-1 = pi(S)`, with `pi|_S` injective.

1. **Infranormal.**  The compression semigroup
   `P_Gamma = {g in G : g Gamma g^-1 <= Gamma}` contains `Gamma`, `t_1` and
   `t_2`, and these generate `G`.
2. **A nontrivial generator of the defect.**  `J <= C_G(Gamma)`.  For
   `1 != s in S` put `z = t_1^-1 pi(s) t_1 in J`, so `t_1 z t_1^-1 = pi(s)`.
   `pi(S) ~= S` is infinite, simple and nonabelian, hence centreless, so some
   `gamma in pi(S) <= Gamma` has `[pi(s), gamma] != 1`.  With `g = t_1`, this
   is a nontrivial generator of `D_G(G, Gamma)`.
3. **Saturation.**  `D_G(G, Gamma)` is normal in `G` and contains the
   nontrivial element `[pi(s), gamma]` of `pi(S)`.  So it contains the normal
   closure of that element in `pi(S)`, which is `pi(S)` by simplicity.
4. **Not normal.**  If `Gamma` were normal in `G`, then for `z in C_G(Gamma)`
   and `g in G` we would have `g z g^-1 in C_G(g Gamma g^-1) = C_G(Gamma)`,
   and every generator of the defect would be trivial, contradicting step 2.
