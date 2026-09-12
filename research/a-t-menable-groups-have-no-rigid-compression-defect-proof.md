---
rg: 2
id: a-t-menable-groups-have-no-rigid-compression-defect-proof
kind: route
title: Property (T) plus a-T-menability forces finiteness, and finite infranormal subgroups are normal
target: a-t-menable-groups-have-no-rigid-compression-defect
requires:
  - finite-infranormal-subgroup-is-normal
---

1. **`G` is finite.** `G <= L` inherits the Haagerup property by restricting
   a proper affine isometric action of `L`. A group with property (T) fixes a
   point in every affine isometric action on Hilbert space, and a proper action
   with a fixed point has finite point stabilizers. So `G` is finite.
2. **`Gamma` is normal in `G`.** `Gamma` is finite, and its compression semigroup
   generates `G`. By `finite-infranormal-subgroup-is-normal`, `Gamma` is
   normal in `G`.
3. **The defect vanishes.** Take `g in G`, `z in C_H(Gamma)` and `gamma in Gamma`.
   Normality gives `g^-1 gamma g in Gamma`, which commutes with `z`. Hence

   ```text
   [g z g^-1, gamma] = g [z, g^-1 gamma g] g^-1 = 1.
   ```

   Every normal generator of `D_H(G, Gamma)` is trivial. ∎

Nothing about `H` is used beyond containing `L`. The argument is uniform in
the approximation metric, which is why it rules out every row of the defect
ladder at once.
