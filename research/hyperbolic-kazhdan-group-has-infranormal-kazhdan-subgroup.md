---
rg: 2
id: hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup
kind: claim
title: A hyperbolic Kazhdan group has an infranormal non-normal Kazhdan subgroup whose defect survives modulo a Kazhdan kernel
distinct_from:
  hyperbolic-compression-centralizer-rigidity: that proves compressors normalize the finite centralizer, so the absolute defect vanishes, and leaves open whether strict compressions exist in hyperbolic groups; this shows they exist, even for infranormal Kazhdan subgroups, and that the defect survives modulo a normal Kazhdan subgroup.
  kun-thom-centralizer-normality-automatic-in-hyperbolic: that says the Kun--Thom centralizer conclusion holds automatically in hyperbolic groups; this supplies an actual infranormal non-normal Kazhdan pair there, together with its relative defect.
  infranormal-nonnormal-has-infinite-compression-orbit: that is the general infinite-orbit lemma; this is existence of such a pair inside a word-hyperbolic group.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** There are:

- a word-hyperbolic Kazhdan group `G`;
- a normal Kazhdan subgroup `N` of `G`;
- Kazhdan subgroups `N <= Gamma_hat <= G_hat <= G`, with `Gamma_hat`
  infranormal and not normal in `G_hat`, and with a strict compressor
  `u_hat Gamma_hat u_hat^-1 < Gamma_hat`.

For this rigid pair:

1. **The absolute defect is trivial.** `[g z g^-1, gamma] = 1` for all
   `g in G_hat`, `z in C_G(Gamma_hat)` and `gamma in Gamma_hat`.
2. **The defect modulo `N` is not trivial.** Some `z in G` with
   `[z, Gamma_hat] <= N`, and some `gamma in Gamma_hat`, satisfy

   ```text
   [u_hat z u_hat^-1, gamma] not in N .
   ```

`Gamma_hat` is not quasiconvex. It contains the infinite normal subgroup `N`,
so all its conjugates intersect in an infinite group. By finite height
(Gitik--Mitra--Rips--Sageev), a quasiconvex subgroup with that property has
finite index, and `Gamma_hat` has infinite index. Absolute defects are dead
in every hyperbolic group, but the compression configuration itself is not:
its defect lives exactly modulo a Kazhdan kernel.

Derivation: `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup-proof`.
Consumer: `nonsofic-hyperbolic-via-relative-rigid-defect`.
