---
rg: 2
id: nonsingular-injectivity-passes-to-proper-power-relators
kind: claim
title: Coefficient injectivity for a relator passes to its proper powers, even at non-amenable shapes
distinct_from:
  torsion-free-amenable-t-shape-adjunctions-are-aspherical: that is injectivity and asphericity at amenable t-shapes; this gives injectivity at the proper-power shapes, which are never amenable and where the Forester--Rourke Main Theorem is not available.
  nonsingular-coefficient-kernel-in-locally-indicable-residual: that controls the kernel through quotients of the coefficient group; this changes the relator, not the coefficient group.
artifacts:
  - research/artifacts/kl-nonamenable-shapes-2026-09-13.md
---

Let `G` be a group, `u in G * <t>` and `k >= 1`, and put `w = u^k`. Then:

1. `deg_t(w) = k deg_t(u)`, so `w` is nonsingular exactly when `u` is.
2. If `G -> G_u = (G * <t>)/<<u>>` is injective, then so is
   `G -> G_w = (G * <t>)/<<w>>`.
3. **Torsion-free corollary.** Let `G` be torsion-free and `u` cyclically
   reduced with amenable `t`-shape `S`. Then `G -> G_(u^k)` is injective for
   every `k >= 1`. The `t`-shape of `u^k` is the cyclic word `S^k`, and for
   `k >= 2` it is not amenable. Forester--Rourke state "no t–shape which is a
   proper power is amenable" (arXiv:math/0306088, `pi-two.tex` l.384–385).

So the proper-power shapes that come from proper-power relators are not an
obstruction. What remains open at proper-power shapes is the case where `w`
has shape `S^k` but is not itself a proper power, because the coefficients
between the repeated blocks differ.
