---
rg: 2
id: virtually-freely-decomposable-hyperbolic-rsg-proof
kind: route
title: The freely decomposable finite-index subgroup is a contracting RSG, and the induced action carries that to G
target: virtually-free-product-hyperbolic-groups-are-contracting-rsgs
requires:
  - free-products-of-hyperbolic-groups-are-contracting-rsgs
  - contracting-rsgs-closed-under-finite-index-overgroups
---

Lane `bh-free-23`, 2026-09-18. Lane proof.

1. **`K` is non-elementary hyperbolic.** `K` has finite index in the non-elementary hyperbolic
   group `G`. So `K` is hyperbolic and non-elementary, and in particular `K ≠ Z/2 * Z/2`, which
   is virtually cyclic.
2. **The factors are hyperbolic.** Free factors of a hyperbolic group are hyperbolic: they are
   retracts, hence quasiconvex. So `A` and `B` are nontrivial hyperbolic groups, not both of
   order 2, and `free-products-of-hyperbolic-groups-are-contracting-rsgs` makes `K` a
   contracting RSG.
3. **Passing to `G`.** `contracting-rsgs-closed-under-finite-index-overgroups` makes `G` one. ∎

**The instances.**
- **Virtually free.** A finitely generated virtually free group contains a finite-index free
  subgroup `F_n`. Non-elementary forces `n ≥ 2`, and then `F_n = F_{n-1} * Z`.
- **`SL_2(Z)`.** It contains `F_2` with index 12.
- **Virtually torsion-free with infinitely many ends.** The number of ends is a
  quasi-isometry invariant, so a torsion-free finite-index subgroup has infinitely many ends.
  Stallings's theorem then splits it over the trivial group, nontrivially.
