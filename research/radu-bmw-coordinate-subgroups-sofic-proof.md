---
rg: 2
id: radu-bmw-coordinate-subgroups-sofic-proof
kind: route
title: Closed vertical letter sets give virtually free and free-by-dihedral subgroups of Radu's lattice
target: radu-bmw-coordinate-subgroups-are-sofic
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - abelian-by-virtually-free-groups-are-sofic
  - sofic-kernel-amenable-quotient-permanence
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

## Why sufficient

Section 4 of the artifact.

1. **Closure.** The complete square table of the citation claim sends `y` to `y` and `{x,z}` into
   `{x,z}` when a horizontal letter is pushed through. So `A.{1,y}` and `A.D`, with `D` the reduced
   words in `x, z`, are closed under multiplication. By uniqueness of normal forms they are `P_y` and
   `P_xz`, and both are proper.
2. **`P_y`.** `y a y = a`, `y b y = c`, `y c y = b`, so `P_y = A ⋊ <y>` contains `A = C_2 * C_2 * C_2`
   with index two. It is virtually free, hence sofic, by `abelian-by-virtually-free-groups-are-sofic`
   with trivial abelian kernel.
3. **`P_xz`.** `P_xz` acts on the path `L = P_xz / A` of reduced `{x,z}`-words. Letters `a, b` fix every
   vertex and `c` flips the path, so the kernel is the index-two subgroup `A_ev` of `A` (virtually free,
   hence sofic). The quotient embeds in `Aut(L) = D_infinity`, which is amenable. So `P_xz` is sofic by
   `sofic-kernel-amenable-quotient-permanence`.
4. **Generation.** `cx = zc` makes `<A,x> = <A,z> = P_xz`, and `zaz = b`, `yby = c` make one
   horizontal letter together with `V` generate `Gamma_R`.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently from the complete square
table. Rows with `v = y` keep `y`, and rows with `v` in `{x,z}` keep `{x,z}`. In `P_xz`, `a` and `b` fix
the path and `c` reflects it, so the kernel is `A_ev` and the quotient embeds in `D_infinity`
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 5.4).
