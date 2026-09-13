---
rg: 2
id: sl3z-parabolic-subgroups-are-coherent-proof
kind: route
title: The maximal parabolics of SL_3(Z) are Z^2 by GL_2(Z), which is polycyclic-by-coherent
target: sl3z-parabolic-subgroups-are-coherent
requires:
  - coherence-passes-to-polycyclic-by-coherent-extensions
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md
---

1. **Reduction to `P_1` and `P_2`.** A rational line meets `Z^3` in `Zv` with
   `v` primitive. A rational plane meets `Z^3` in a rank-two direct summand. A
   basis of either extends to a basis of `Z^3`, and one sign change puts the
   change of basis in `SL_3(Z)`. So a subgroup preserving a rational line or
   plane is conjugate into `P_1` or `P_2`.
2. **Structure of `P_1`.** Write `P_1 = { [[a, x], [0, B]] : a = ±1,
   B ∈ GL_2(Z), a·det B = 1, x ∈ Z^{1×2} }`. The map `g ↦ B` is a surjection
   onto `GL_2(Z)` with kernel `{[[1, x], [0, I]]} ≅ Z^2`.
3. **Coherence.** `GL_2(Z)` is virtually free, and virtually free groups are
   coherent: a finitely generated subgroup meets a finite-index free subgroup
   in a finitely generated free group. `Z^2` is polycyclic. So `P_1` is
   coherent by `coherence-passes-to-polycyclic-by-coherent-extensions`.
4. **`P_2`.** The same argument applies to `P_2 = { [[B, y], [0, a]] }`.
5. **Subgroups.** Coherence passes to subgroups.

This is Proposition 2.1 of the artifact.
