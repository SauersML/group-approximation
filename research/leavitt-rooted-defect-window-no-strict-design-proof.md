---
rg: 2
id: leavitt-rooted-defect-window-no-strict-design-proof
kind: route
title: Compute both product rectangles exactly, eliminate to Z * Z/2, and separate the reverse products in a finite image
target: leavitt-rooted-defect-window-carries-no-strict-design
requires:
  - two-rectangle-surjunctive-images-kill-all-designs
artifacts:
  - experiments/gk3-leavitt-nonlinear/defect_direct_tables.py
---

Notation as in `leavitt-rooted-defect-window-carries-no-strict-design`.

1. **Exact product tables** (`experiments/gk3-leavitt-nonlinear/defect_direct_tables.py`).
   Products are normal-form products in the shared checker
   `experiments/nonsofic-certificates/leavitt.py`. Dual mode recomputes every product on
   the second, prefix-table path: 288 products cross-checked, no disagreement.
   - `l^2 = 1` and `l != 1`; `a^k != 1` for `k = 1..8`; `d != 1`.
   - Forward rectangle `S x M`: 8 classes of 12. The only coincidences are
     `(1,1) = (a^-1, a)`, `(1,a) = (a,1) = (al, l)` and `(a,l) = (al, 1)`.
   - Reverse rectangle `M x S`: 10 classes of 12. The only coincidences are
     `(1,1) = (a, a^-1)` and `(1,a) = (a,1)`.
2. **The table group.** The letters are `x_a` (for `a` in `S ∩ M`), `x_(a^-1)`, `x_(al)`
   and `x_l`. The relators are:
   - `x_(a^-1) x_a = 1` and `x_a x_(a^-1) = 1`;
   - `x_a = x_(al) x_l` and `x_a x_l = x_(al)`;
   - `x_a = x_a`, which is trivial.

   Eliminate `x_(a^-1) = x_a^-1` and `x_(al) = x_a x_l`. The remaining relator
   `x_a = x_a x_l x_l` gives `x_l^2 = 1`. So `T = <x_a, x_l | x_l^2 = 1> = Z * Z/2`.
3. **Separation.** A free product of residually finite groups is residually finite.
   `T -> G` distinguishes the 10 reverse classes, so they are distinct in `T`. For each of
   the 45 pairs take a finite quotient separating it. The product of these quotients is a
   finite image separating all 10 classes.
4. **Conclusion.** Finite groups are surjunctive, so
   `two-rectangle-surjunctive-images-kill-all-designs` gives surjectivity of every `tau`
   with memory `M` that has a left inverse with memory `S`, over any alphabet. QED
