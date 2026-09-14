---
rg: 2
id: small-leavitt-windows-no-strict-design-proof
kind: route
title: Build both product tables exactly, replay permutation images that separate the reverse products, and apply the two-rectangle filter
target: small-leavitt-windows-carry-no-strict-design
requires:
  - two-rectangle-surjunctive-images-kill-all-designs
artifacts:
  - experiments/gk3-leavitt-nonlinear/general_window_screen.py
  - experiments/gk3-leavitt-nonlinear/runs/gen.json
  - experiments/gk3-leavitt-nonlinear/runs/gapstage-791209.log
---

Notation as in `small-leavitt-windows-carry-no-strict-design`.

1. **Exact tables.** `experiments/gk3-leavitt-nonlinear/general_window_screen.py` builds
   each window from normal-form products in `experiments/nonsofic-certificates/leavitt.py`.
   - It lists the two-rectangle table group `T`:
     - one letter per element of `S u M`;
     - a relator for each coincidence `s m = s' m'` and each `m s = m' s'` in `G`;
     - products equal to `1` give relators with the empty word.
   - It lists one word `x_m x_s` per reverse product class.
   - Sizes are in `runs/gen.json`: letters 3 to 9, relators 6 to 40, reverse classes 6 to 30.
2. **Finite control.** For `control-gl2-1-1`, `<S u M>` closes up to a group of order 6, a
   finite image that separates trivially.
3. **Images found by GAP.** MSI job 791209 ran GAP 4 through `sagemath/10.7`
   (`runs/gapstage-791209.log`).
   - For each window it simplified `T` and ran `GQuotients` onto small simple and symmetric
     groups, then low-index coset actions.
   - It kept every image that separated more reverse classes.
   - All six gap-stage windows reached full separation with images onto PSL(3,2) acting on
     7 points: 1 to 6 images per window.
   - The images are stored as permutations of the original letters in
     `runs/gap/<window>.witness.json`.
4. **Replay, independent of GAP.** `general_window_screen.py --verify` recomputes the tables.
   For each stored image it checks that every relator of `T` holds, and it counts distinct
   signatures of the reverse classes across the images. The result:
   - 10 of 10, 20 of 20, 20 of 20, 23 of 23, 10 of 10 and 30 of 30;
   - replayed on MSI, and again locally with the checker's dual mode on, where 1214 products
     were recomputed by prefix tables with no disagreement.
5. **Product image.** The images of one window combine into a homomorphism into a finite
   direct product of copies of PSL(3,2). It separates a pair of reverse classes whenever
   one image does, so it separates all of them.
6. **Conclusion.** Finite groups are surjunctive. Apply
   `two-rectangle-surjunctive-images-kill-all-designs` to each window. QED

**Unresolved windows.** For `defect-nested-E01`, `eld1-cu-1-1` and `eld1-cu-c-1-1`, GAP
stopped at the 900 s limit after simplification (5 generators / 2 relators,
7 / 12 and 8 / 18). No image was recorded, and nothing is claimed for them.
