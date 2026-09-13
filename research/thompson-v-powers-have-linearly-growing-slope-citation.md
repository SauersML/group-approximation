---
rg: 2
id: thompson-v-powers-have-linearly-growing-slope-citation
kind: route
title: Import the slope computation from the proof of Theorem 1.3 of Bleak et al.
target: thompson-v-powers-have-linearly-growing-slope
requires: []
---

Citation import. C. Bleak, H. Bowman, A. Gordon, G. Graham, J. Hughes, F. Matucci,
E. Sapir, *Centralizers in the R. Thompson group V_n*, arXiv:1107.0672v3, Section 8
("Cyclic subgroup (non)distortion"), proof of Theorem 1.3, pages 30--31. Read from the
arXiv PDF on 2026-09-12 by lane `ex-q34-leavitt-hs`.

**Set-up (page 30).** "Suppose alpha in V_n and that <alpha> ~= Z." With a representative
revealing pair `(A,B,sigma)` of `alpha`, "let r be a repeller for this tree pair". The
repeller has iterated augmentation chain `r = r_0, r_i = r_0 alpha^i` for `0 <= i <= u`.
`L_r` is the length of the spine `Gamma_r` of the complementary component containing `r`.
The jumps `J_(r,i)` in depth between consecutive `r_i` have total sum zero, and
`S_(r,z)` is the partial sum of the first `z mod u` jumps.

**Estimate (page 31).** "Now fix a particular positive integer z. Set w = floor(z/u) ...
if y_i is the repelling periodic point under the leaf r_i for 0 <= i < u, direct
calculation shows that the slope of alpha^z at y_0 is
((2n-1)^(L_r))^(w+1) (2n-1)^(S_(r,z))." The paper then uses the chain rule to bound the
word length of `alpha^z` below by an affine function of `z`, and states that "A similar
argument produces an affine distortion function f_neg" for negative powers.

**Reading.** `S_(r,z)` is a partial sum of `u` fixed jumps, so `|S_(r,z)| <= C`. `L_r >= 1`
is the length of a spine. The base `2n-1` is the scaling of the paper's realization of
`C_n` inside the interval, where each `n`-caret keeps `n` of `2n-1` subintervals
(Section 2.1). So the exponent `e(z) = L_r (w+1) + S_(r,z)` grows linearly in `z`. The
existence of a repeller for an infinite-order element is part of the revealing-pair
technology the paper imports from Brin and Salazar-Diaz, and its proof takes it as given.
