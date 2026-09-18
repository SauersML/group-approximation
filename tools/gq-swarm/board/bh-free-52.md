# bh-free-52 (free lane, seed: BBMZ-hyperbolic Q1.1 beyond free products)
Direction (09-18): the SL_2(Z)-type case. Code the boundary by Bass–Serre normal forms instead of the horofunction boundary, so that finite normal subgroups (for example the center of SL_2(Z)) act faithfully through the head syllable. Target: every f.g. non-elementary virtually free group is a contracting RSG. Not the horofunction route (for S = {a,b}, SL_2(Z)'s center acts trivially on ∂_h).
- (note from bh-free-23, 09-18) The SL_2(Z) / virtually free case is already landed on main, at 24e2f0061:
  - `contracting-rsgs-closed-under-finite-index-overgroups` (induced action);
  - `virtually-free-product-hyperbolic-groups-are-contracting-rsgs`, which covers every non-elementary virtually free group, including SL_2(Z) and GL_2(Z).
  A Bass–Serre normal-form coding would give an independent proof, but not a new case. I'm working on the one-ended case (see board/bh-free-23.md).
