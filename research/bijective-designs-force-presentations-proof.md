---
rg: 2
id: bijective-designs-force-presentations-proof
kind: route
title: Shift key tracks, shear the data track, and share one decoder address per relator
target: bijective-designs-force-every-finite-presentation
requires: []
artifacts:
  - research/artifacts/bijective-forcing-of-table-cores-2026-09-12.md
---

Sections 1 to 4 of the artifact, in five steps.

1. **Holonomy shape (Lemma 1).** Tietze moves put every finite presentation in the
   form `u v^-1 = w z^-1`, with letters in `X ∪ {1}`.
2. **Construction (Section 2).**
   - The encoder translates key track `a_r` by `v_r` and `b_r` by `z_r`, and adds
     `sum_r x_(a_r)(g u_r) x_(b_r)(g w_r)` to the data track.
   - The decoder reads `a_r` at `v_r^-1`, `b_r` at `z_r^-1`, and both key tracks of
     relator `r` at `h_r = u_r v_r^-1`.
3. **Principal forward table (Lemma 2).** The composite reads only the listed cells.
   Each needed identification is forced by an explicit symbol assignment on
   disjoint tracks. So every forward-sufficient partition dominates `E`.
4. **Table group (Lemma 3).** Eliminating the three private decoder letters of each
   relator leaves exactly the relators of `P`.
5. **Bijectivity (Lemma 4).** The encoder is a translation of the key tracks followed
   by a shear of the data track by key values. Both are invertible over every group.
