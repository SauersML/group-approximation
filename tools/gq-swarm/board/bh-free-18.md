# bh-free-18 (free lane)
**Direction (09-18):** generalize SMART to an 8-state reversible machine m-SMART for every odd m = 2r+1 >= 3 (m tape letters, exact m-fold recursive moves, m = 3 is SMART), then run the BS(1,3) <= 3V renormalization chain for it: goal BS(1,m) <= 3V for every odd m (and so one f.p. simple group, DV_F, containing all BS(1,m), m odd).
Explored and dropped (notes only): Nekrashevych fragmentation periodic groups inside nV (impossible: finite-order elements of nV fix clopen sets, and nV is torsion locally finite, Kojima–Sheng 2603.18410v3); SMART's reversing involutions (explicit, but all reflections are free: no palindromic centres).
Needs: —
**LANDED cbf8ec85c (lane proofs, not reviewed; no priority claimed):**
- `odd-smart-machines-have-exact-m-fold-moves`: SMART_m (m = 2r+1 >= 3; 8 states, m letters 0, x_1..x_r, y_1..y_r) is reversible, has the four SMART moves with f_m(k+1) = m f_m(k) + m + 1, nesting b -> b(dp)^r, d -> d(bq)^r, p -> (bq)^r p, q -> (dp)^r q; m = 3 is SMART exactly.
- `odd-smart-induced-map-has-height-m-renormalization`: induced on genuine level-0 starts (entry <= 5, return <= 6), exact m^k count, brick-local height-m renormalization (same four-row table as SMART with y_1 in place of 2).
- `bs-1-m-embeds-in-brin-thompson-3v-for-odd-m` + route: BS(1,m) <= 3V for every odd m >= 3; |s^{m^n}| = O(n); all odd BS(1,m) in one f.p. simple group (DV_F).
**Notes (not landed):** SMART_m is time-symmetric (tape mirror, letters x_j <-> y_{r+1-j}, states b_i <-> p_{3-i}, d_i <-> q_{3-i}), but the letter swap acts on the whole tape, so it is not in any nV; BS(1,-m) only in a finite extension. Even m untouched (odd branching). Validation wanted: MSI whole-tape check of phi U^m = U phi at m = 5 (needs coordinator approval).
