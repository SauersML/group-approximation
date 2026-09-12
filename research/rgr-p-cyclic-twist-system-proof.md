---
rg: 2
id: rgr-p-cyclic-twist-system-proof
kind: route
title: Proof that the twisted cyclic shift makes w(t) block-diagonal with cyclic-rotation blocks
target: rgr-p-reduces-to-cyclic-twist-system
requires:
  - rank-ultraproduct-unit-groups-solve-nonsingular-equations
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
---

Proof of `rgr-p-reduces-to-cyclic-twist-system` (artifact Section 1).

1. **Block-diagonality.** `c_i (x) 1_e` is block-scalar (`c_i` on each `W_j`). The twisted shift `t`
   sends `W_j -> W_(j+1)` by `b_j` and `t^(-1)` sends `W_j -> W_(j-1)` by `b_(j-1)^(-1)`. Reading `w(t)`
   right to left from `W_m`, each `t^(pm 1)` moves the block index by `pm 1`; the net index change over
   `w` is the total exponent `e ≡ 0 (mod e)`, so the image returns to `W_m`. Hence `w(t)` is
   block-diagonal.

2. **Block value.** Tracking the accumulated `Fbar^d` factor gives `w(t)|_(W_m) = P_m` with
   `P_m = c_0 B_1(m) c_1 ... B_l(m) c_l`, where `B_i(m)` is the product of the twists (or inverses) the
   `i`-th syllable traverses starting from the block reached so far. The index windows for
   `B_1(m), ..., B_l(m)` are the cyclic translate by `m` of those for `m = 0`.

3. **Rank additivity.** For a block-diagonal operator `rank(w(t) - lambda 1) = sum_m rank(P_m - lambda 1_d)`.
   So `w(t) = lambda 1` iff all `P_m = lambda 1`, and the `eps`-approximate form is the stated sum bound.

4. **No loss, up to one further amplification.**
   - Solving the system gives an RGR_p witness.
   - Conversely, a witness `t` at amplification `k` gives the twisted shift `t (x) S`, with every twist equal to `t`,
     at amplification `k|e|`. Then `w(t (x) S) = w(t) (x) 1`, with the same normalized error.

**Correction (w4-vf-linear-b, 2026-09-12).** An earlier version of step 4 said that solving the system is
equivalent to RGR_p at amplification `e`.
- A general witness at that amplification need not be a shift. For `c_0 t c_1 t c_2`, `t = diag(u, u)` with
  `u c_1 u = K` is one.
- The corrected form is above. For a negative total exponent, amplify by `|e|`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 30.1 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS for steps 1–3 and the corrected step 4.*

The computation is verified in full for `l = 2, e_1 = e_2 = 1` in
`two-syllable-nonsingular-words-are-exactly-solvable` (direct `2x2` block product).
