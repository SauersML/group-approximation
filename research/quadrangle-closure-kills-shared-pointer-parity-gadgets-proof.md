---
rg: 2
id: quadrangle-closure-kills-shared-pointer-parity-gadgets-proof
kind: route
title: Coherent shifts become one fixed-point-free partial permutation whose triple sites come in 3-cycles, and inclusion-exclusion gives the residue
target: quadrangle-closure-kills-shared-pointer-parity-gadgets
requires: []
artifacts:
  - research/artifacts/cancellative-firewall-reverification-2026-09-17.md
  - experiments/cancellative-firewall-2026-09-17/verify_gadget.py
  - experiments/cancellative-firewall-2026-09-17/verify_gadget.json
---

Complete direct proof, Section 4 of the artifact. Indices are mod 3.

1. **The three shift forms agree.** For positions `e, r`, the statements `W_2 e = W_1 r`, `W_3 e = W_2 r` and
   `W_1 e = W_3 r` are equivalent.
   - For the first implication apply (Q) with `(c, c') = (W_1, W_2)`, the instance `(u, u')`, `(r, r') = (r, e)`, and
     `(d, d') = (W_2, W_3)`, using `W_2 u = W_3 u'`.
   - The other two implications are the cyclic shifts.
2. **A partial permutation.** Write `pi(e) = r` when they hold. By (L), `pi` is a partial injection. By (R) it has no
   fixed points.
3. **Pairwise intersections.** Pairs (site, pair of codewords containing it) correspond bijectively to (arrow of `pi`,
   type), with site `W_(i+1) e = W_i pi(e)`. So `sum_(i<j) |W_i E ∩ W_j E| = 3A`, where `A` is the number of arrows.
4. **Triple sites.** Suppose `s = W_1 e_1 = W_2 e_2 = W_3 e_3`. Then `pi(e_2) = e_1`, `pi(e_3) = e_2` and
   `pi(e_1) = e_3`: a 3-cycle. Conversely, every position `x` on a 3-cycle gives a triple site `W_1 x`. So the number
   of triple sites is `T = 3C`, where `C` is the number of 3-cycles.
5. **Inclusion-exclusion.** `|Δ| = 3|E| - 6A + 4T ≡ T ≡ 0 (mod 3)`.
6. **Corollary.** Define `sigma_ij` on `P` by `W_i sigma_ij(p) = W_j p`.
   - By (R) each `sigma_ij` is a 3-cycle.
   - `sigma_13 = sigma_12 sigma_23` is fixed-point-free, so `sigma_12 = sigma_23 = sigma_31 = tau`.
   - So `(tau(p), p)` is a coherent shift.
   - The pointer sites lie in all three windows and, by (L), in no value window. So `|Δ_val| = |Δ| - 3`.

**Checks** (`verify_gadget.json`):
- **Exhaustive enumeration** of 3-row cancellative patterns with `|E| <= 4` (30240 patterns at `|E| = 4`). Every
  pattern with (Q) and a coherent shift has `|Δ| ≡ 0 (mod 3)`. Without (Q) the values `2` and `4` occur.
- **Random group patterns:** 3000 in `Z/3 x Z/n`, all with residue `0`.
- **The Theorem A gadget:** it violates (Q), with 6 bad shift-relation pairs in gadget 0.
