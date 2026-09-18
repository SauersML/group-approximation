---
rg: 2
id: quadrangle-closed-patterns-do-not-force-domination-proof
kind: route
title: Open pointer rotation with shifts a, a, -2a along a Hamiltonian value cycle, distinct translation types per class, and an exact coupon residual
target: quadrangle-closed-patterns-do-not-force-domination
requires: []
artifacts:
  - research/artifacts/quadrangle-closed-pattern-firewall-2026-09-17.md
  - experiments/quadrangle-firewall-2026-09-17/verify_rotation_gadget.py
  - experiments/quadrangle-firewall-2026-09-17/verify_rotation_gadget.json
---

Complete direct proof, §§1-6 of the artifact. It is elementary and self-contained, with no prerequisites.

1. **Lemma 1.1.** Under (L) and (R), (Q) holds iff classes of distinct row pairs are disjoint or equal. The
   diagonal classes `R(c, c)` meet only diagonal classes, by (R).
2. **Construction (§2).**
   - **Parameters.** `L` prime with `L > 16R`. Greedy shifts `a_rho` whose sets `{±a, ±2a}` are pairwise
     disjoint of size 4; each choice excludes at most 16 residues. `n` prime with `n >= R^2 + R + 1`,
     steps `c_rho = rho + 1` and points `z_rho = rho(R + 1)`.
   - **The table.** Three explicit bijections from the value positions to value sites, with only `o` read
     once.
3. **(L) and (R) (§3).** Proved column by column. The `z_rho` are distinct because `(rho - rho')(R + 1)` has
   absolute value at most `R^2 - 1 < n`.
4. **(Q) (§4).**
   - The nonempty classes are `tau_rho = T_(a) ∪ N_c(Sg)` (equal to both `R(W_0, W_1)` and `R(W_1, W_2)`),
     `sigma_rho = T_(2a) ∪ N_c(Tg)`, their inverses, and singletons `kappa_(rho, rho')`.
   - **Pointer translations.** These are distinct across types, since the `4R` shifts are distinct.
   - **Value differences.** `±c_rho` are distinct since `n > 2R`, and `kappa` differences avoid them since
     `n - (R^2 - 1) > R`.
   - **Same difference.** Within one difference, `tau` and `sigma` separate by first coordinate (`Sg` versus
     `Tg`).
5. **Entropy (§5).**
   - `H(psi) = t + 1`, since `j` is uniform and the XOR bit is fresh.
   - **Masks.** For each gadget, `y_F` is in bijection with `(J, masks, x(o)[j_rho])`. The three outputs are
     `(j, alpha + gamma)`, `(j, x(o)[j] + alpha + beta)` and `(j, beta + gamma)`, with independent uniform
     masks.
   - **Residual.** `H(x(o) | y_F) = k(1 - 1/k)^R <= 1/k`.
6. **Non-realizability (§6).** This is a remark, not needed for the claim.
   - The word `(tau sigma)^m sigma` fixes `s_1` and translates every pointer by `-(3m + 2)a`, so (H) fails.
   - In a group, `g = W_1^-1 W_0` satisfies `g^L = g^(3m+2) = 1`.

**Checks** (`verify_rotation_gadget.json`):
- **Literal brute-force (Q)** on a small instance: 65826 instances, 0 violations. The one-shift negative
  control has 4836 violations.
- **Class check of (Q)** at `k = 4, 8`.
- **(H) failure:** all pointers are moved.
- **Monte Carlo decoding:** 0 errors, and the mean unrevealed count matches `k(1 - 1/k)^R`.
