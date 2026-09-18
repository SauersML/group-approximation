---
rg: 2
id: deligne-monomial-parameter-group-is-governed-by-maslov-slope
kind: claim
title: Monomial Maslov parameters of Sp_4(Z) form a closed subgroup between the half parameter and P_op, and it is the whole circle iff the small-parameter Maslov slope vanishes
distinct_from:
  deligne-sep7-norm-parameter-closed-subgroup: that proves the closed-subgroup structure of the pointwise operator-norm parameter group P_op; this is the monomial (exact-permutation, diagonal-phase) parameter group P_mon, which sits inside P_op, and adds the slope law lim m(t)/t = sup m(t)/t that has no operator-norm counterpart proved.
  maslov-ce-parameter-set-is-a-closed-subgroup: that concerns canonical tracial microstates; this concerns uniform (sup over all cells) defects of monomial models over finite Gamma-sets.
  deligne-finite-parameter-group-has-period-prime-to-three: that asks 3 not dividing |P_op| on the finite branch; this proves the monomial floor at 1/3 is exactly the conjunction of a monomial finite-branch statement and a monomial period statement, each implied by the corresponding operator-norm prerequisite.
  deligne-class-finite-action-norms-vanish: that is the normalized Hamming norm of the mod-3 class, relevant to soficity; this is the uniform-in-cells norm of the real Maslov line relevant to MF, and the two are not comparable.
---

**ESTABLISHED** (`deligne-monomial-parameter-group-slope-proof`). Unreviewed.

**Setting.**
- `Gamma = Sp_4(Z)` with a fixed finite presentation `<S | R>`.
- Lifted relations `r~(S) = z^(k_r)` hold in the preimage `Gamma~` of `Gamma` in the universal cover of `Sp_4(R)`,
  with `z` the kernel generator.
- `kappa` is the integral cellular 2-cocycle `r -> k_r`, and `K = max_r |k_r|`.
- A **monomial model** over a finite `Gamma`-set `X` is a phase function `a : X x S -> R/Z`. Its operator is
  `rho(s) = D_s P_s`, where `P_s` is the exact permutation and `D_s` is diagonal with entries `e(a(x,s))`.
  `delta a (x,r)` is the holonomy of `a` around the 2-cell `(x,r)` of the Schreier 2-complex `Y_X`.
- `mu_theta(X) = min_a max_(x,r) dist(delta a (x,r) - theta k_r, Z)` is the uniform relator defect at parameter
  `theta`, and `m(theta) = inf_X mu_theta(X)`.
- `P_mon = { theta in R/Z : m(theta) = 0 }` is the **monomial parameter group**.
- `||.||_cell` is the quotient sup-norm on `H^2(Y_X; R) = C^2 / delta C^1`.
- `L_X` is the image of `H^2(Y_X; Z)` in `H^2(Y_X; R)`.
- `c_K = ||kappa_R||_cell` on the one-vertex presentation complex `P = Y_pt`.

**Theorem.**
1. **Diophantine form.** `mu_theta(X) = min_(u in H^2(Y_X;Z)) ||theta kappa_R + u_R||_cell = dist_cell(theta kappa_R, L_X)`.
   Moreover `||kappa_R||_cell = c_K` on every `Y_X`.
2. **Group law.** `m` is even, subadditive, `c_K`-Lipschitz and `1/2`-periodic on `R/Z`, and `m(theta) <= c_K |theta|`.
   So `P_mon` is a closed subgroup, and
   ```text
   (1/2)Z/Z  <=  P_mon  <=  P_op,                                        (MP1)
   ```
   hence `P_mon = R/Z` or `P_mon = (1/m)Z/Z` for one even `m`.
3. **Slope law.** The limit
   ```text
   s := lim_(t -> 0+) m(t)/t  exists and equals  sup_(t > 0) m(t)/t,  with 0 <= s <= c_K.   (MP2)
   ```
   So `m(t) <= s t` for all `t > 0`, and `m(t) = s t (1 + o(1))` as `t -> 0`. In particular
   ```text
   P_mon = R/Z   iff   s = 0   iff   m vanishes on some sequence t_n -> 0 faster than t_n.   (MP3)
   ```
4. **Transference to one third.** For every finite `X` and every `t in (0, 1/6]`,
   ```text
   m(1/3) = m(1/6) <= mu_t(X) / (6t) + c_K t.                                       (MP4)
   ```
   Monomial models at small parameters with defect `o(t)` therefore produce `1/3`-models of defect `-> 0`.
5. **Decomposition of the third floor.** The uniform third cellular floor `F: m(1/3) > 0` holds iff
   `1/6 notin P_mon`, iff both of the following hold:
   - (A) `s > 0`, i.e. `P_mon` is finite;
   - (B) if `P_mon = (1/m)Z/Z`, then `3` does not divide `m`.

   Each of (A) and (B) can fail on its own: `P_mon = R/Z` breaks (A), and `P_mon = (1/6)Z/Z` breaks only (B).
6. **Interlock with the operator-norm routes.** Since `P_mon <= P_op`:
   - "`P_op` finite" (the output of `sp4-quasirep-windings-are-sublinear`) implies (A);
   - that, together with `deligne-finite-parameter-group-has-period-prime-to-three`, implies (B);
   - the flagship `deligne-triple-cover-exact-mf-radical` implies `F`.

   Any refutation of (A) or (B) refutes the flagship.
7. **Sufficient condition for (A).** Suppose the lattices `L_X` have a uniform systole: some `sigma > 0` with
   `||u_R||_cell >= sigma` for every integral class `u` with `u_R != 0` on every `Y_X`. Then `mu_t(X) = c_K t` for
   `t < sigma / (2 c_K)`, so `s = c_K > 0`.

**What is not decided.** Neither (A) nor (B) is decided, and neither is the value of `s`. The theorem splits the
monomial gate of the flagship into a small-parameter part and an arithmetic part. It also turns any sublinear
small-parameter monomial family into a counterexample via (MP4).

## Attempts
