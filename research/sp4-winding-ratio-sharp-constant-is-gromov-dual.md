---
rg: 2
id: sp4-winding-ratio-sharp-constant-is-gromov-dual
kind: claim
title: The winding of an Sp4(Z) quasi-representation is the pairing of its determinant cocycle with the relator cycle, and the all-MF branch saturates the l1-dual constant exactly
distinct_from:
  sp4-quasirep-windings-budget-and-saturation: that gives the crude budget (6g-1)eps/4 and a saturation floor |k|/(2 pi max_W|b|) that depend on the chosen word and cocycle; this computes the winding exactly as a cocycle pairing, replaces both constants by the rephasing-invariant LP values N_W and |k|/beta*_W, and shows both converge to the same l1-dual constant nu/(2 pi), so the all-MF branch pins the winding ratio at its maximum.
  deligne-sector-determinants-see-only-dimension-mod-three: that shows determinant data of exact or near-exact Deligne sector models see only d mod 3 at the order-three mark; this is about the ratio of winding to defect for plain quasi-representations of Sp_4(Z) at the infinite-order mark, and shows the determinant relaxation of that ratio already reaches the all-MF value.
  sp4-quasirep-windings-are-sublinear: that asks for the ratio to tend to zero; this proves the exact unconditional ceiling of the ratio and the exact value forced by P_op = R/Z, which yields the strictly weaker sufficient condition sp4-quasirep-winding-ratio-has-a-deficit.
  deligne-sep8-first-order-tensor-threshold: that is the o(|t|) criterion for the all-MF branch with a moving parameter; this reads that criterion off a single number attached to plain quasi-representations of Sp_4(Z).
---

**ESTABLISHED** (route `sp4-winding-ratio-sharp-constant-is-gromov-dual-proof`).

**Setting.** Notation as in `sp4-quasirep-windings-budget-and-saturation`: `Gamma = Sp_4(Z)`, `b` the normalized
integral covering cocycle, `E_infinity = Gamma x_b Z`, `zeta = (e,1)`, `P_op` the parameter group, a relator
`r = prod_{i<=g} [a_i,b_i]` with lifted value `zeta^k`, `k != 0`, its window `W_r`, the winding `kappa_r`, and
`S_W(eps)` for finite `W` containing `W_r`. Chains are normalized bar chains over `R` (`[g|h] = 0` if `g = e` or
`h = e`), with `d[g|h] = [g] + [h] - [gh]`. Cochains are normalized, with `(delta psi)(g,h) = psi(g) + psi(h) - psi(gh)`.

**Objects.**
- *Relator cycle.* Write the word as letters `y_1, ..., y_(4g)` (`a_1, b_1, a_1^-1, b_1^-1, ...`) with partial
  products `p_j`. Put
  `c_r = sum_{j<4g} [p_j | y_(j+1)] - sum_i ([a_i | a_i^-1] + [b_i | b_i^-1])`.
  Then `c_r` is a cycle supported on `W_r`, and `<b, c_r> = k`.
- *Determinant cocycle.* For unital `pi : Gamma -> U(d)`, put `D(g,h) = pi(g) pi(h) pi(gh)^*` and
  `beta_pi(g,h) = (1/(2 pi i d)) Tr log D(g,h)` (principal branch). Put `a(eps) = (1/pi) arcsin(eps/2)`.
- *Local cocycles.* `T(W)` is the set of triples `(g,h,l)` whose nondegenerate faces `(h,l), (gh,l), (g,hl), (g,h)`
  all lie in `W`. A local cocycle on `W` is a normalized `beta : W -> R` with `delta beta = 0` on `T(W)`. Put
  `N_W = max { <beta, c_r> : beta a local cocycle on W, |beta| <= 1 }`.
- *Rephasing constant.* `beta*_W = min_psi max_W |b + delta psi|`, over normalized real `psi`.
- *l1 constant.* `nu = ||[r]||_1 = inf { ||z||_1 : z a real 2-cycle homologous to c_r }`, the l1 seminorm of the
  class of `r` in the normalized bar complex.
- *Ratio.* `Theta(W) = limsup_{eps -> 0+} S_W(eps)/eps`. It is nonincreasing in `W`; put
  `Theta_inf = lim_W Theta(W)`.

**Theorem.**
1. **Exact winding formula.** If `pi` is unital with defect at most `eps` on `W_r` and `(6g-1) eps < 2`, then
   `kappa_r(pi)/d = <beta_pi, c_r>`.
2. **Determinant cocycle.** If `pi` has defect at most `eps < 1` on `W`, then `beta_pi` is a local cocycle on `W` with
   `|beta_pi| <= a(eps)`. Moreover `d beta_pi = delta theta + n` on `W`, where `theta(g)` is a real logarithm of
   `det pi(g)` divided by `2 pi i` (with `theta(e) = 0`) and `n` is integer valued.
3. **Sharp budget.** For `eps < min(1, 2/(6g-1))`, `S_W(eps) <= a(eps) N_W`. Hence `Theta(W) <= N_W/(2 pi)`.
   Since `N_W <= ||c_r||_1 <= 6g-1` and `a(eps) <= eps/4`, this contains item 1 of the budget node.
4. **Duality.** `beta*_W = max { <b, z> : z a real 2-cycle supported on W, ||z||_1 <= 1 }`. Also:
   - `0 < nu < infinity`;
   - `beta*_W` increases to `|k|/nu`;
   - `N_W >= |k|/beta*_W >= nu` for every `W`, and `N_W` decreases to `nu`.
   The ratio `nu/|k|` does not depend on the relator.
5. **Sharp saturation.** If `P_op = R/Z`, then `Theta(W) >= |k|/(2 pi beta*_W)` for every finite `W` containing
   `W_r`.
6. **The all-MF branch pins the ratio.** Unconditionally, `Theta_inf <= nu/(2 pi)`. If `P_op = R/Z`, then
   `nu/(2 pi) <= |k|/(2 pi beta*_W) <= Theta(W) <= N_W/(2 pi)` for every `W`, so `Theta_inf = nu/(2 pi)`.
7. **Deficit criterion.** If some finite `W` containing `W_r` has `Theta(W) < |k|/(2 pi beta*_W)`, then `P_op` is
   finite, `P_op = (1/m)Z/Z` with `m` even. This holds in particular if `Theta_inf < nu/(2 pi)`.
8. **The determinant relaxation cannot see the deficit.** Let `R_W(eps)` be the supremum of `|<beta, c_r>|` over
   all `d >= 1` and data `(beta, theta, n)` on `W` satisfying the conclusions of item 2 at defect `eps`:
   - `beta` is a local cocycle;
   - `|beta| <= a(eps)`;
   - `d beta = delta theta + n` with `n` integral.
   Then `S_W(eps) <= R_W(eps) <= a(eps) N_W`, and `R_W(eps) >= |k| a(eps)/beta*_W`. So
   `liminf R_W(eps)/eps >= |k|/(2 pi beta*_W)`, which is exactly the threshold of item 7. The bound is approached, as
   `d -> infinity`, by `beta = lambda (b + delta psi*)` with `d lambda` integral. When `P_op = R/Z`, the rephased `t`-models realize
   these data to first order.

**What this changes.**
- The winding-to-defect ratio has a canonical ceiling `nu/(2 pi)`, where `nu` is the Gromov-type l1 norm of the
  relator class.
- The all-MF branch forces the ratio to sit exactly at that ceiling, and on every window at least at
  `|k|/(2 pi beta*_W)`.
- So `P_op` is finite as soon as quasi-representations fall short of the ceiling on one window. This is the OPEN
  claim `sp4-quasirep-winding-ratio-has-a-deficit`, strictly weaker than asking for ratio `o(1)`.
- Item 8 kills a class of approaches: every Tr-log, determinant, K_1 or winding-count argument that uses only the
  scalar data of the defects. Such arguments cannot prove the deficit, and a fortiori cannot prove sublinearity.
  - *The invariant.* The determinant cocycle `beta_pi`, whose relaxation reaches the all-MF value.
  - *Where they die.* At the bound on `<beta_pi, c_r>`.
  A proof of the deficit must use the traceless part of the defects `D(g,h)`.
