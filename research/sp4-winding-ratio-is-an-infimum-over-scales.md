---
rg: 2
id: sp4-winding-ratio-is-an-infimum-over-scales
kind: claim
title: Tensor products make the Sp4(Z) winding budget superadditive, so the winding-to-defect ratio is a true limit equal to its infimum over all scales
distinct_from:
  sp4-winding-ratio-sharp-constant-is-gromov-dual: that computes the ceiling N_W/(2 pi) and the all-MF value of the limsup Theta(W); this proves that the limsup is a limit and equals the infimum of S_W(eps)/eps over every scale up to 1/(6g-1), which turns the deficit criterion into a single-scale inequality.
  sp4-quasirep-windings-budget-and-saturation: that bounds S_W(eps) linearly from above and gives saturation along a sequence; this proves S_W is superadditive in the defect and upgrades saturation along a sequence to a lower bound at every scale.
  sp4-quasirep-winding-ratio-has-a-deficit: that is the open inequality on the limsup; this is the unconditional structure theorem that makes it a one-scale statement.
---

**ESTABLISHED** (route `sp4-winding-ratio-is-an-infimum-over-scales-proof`).

**Setting.** Notation as in `sp4-quasirep-windings-budget-and-saturation` and
`sp4-winding-ratio-sharp-constant-is-gromov-dual`: `Gamma = Sp_4(Z)`, a relator `r = prod_{i<=g} [a_i,b_i]` with
lifted value `zeta^k`, `k != 0`, window `W_r`, winding `kappa_r`, and for a finite `W` containing `W_r`

```text
S_W(eps) = sup { |kappa_r(pi)|/d : pi : Gamma -> U(d) unital, defect <= eps on W }.
```

Put `a_g = 1/(6g-1)`, and `tau_W = |k|/(2 pi beta*_W)` (the all-MF threshold of item 5 of the sharp-constant node).

**Theorem.**
1. **Superadditivity.** `S_W` is nondecreasing on `(0, a_g]`, and for `eps_1, eps_2 > 0` with `eps_1 + eps_2 <= a_g`,

   ```text
   S_W(eps_1 + eps_2)  >=  S_W(eps_1) + S_W(eps_2).
   ```

   The witness is the tensor product: `kappa_r(pi (x) sigma)/(d_pi d_sigma) = kappa_r(pi)/d_pi + kappa_r(sigma)/d_sigma`
   whenever both defects are at most `a_g`, after conjugating so that both windings are nonnegative.
2. **The ratio is a limit, equal to an infimum.** `lim_{eps->0+} S_W(eps)/eps` exists, and

   ```text
   Theta(W) = lim_{eps->0+} S_W(eps)/eps = inf_{0 < eps <= a_g} S_W(eps)/eps.
   ```

   Quantitatively, for `0 < x < y <= a_g`: `S_W(x)/x <= (S_W(y)/y) * y/(y - x)`.
3. **Also over windows.** `Theta_inf = lim_W Theta(W) = inf_W inf_{0<eps<=a_g} S_W(eps)/eps`.
4. **Single-scale deficit criterion.** The open claim `sp4-quasirep-winding-ratio-has-a-deficit` holds iff there are
   one finite `W` containing `W_r` and one scale `eps_1 in (0, a_g]` with

   ```text
   S_W(eps_1)  <  tau_W * eps_1.                                  (SSD)
   ```

   It also holds if some `(W, eps_1)` has `S_W(eps_1) < eps_1 nu/(2 pi)`. Likewise
   `sp4-quasirep-windings-are-sublinear` holds iff there is one `W` such that for every `c > 0` some single scale
   `eps` has `S_W(eps) < c eps`.
5. **The all-MF branch at every scale.** If `P_op = R/Z`, then for every finite `W` containing `W_r` and every
   `eps in (0, a_g]`,

   ```text
   S_W(eps)  >=  tau_W * eps  >=  (nu/(2 pi)) * eps.
   ```

   So on the all-MF branch, at the fixed scale `eps = a_g`, every window carries quasi-representations whose
   normalized winding is arbitrarily close to at least `nu a_g/(2 pi)`, in some finite dimension.
6. **Direction of amplification (obstruction).** A single `eps_1`-quasi-representation with winding ratio `rho`
   yields, by tensor powers, ratio `rho` at the scales `n eps_1` only. Amplification by tensor powers, direct sums
   and conjugation never moves a winding lower bound to a smaller scale. So no refutation of the deficit (and no
   proof of saturation) can come from finitely many scales; a proof of the deficit needs only one.
7. **The determinant relaxation is strictly above threshold at every scale.** With `R_W` as in item 8 of the
   sharp-constant node, `R_W(eps)/eps >= |k| a(eps)/(eps beta*_W) > tau_W` for every `eps in (0, a_g]`, since
   `a(eps) = (1/pi) arcsin(eps/2) > eps/(2 pi)`. So (SSD) at any one scale must again use the traceless part of the
   defects.

**What this changes.**
- The deficit hole was a `limsup` over `eps -> 0`. It is now one inequality at one chosen scale, which may be as
  large as `1/(6g-1)`. A fixed-defect statement is the natural target for rigidity or stability arguments that do
  not survive `eps -> 0` with uncontrolled constants.
- The flagship `deligne-triple-cover-exact-mf-radical` follows from (SSD) at one `(W, eps_1)` together with
  `deligne-finite-parameter-group-has-period-prime-to-three` (route `deligne-triple-cover-via-winding-deficit`).
- The all-MF branch must produce large windings at every scale uniformly, which is strictly more than the
  sequence statement of the saturation items.
