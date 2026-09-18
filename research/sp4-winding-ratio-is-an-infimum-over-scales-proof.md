---
rg: 2
id: sp4-winding-ratio-is-an-infimum-over-scales-proof
kind: route
title: Tensor two quasi-representations, add their eigenangles, and run Fekete's lemma at zero for a monotone superadditive budget
target: sp4-winding-ratio-is-an-infimum-over-scales
requires:
  - sp4-quasirep-windings-budget-and-saturation
  - sp4-winding-ratio-sharp-constant-is-gromov-dual
---

Notation as in the target. All maps are unital `pi : Gamma -> U(d)`, and "defect `<= eps` on `W`" means
`||pi(g)pi(h) - pi(gh)|| <= eps` for `(g,h) in W`.

**Step 0: the winding is defined and angles are small.** By Step 1 of `sp4-quasirep-windings-budget-and-saturation-proof`
(with `t = 0`), defect `<= eps` on `W_r` gives `||W_r(pi) - 1|| <= (6g-1) eps`. For `eps <= a_g = 1/(6g-1)` this is
`<= 1`, so every eigenvalue `exp(i phi_j)` of `W_r(pi)` (principal angle `phi_j in (-pi, pi]`) has
`2|sin(phi_j/2)| <= 1`, i.e. `|phi_j| <= pi/3`. Then `kappa_r(pi) = (1/2 pi) sum_j phi_j` is the principal-branch
`(1/2 pi i) Tr log W_r(pi)`, an integer (determinant `1`). In particular `S_W(eps)` is defined, with
`0 <= S_W(eps) <= (6g-1) eps/4 < infinity` (item 1 of the budget node); the trivial representation gives `0`.

**Step 1: monotonicity.** The set of admissible `pi` grows with `eps`, so `S_W` is nondecreasing.

**Step 2: conjugation flips the sign.** Let `pi-bar(g)` be the entrywise complex conjugate of `pi(g)`. It is unital,
unitary, and `||pi-bar(g)pi-bar(h) - pi-bar(gh)|| = ||pi(g)pi(h) - pi(gh)||`. Also `W_r(pi-bar)` is the conjugate of
`W_r(pi)`, whose eigenvalues are `exp(-i phi_j)`. So `kappa_r(pi-bar) = -kappa_r(pi)`, and in the supremum defining
`S_W` one may restrict to `kappa_r(pi) >= 0`.

**Step 3: the tensor product.** Let `pi` (dimension `d_1`) and `sigma` (dimension `d_2`) have defects `<= eps_1`,
`<= eps_2` on `W`, with `eps_1 + eps_2 <= a_g`. Put `rho = pi (x) sigma`, unital and unitary.
- *Defect.* For `(g,h) in W`, writing `A = pi(g)pi(h)`, `E = pi(gh)`, `C = sigma(g)sigma(h)`, `F = sigma(gh)`:
  `||A (x) C - E (x) F|| <= ||(A - E) (x) C|| + ||E (x) (C - F)|| = ||A - E|| + ||C - F|| <= eps_1 + eps_2`,
  since `||X (x) Y|| = ||X|| ||Y||` and `C`, `E` are unitary.
- *Relator word.* `(X (x) Y)(X' (x) Y') = XX' (x) YY'` and `(X (x) Y)^* = X^* (x) Y^*`, so every commutator and every
  product of commutators factors: `W_r(rho) = W_r(pi) (x) W_r(sigma)`.
- *Eigenangles add.* The eigenvalues of `W_r(pi) (x) W_r(sigma)` are `exp(i(phi_j + psi_l))`, over all pairs, where
  `phi_j, psi_l` are the principal angles of the two factors. By Step 0 (applied to `pi` at `eps_1 <= a_g` and to
  `sigma` at `eps_2 <= a_g`), `|phi_j|, |psi_l| <= pi/3`, so `phi_j + psi_l in [-2pi/3, 2pi/3]` is itself the
  principal angle. (Step 0 applied to `rho` at `eps_1 + eps_2 <= a_g` also shows `kappa_r(rho)` is defined.) Hence

  ```text
  kappa_r(rho) = (1/2 pi) sum_{j,l} (phi_j + psi_l) = d_2 kappa_r(pi) + d_1 kappa_r(sigma),
  kappa_r(rho)/(d_1 d_2) = kappa_r(pi)/d_1 + kappa_r(sigma)/d_2.
  ```

**Step 4: superadditivity (item 1).** Given `delta > 0`, choose by Step 2 admissible `pi`, `sigma` at `eps_1`, `eps_2`
with `kappa_r(pi)/d_1 >= S_W(eps_1) - delta` and `kappa_r(sigma)/d_2 >= S_W(eps_2) - delta`, both nonnegative. By
Step 3, `rho` is admissible at `eps_1 + eps_2` and `S_W(eps_1 + eps_2) >= kappa_r(rho)/(d_1 d_2) >= S_W(eps_1) +
S_W(eps_2) - 2 delta`. Let `delta -> 0`.

**Step 5: Fekete's lemma at zero (item 2).** Let `f : (0, a] -> [0, infinity)` be nondecreasing with
`f(x + y) >= f(x) + f(y)` whenever `x + y <= a`. Put `L = inf_{0 < x <= a} f(x)/x`, which is finite.
- *Iteration.* For `n >= 1` with `n x <= a`, induction gives `f(n x) >= n f(x)`, each step using
  `(m+1) x <= a`.
- *Comparison.* For `0 < x < y <= a`, let `n = floor(y/x) >= 1`. Then `n x <= y`, so by monotonicity
  `n f(x) <= f(n x) <= f(y)`. Since `n x > y - x`,

  ```text
  f(x)/x <= f(y)/(n x) = (f(y)/y) (y/(n x)) <= (f(y)/y) * y/(y - x).
  ```

- *Limit.* Clearly `liminf_{x->0} f(x)/x >= L`. Given `delta > 0`, pick `y` with `f(y)/y <= L + delta`; the
  comparison gives `limsup_{x->0} f(x)/x <= L + delta`. So `lim_{x->0} f(x)/x = L`.

Steps 1 and 4 show `f = S_W` satisfies the hypotheses on `(0, a_g]`, which proves item 2 and its quantitative form.

**Step 6: windows (item 3).** The *Ratio* definition in `sp4-winding-ratio-sharp-constant-is-gromov-dual` records that
`Theta(W)` is nonincreasing in `W` and defines `Theta_inf = lim_W Theta(W)` along the directed set of finite windows.
A nonincreasing net of reals converges to its infimum, so
`Theta_inf = inf_W Theta(W) = inf_W inf_eps S_W(eps)/eps` by item 2.

**Step 7: the single-scale criterion (item 4).** By item 2, `Theta(W) < tau_W` iff some `eps_1 in (0, a_g]` has
`S_W(eps_1)/eps_1 < tau_W`. The claim `sp4-quasirep-winding-ratio-has-a-deficit` is exactly "`Theta(W) < tau_W` for
some finite `W` containing `W_r`" (with its relator `r`), so it is equivalent to (SSD) at some `(W, eps_1)`. For the
second sufficient form: item 4 of the sharp-constant node gives `|k|/beta*_W >= nu`, so `tau_W >= nu/(2 pi)`, and
`S_W(eps_1) < eps_1 nu/(2 pi)` gives `Theta(W) <= S_W(eps_1)/eps_1 < tau_W`. For sublinearity: `S_W(eps) = o(eps)`
means `Theta(W) = 0`, which by item 2 means `inf_eps S_W(eps)/eps = 0`.

**Step 8: the all-MF branch (item 5).** If `P_op = R/Z`, item 5 of the sharp-constant node gives
`Theta(W) >= tau_W` for every finite `W` containing `W_r`. By item 2, `S_W(eps)/eps >= Theta(W) >= tau_W` for every
`eps in (0, a_g]`, and `tau_W >= nu/(2 pi)` as in Step 7. At `eps = a_g`, the definition of `S_W` as a supremum gives
quasi-representations with normalized winding arbitrarily close to `tau_W a_g >= nu a_g/(2 pi)`.

**Step 9: amplification (item 6).** Tensor powers: by Step 3, `pi^(x)n` has defect `<= n eps_1` and normalized winding
`n kappa_r(pi)/d`, the same ratio at scale `n eps_1` (while `n eps_1 <= a_g`). Direct sums take the maximum defect and a
convex combination of normalized windings; conjugation flips the sign. None of these produces a map of defect below
the smallest defect of its inputs. So from quasi-representations at finitely many scales, these operations give
lower bounds on `S_W` only at scales bounded below by a positive constant. Since `Theta(W)` depends only on
arbitrarily small scales in its limsup form, and equals the infimum over all scales in its limit form, a lower bound
`Theta(W) >= c` needs lower bounds at every scale, while an upper bound `Theta(W) < c` needs one scale.

**Step 10: the relaxation (item 7).** Item 8 of the sharp-constant node gives `R_W(eps) >= |k| a(eps)/beta*_W`
with `a(eps) = (1/pi) arcsin(eps/2)`. For `0 < u <= 1`, `arcsin u > u`, so `a(eps) > eps/(2 pi)` and
`R_W(eps)/eps > |k|/(2 pi beta*_W) = tau_W`. As `S_W <= R_W`, an argument that bounds `S_W(eps_1)` only through the
scalar data of item 2 of that node cannot reach (SSD) at any scale `eps_1`.
