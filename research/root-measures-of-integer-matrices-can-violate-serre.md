---
rg: 2
id: root-measures-of-integer-matrices-can-violate-serre
kind: claim
title: The spectral measure of an integer symmetric matrix at a single basis vector can violate the Serre inequality
distinct_from:
  integer-moment-measure-with-negative-log-determinant: that is an abstract measure with integer moments; this is a root measure, the spectral measure of an operator with integer coordinates in an orthonormal basis taken at one basis vector, and it still violates the inequality
  necklace-realizable-measures-can-violate-serre: that refutes moment-level positivity classes of trace measures by a dominated difference; this refutes integral realizability at finitely many roots and isolates averaging over an invariant set of roots as the missing input
  finite-spectrum-integral-elements-obey-determinant: that proves the Serre inequalities for trace measures of finite spectrum over every group; this shows the same inequalities fail for a single-root measure of finite spectrum, so the trace averaging is essential
---

**ESTABLISHED** by `root-measures-integer-matrices-serre-violation-proof`.

Let `B = [[0,1],[1,1]]`, `phi = (1+sqrt 5)/2` and `psi = -1/phi`. Write
`rho_i = <E_B(.) e_i, e_i>` for the spectral measure of `B` at the basis
vector `e_i`.

1. **Integral data.** `B^k = [[F_(k-1), F_k],[F_k, F_(k+1)]]`, so
   `rho_1` has the integer moments `F_(k-1)`. It is realized by an operator
   with integer coordinates in an orthonormal basis, at one basis vector.
2. **Violation.** `rho_1 = w delta_phi + (1-w) delta_psi` with
   `w = 1/(1+phi^2)`, and

   ```text
   integral log|x| d rho_1 = log(phi) (1 - phi^2)/(1 + phi^2) ~ -0.2152 < 0.
   ```

3. **Atomless version.** Let `alpha` be the arcsine law on `[-2,2]`, the
   root measure of `g + g^-1` on `l^2(Z)`. Then `rho = rho_1 boxtimes alpha`
   is the root measure of `B (x) (g+g^-1)` at `e_1 (x) delta_0`. It has
   integer moments and no atoms, and
   `integral log|x| d rho = integral log|x| d rho_1 + m(x^2+1) < 0`.
4. **The trace average repairs it.** `integral log|x| d rho_2 ~ +0.2152`, and
   `rho_1 + rho_2` is the trace measure of `B`, with log integral
   `log|det B| = 0`.

**What separates root measures from trace measures.** Both root measures
above fail trace-level invariants that main proves for group rings:
- `rho_1` puts unequal mass on the Galois orbit `{phi, psi}`, while
  `finite-spectrum-integral-elements-obey-determinant` forces equal weights;
- for `Q = x`, `rho_1` has necklace number `p_2 = (N_2 - N_1)/2 = 1/2` and
  `rho` has `p_4 = (N_4 - N_2)/4 = 5/2`, so both fail the integrality of
  `torsion-free-integral-zeta-is-an-integer-euler-product`.

So those integrality invariants come from averaging over an invariant set of
roots, not from integer coordinates.

**Consequence.** Two ingredients are each insufficient on their own:
- integral realizability at finitely many roots admits Serre violators (this claim);
- measure-level invariants of trace measures admit the violator
  `mu = 23 nu - sigma` (`euler-integral-measure-violates-serre-inequality`,
  `necklace-realizable-measures-can-violate-serre`).

An approximation-free proof of the determinant conjecture has to couple
integral realizability with unimodular averaging. That is the open claim
`serre-class-from-unimodular-integral-realizability`.
