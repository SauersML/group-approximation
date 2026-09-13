---
rg: 2
id: free-group-ihara-bass-outlier-trace-criterion-proof
kind: route
title: Block-matrix proof of Bass's identity for representations of F_k, and the pole argument for the trace criterion
target: free-group-ihara-bass-outlier-trace-criterion
requires: []
---

Notation as in the target.  Write `V^S = V (x) C^S`, with elements `xi = (xi_s)_(s in S)`.

**Operators.**  Let `D = diag(rho(s^-1))_s`.  Let `Q` swap the coordinates `s` and `s^-1`.
Let `T : V -> V^S`, `Tv = (v)_s`, so that `T* xi = sum_s xi_s` and `T T*` is the all-ones block
matrix.  Then `B = D (T T* - Q)`: indeed `(B xi)_s = rho(s^-1)(sum_t xi_t - xi_(s^-1))`.

**Trace.**  Iterating, `(B^n)_(s_0, s_n)` is the sum of `rho(s_0^-1 s_1^-1 ... s_(n-1)^-1)` over
`s_1, ..., s_(n-1)` with `s_(i+1) != s_i^-1`, and with `s_n != s_(n-1)^-1`.  Setting `s_n = s_0`
and summing over `s_0`, `tr B^n` is the sum of `chi_rho(s_0^-1 ... s_(n-1)^-1)` over cyclic
sequences with `s_(i+1) != s_i^-1` for all `i` mod `n`.  The map `(s_i) -> (s_i^-1)` is a
bijection from these sequences onto `CR_n`, so `tr B^n = T_rho(n)`.

**Determinant.**  Put `J = DQ`, so `(J xi)_s = rho(s^-1) xi_(s^-1)`.
- `J^2 = I`, because `rho(s^-1) rho(s) = I`.  `J` has zero diagonal blocks, so `tr J = 0`,
  and its eigenvalues `+1` and `-1` each have multiplicity `kd`.  Hence
  `det(I + uJ) = (1 - u^2)^(kd)` and `(I + uJ)^-1 = (I - uJ) / (1 - u^2)`.
- `I - uB = (I + uJ) - u D T T*`.  By Sylvester's identity `det(I - XY) = det(I - YX)`,
  `det(I - uB) = (1 - u^2)^(kd) det(I_V - u T* (I + uJ)^-1 D T)`.
- `(J D T v)_s = rho(s^-1) rho(s) v = v`, so `J D T = T`.  Also `T* D T = sum_s rho(s^-1) = Z`
  (`S` is symmetric) and `T* T = 2k I`.  Therefore
  `T* (I + uJ)^-1 D T = (T* D T - u T* T) / (1 - u^2) = (Z - 2k u) / (1 - u^2)`.
- Hence `det(I - uB) = (1 - u^2)^(kd - d) det((1 - u^2) I - uZ + 2k u^2 I)
  = (1 - u^2)^((k-1) d) det((1 + q u^2) I - u Z)`.

**Spectrum and part 2.**  The right side factors as
`(1 - u)^((k-1)d) (1 + u)^((k-1)d) prod_j (1 - mu_j^+ u)(1 - mu_j^- u)`, since
`mu^+ + mu^- = lambda_j` and `mu^+ mu^- = q`.  The degree is `2kd = dim V^S`, so the spectrum of
`B` is `+1` and `-1` with multiplicity `(k-1)d` each, together with all the `mu_j^(+-)`.  So
`tr B^n = (k-1) d (1 + (-1)^n) + sum_j ((mu_j^+)^n + (mu_j^-)^n)`.  The roots are
`(lambda +- sqrt(lambda^2 - 4q)) / 2`.  If `lambda^2 <= 4q` they are complex conjugate with product
`q`, so both have modulus `sqrt q`.  If `lambda^2 > 4q` they are real, of the sign of `lambda`,
with product `q`, so one has modulus `> sqrt q`.

**Part 3.**  Let `nu` run over the distinct values among the `mu_j^(+-)`, with multiplicities
`m_nu >= 1`; all `nu != 0`.  Then
`sum_(n >= 1) E_rho(n) u^n = sum_nu m_nu nu u / (1 - nu u)`.  Distinct `nu` give distinct simple
poles `u = 1/nu` with nonzero coefficients, so nothing cancels.  The radius of convergence is
`1 / M_rho`, and Cauchy--Hadamard gives `limsup |E_rho(n)|^(1/n) = M_rho`.  Since the product of
each pair of roots is `q`, `M_rho >= sqrt q`.  For `x >= sqrt q` the function `x + q/x` is
increasing, `||Z|| = max_j |lambda_j|` (`Z` is self-adjoint), and `|lambda| = |mu| + q/|mu|`
for the larger root.  So `||Z|| > 2 sqrt q` iff `M_rho > sqrt q`, and then
`||Z|| = M_rho + q / M_rho`.

**Part 4(a).**  If `|lambda| <= 2 sqrt q + epsilon` and `lambda^2 > 4q`, the larger root satisfies
`|mu| <= sqrt q + epsilon / 2 + sqrt(4 sqrt q epsilon + epsilon^2) / 2`.  The smaller root has
modulus `q / |mu| <= sqrt q`.  So every root has modulus `<= sqrt q + delta` once `epsilon_i` is
small, and `|E(n)| <= 2 d_i (sqrt q + delta)^n`.

**Part 4(b).**  Take `n = n_i` even.  Each outlier root `nu` is real with `|nu| > sqrt q`, so it
contributes `nu^n > 0`.  All other roots have modulus `sqrt q` and contribute at most
`2 d_i q^(n/2)` in absolute value.  Hence
`M_i^n <= E(n) + 2 d_i q^(n/2) <= (d_i^C + 2 d_i)(sqrt q + delta_i)^n`, and
`M_i <= (sqrt q + delta_i) (3 d_i^(max(C,1)))^(1/n_i)`.  As `log d_i / n_i -> 0` and
`delta_i -> 0`, `limsup M_i <= sqrt q`.  By part 3,
`||Z_i|| <= max(2 sqrt q, M_i + q / M_i)`, which tends to `2 sqrt q`.

**Trivial range.**  `|CR_n| = q^n + 1 + (k-1)(1 + (-1)^n)` and `|chi_rho| <= d`, so
`|E_rho(n)| <= d q^n + O(d)`.  This is `<= d^C q^(n/2)` as long as `q^(n/2) <= d^(C-1)`.
