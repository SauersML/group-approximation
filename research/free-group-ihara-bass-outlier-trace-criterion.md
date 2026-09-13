---
rg: 2
id: free-group-ihara-bass-outlier-trace-criterion
kind: claim
title: A unitary representation of F_k has no outlier above 2 sqrt(2k-1) for the generator sum exactly when its cyclically reduced character sums grow at rate sqrt(2k-1)
---

ESTABLISHED (unreviewed; elementary).  Let `F_k` be free on `s_1, ..., s_k`,
`S = {s_i, s_i^-1}`, `q = 2k - 1`, and `CR_n` the set of cyclically reduced
words of length `n`.  Let `rho` be a unitary representation of `F_k` of
finite dimension `d`, put `Z = sum_(s in S) rho(s)`, and

```text
T_rho(n) = sum_(w in CR_n) chi_rho(w),        E_rho(n) = T_rho(n) - (k-1) d (1 + (-1)^n).
```

1. **Bass's identity for representations.**  The non-backtracking operator
   `B_rho` on `V (x) C^S`, `(B xi)_s = rho(s^-1) sum_(t != s^-1) xi_t`, satisfies
   `tr B_rho^n = T_rho(n)` and
   `det(I - u B_rho) = (1 - u^2)^((k-1) d) det((1 + q u^2) I - u Z)`.
2. **Spectral expansion.**  Let `lambda_1, ..., lambda_d` be the eigenvalues of `Z`
   and `mu_j^+, mu_j^-` the roots of `mu^2 - lambda_j mu + q = 0`.  Then
   `E_rho(n) = sum_j ((mu_j^+)^n + (mu_j^-)^n)`.  If `|lambda_j| <= 2 sqrt q`, both roots
   have modulus `sqrt q`.  Otherwise both are real, of the sign of `lambda_j`, and one of
   them has modulus `> sqrt q`.
3. **Exact criterion.**  Let `M_rho = max_(j, +-) |mu_j^(+-)|`, which is `>= sqrt q`.  Then
   `limsup_n |E_rho(n)|^(1/n) = M_rho`, and `||Z|| > 2 sqrt q` iff `M_rho > sqrt q`, in which case
   `||Z|| = M_rho + q / M_rho`.  So `rho(Z)` has no outlier above `2 sqrt q` iff the corrected
   character sums over cyclically reduced words grow at rate at most `sqrt q`.
4. **Uniform criterion along a sequence.**  Let `rho_i` have dimensions `d_i`.
   - (a) If `||Z_i|| <= 2 sqrt q + epsilon_i` with `epsilon_i -> 0`, then for every `delta > 0`,
     for all large `i` and every `n`, `|E_(rho_i)(n)| <= 2 d_i (sqrt q + delta)^n`.
   - (b) Conversely, suppose there are even lengths `n_i` with `n_i / log d_i -> infinity`, a constant
     `C` and `delta_i -> 0` such that `E_(rho_i)(n_i) <= d_i^C (sqrt q + delta_i)^(n_i)`.  Then
     `limsup ||Z_i|| <= 2 sqrt q`.  Only an upper bound on the even-length sums is needed,
     because outliers contribute positively at even lengths.

**Scope.**  The trivial bound `|E_rho(n)| <= d |CR_n| + 2(k-1)d` already gives the
bound in 4(b) for `n <= 2 (C - 1) log_q d` or so.  All the content sits at lengths
`n >> log d`, where cyclically reduced words of length `n` equidistribute in the
image group.  So the criterion is a reformulation, not a proof technique: it moves
the question into counting fixed points of long words.  For a permutation
representation minus the trivial one, `chi_rho(w) = #Fix(w) - 1`.

Specialisation to the congruence quotients of a cubic division lattice:
`cubic-division-ihara-traces-count-roots-mod-p`.

Proof: `free-group-ihara-bass-outlier-trace-criterion-proof`.
