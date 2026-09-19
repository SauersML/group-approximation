---
rg: 2
id: fixed-commuting-lamps-have-robust-fourier-atoms
kind: claim
title: A fixed commuting involution packet has explicit robust Fourier cylinder atoms
distinct_from:
  native-hecke-edge-rank-integrality-is-bounded: that applies the exact atom formula to one clique and extracts only bounded rank pressure; this records the full trace and covariance estimates needed for a nonlinear decoder.
  arithmetic-global-pvm-does-not-bypass-coset-action-gate: that starts after a global spectral PVM has already been rounded; this gives the finite packet formula and its dimension-independent perturbation bound.
---

Let `u_1,...,u_k` be commuting self-adjoint involutions in a finite tracial
algebra.  For `epsilon in {+1,-1}^k`, put

```text
E_epsilon=2^(-k) product_(i=1)^k (1+epsilon_i u_i).     (FCA1)
```

Then the `E_epsilon` are pairwise orthogonal projections and

```text
sum_epsilon E_epsilon=1.                               (FCA2)
```

Their traces are given by the finite Fourier transform

```text
tau(E_epsilon)
 =2^(-k) sum_(S subseteq [k])
       (product_(i in S) epsilon_i) tau(product_(i in S)u_i).  (FCA3)
```

In particular, if every nonempty lamp moment vanishes, all `2^k` atoms have
trace `2^(-k)`.  More generally,

```text
|tau(E_epsilon)-2^(-k)|
 <=2^(-k) sum_(emptyset != S subseteq [k])
                 |tau(product_(i in S)u_i)|.            (FCA4)
```

This construction has a dimension-independent covariance modulus.  Suppose
`u'_1,...,u'_k` is another commuting involution packet, `v` is unitary, and
`sigma` is a permutation of the coordinates.  If `epsilon'_(sigma(i)) =
epsilon_i`, then telescoping the ordered product of contractions gives

```text
||v E_epsilon v* - E'_(epsilon')||_2
 <=(1/2) sum_i ||v u_i v* - u'_(sigma(i))||_2,          (FCA5)
```

and hence

```text
||v E_epsilon v* - E'_(epsilon')||_2^2
 <=(k/4) sum_i ||v u_i v* - u'_(sigma(i))||_2^2.        (FCA6)
```

For fixed `k=42`, these are fixed polynomial/Lipschitz constants, independent
of matrix dimension.  Thus a genuinely commuting raw 42-lamp packet with
controlled joint moments and denominator covariance would provide exactly
the proposed cylinder PVM.  The arithmetic obstruction is not analytic
loss in `(FCA1)--(FCA6)`: `native-forty-two-shell-has-a-noncommuting-pair`
shows that the native packet does not satisfy the required all-pairs
commutation even at zero defining-relator defect.
