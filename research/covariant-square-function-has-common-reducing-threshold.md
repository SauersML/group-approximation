---
rg: 2
id: covariant-square-function-has-common-reducing-threshold
kind: claim
title: A covariant defect square function has one small common almost-reducing threshold
distinct_from:
  hs-defect-operator-norm-quarantine: that thresholds a joint defect operator but obtains no invariance; this quantifies the additional covariance input which makes the threshold almost reducing for all model unitaries on average
  complete-pair-overlay-uniform-hs-basin-capture: that must construct the covariant square function and finish diffuse correction; this proves the spectral coarea and block-diagonalization step once such a function is available
---

Let `0<=H<=C I` in a finite tracial matrix algebra, let `(U_s)_(s in S)` be
unitaries, and suppose

```text
  tau(H)<=E,
  (1/|S|) sum_s ||[H,U_s]||_2 <= K.                      (CSF1)
```

For every `0<a<b<C` there is `t in [a,b]` such that, for
`p=1_[t,infinity)(H)`,

```text
  tau(p)<=E/a,
  (1/|S|) sum_s ||[p,U_s]||_2^2 <= K/(b-a).              (CSF2)
```

Moreover each `U_s` can be changed to a unitary `V_s` commuting with this
same `p`, with

```text
  (1/|S|) sum_s ||U_s-V_s||_2^2
    <= C_0 K/(b-a)                                       (CSF3)
```

for a numerical constant `C_0`.  Thus if `E,K->0` and `a,b` are fixed, the
high-energy sector has vanishing trace and is a common approximately
reducing sector at vanishing average normalized-HS cost.

For the coarea calculation, diagonalize `H` with eigenvalues `lambda_i`.
Writing `u_ij` for the matrix entries of one `U`, direct integration gives

```text
 int_0^C ||[1_[t,infinity)(H),U]||_2^2 dt
   = (1/d) sum_(i,j) |lambda_i-lambda_j| |u_ij|^2
   <= ||[H,U]||_2.                                       (CSF4)
```

The inequality is Cauchy--Schwarz and
`d^(-1) sum_(i,j)|u_ij|^2=1`.  Average `(CSF4)` over `s` and then over
`t in [a,b]`; one threshold satisfies the second part of `(CSF2)`, while
Markov's inequality gives its first part for every `t>=a`.

Finally use the cosine--sine decomposition of `U_s` relative to
`pH direct-sum (1-p)H`.  Replacing each two-dimensional rotation block by
its diagonal polar blocks produces a unitary commuting with `p`; its squared
Hilbert--Schmidt displacement is bounded by a numerical multiple of the
squared off-diagonal mass, which is `||[p,U_s]||_2^2/2`.  This proves
`(CSF3)`.

The theorem explains exactly what plain defect quarantine lacks.  It is not
enough that `tau(H)` is small: one must also build `H` so its average
commutator with the occurrence reflections is small.  Establishing that
covariance for a balanced parity/complete-pair defect square function is the
remaining nonlinear algebraic step in the basin route.
