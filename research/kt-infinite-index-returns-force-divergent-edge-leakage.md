---
rg: 2
id: kt-infinite-index-returns-force-divergent-edge-leakage
kind: claim
title: Infinite-index Kun--Thom returns force divergent aggregate edge leakage
distinct_from:
  kt-return-expectation-pays-one-full-edge-principal-angle: That uses one exterior return and forces one principal-angle unit of leakage; this uses the infinite compressor index to obtain arbitrarily many nearly orthogonal returns and forces the aggregate leakage to diverge.
  kt-intrinsic-subfactor-data-does-not-see-ambient-wall: That shows fixed intrinsic moment data of the subgroup-factor inclusion cannot detect the wall; this uses an unbounded family of exterior expectation tests and an unnormalized superoperator Hilbert--Schmidt sum, so it is deliberately not a fixed-moment continuous invariant.
  kt-nested-compressor-flat-tower-has-uniform-wall: That constructs a one-compressor HNN wall by increasing depth and leaves extension to the full actor open; this is a necessary one-step leakage law for any relative matrix model of the full vertex inclusion.
---

Fix the `q=2` Kun--Thom compressor `t`, put

```text
Lambda=t Gamma t^(-1)<Gamma,
```

and use the established fact

```text
[Gamma:Lambda]=infinity.                                 (KDL1)
```

Let `phi_n:G->U(d_n)` be normalized-Hilbert--Schmidt approximate
representations with canonical limiting character.  Put

```text
T_n=phi_n(t),
B_n=C*(phi_n(Gamma)),
P_n=E_(B_n),
L_n=||(1-P_n)Ad(T_n)P_n||_HS^2.                         (KDL2)
```

Assume the coordinates realize the canonical relative expectation on every
fixed exterior element:

```text
||E_(B_n)(phi_n(g))||_2->0        for every g outside Gamma.  (KDL3)
```

Then

```text
L_n->infinity.                                           (KDL4)
```

More quantitatively, choose any `N` distinct nontrivial left cosets
`gamma_i Lambda`, and put

```text
h_i=t^(-1)gamma_i t outside Gamma.                       (KDL5)
```

Let

```text
G_(ij,n)=<phi_n(gamma_i),phi_n(gamma_j)>,
q_(i,n)=||E_(B_n)(phi_n(h_i))||_2,
eta_(i,n)=||phi_n(h_i)-T_n^*phi_n(gamma_i)T_n||_2.       (KDL6)
```

For all sufficiently large `n`, `G_n` is invertible and

```text
L_n >= [sum_(i=1)^N (1-(q_(i,n)+eta_(i,n))^2)]
                    /lambda_max(G_n).                   (KDL7)
```

Canonical character convergence and multiplicativity give `G_n->I_N`,
while `(KDL3)` and the fixed-word defects give `q_(i,n),eta_(i,n)->0`.
Thus

```text
liminf_n L_n>=N.                                         (KDL8)
```

Since `N` is arbitrary, `(KDL4)` follows.

Combining this with the word-basis estimate `(KPA8)` gives a sharp necessary
growth law.  For any edge-algebra word basis with Gram least eigenvalue
`lambda_n` and forward covariance residuals `epsilon_(j,n)`, a positive
relative construction must satisfy

```text
lambda_n^(-1) sum_j epsilon_(j,n)^2 -> infinity.         (KDL9)
```

In particular, if the residual on a basis word of length `ell_(j,n)` is at
most `ell_(j,n) epsilon_n`, then

```text
lambda_n^(-1) epsilon_n^2 sum_j ell_(j,n)^2 -> infinity. (KDL10)
```

The surviving Certificate C architecture therefore needs an **unbounded**
moving-radius amplification of its vanishing actor defect, not merely the
single ill-conditioned direction allowed by `(KPA10)`.

DERIVATION
kt-infinite-return-principal-angle-sum-proof
