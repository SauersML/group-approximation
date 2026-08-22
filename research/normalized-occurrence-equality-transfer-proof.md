---
rg: 2
id: normalized-occurrence-equality-transfer-proof
kind: route
title: Combine normalized face domination with operator-valued cloud Poincare
target: normalized-occurrence-equality-transfer-preserves-face-gap
requires:
  - averaged-pinching-channels-are-row-square-lipschitz
  - repeated-ldpc-adjoint-face-hamiltonian-gap
  - expander-cloud-reduction-preserves-pauli-dimension-gap
  - balanced-overlay-common-reducing-outlier-cut
---

Put

```text
 P_(c,i)=(I-Ad(Q_(c,i)))/2,
 Pbar_loc=sum_(c,i)w_(c,i)P_(c,i)=I-A_loc.
```

Inside one exact face the adjoint coordinate involutions commute.  Therefore
their `P_(c,i)` are commuting orthogonal projections and

```text
 I-Phi_c
 =I-product_(i in c)(I-P_(c,i))
 <=sum_(i in c)P_(c,i).                                 (NOET8)
```

Multiply by `mu_c` and sum.  Since
`mu_c P_(c,i)=|c|w_(c,i)P_(c,i)<=q_0w_(c,i)P_(c,i)`,

```text
 H_F<=q_0 Pbar_loc.                                     (NOET9)
```

Together with `(NOET2)`, this gives
`Pbar_loc>=delta_0(I-E_K)`.  The local channel is a positive selfadjoint
contraction fixing `K`, so `(NOET4)` follows.

Next fix one equality cloud and one vector `xi`.  Apply the ordinary
Hilbert-valued Poincare inequality to the map
`v |-> Q_(i,v)xi`.  With the convention that its Dirichlet form is the edge
expectation in `(NOET6)`,

```text
 sum_v lambda_(i,v)||(Q_(i,v)-S_i)xi||^2
 <=lambda_eq^(-1) E_((u,v) edge i)
       ||(Q_(i,u)-Q_(i,v))xi||^2.                       (NOET10)
```

Because `(NOET10)` holds for every `xi`, it is the Loewner inequality

```text
 sum_v lambda_(i,v)(Q_(i,v)-S_i)^2
 <=lambda_eq^(-1)E_((u,v) edge i)
       (Q_(i,u)-Q_(i,v))^2.                             (NOET11)
```

Average with `nu_i`.  The displacement square function between the repeated
shared channel and the local occurrence channel is therefore at most
`lambda_eq^(-1)B_eq`, and has operator norm at most `b/lambda_eq`.
`averaged-pinching-channels-are-row-square-lipschitz` now gives

```text
 ||A_sh^k-A_loc^k||_(2->2)<=k sqrt(b/lambda_eq).         (NOET12)
```

Compress `(NOET12)` by `I-E_K` and use `(NOET4)` to obtain `(NOET7)`.

Finally, in the balanced presentation the normalized equality edge squares
are a fixed-density positive summand of the raw residual square function.
On a block reducing the corrected occurrence reflections, compression
preserves the Loewner order, so the common outlier bound gives
`B_eq<=C_bal beta I`.  This is exactly why the result survives sparse
high-operator-norm discrepancies: they are removed once in the common cut,
whereas the retained channel sees only the normalized positive row square.
