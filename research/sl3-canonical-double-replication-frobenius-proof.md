---
rg: 2
id: sl3-canonical-double-replication-frobenius-proof
kind: route
title: Replicate blocks and use exact folding to guarantee a positive relator defect
target: sl3-canonical-double-replication-escapes-every-frobenius-basin
requires:
  - sl3-arithmetic-double-finite-representations-fold
---

For every matrix word `W`, block evaluation commutes with replication:

```text
W(sigma^(rep)) = W(sigma) direct_sum ... direct_sum W(sigma).      (RFP1)
```

Writing `tr_d`, `||.||_(2,d)` and `||.||_F` for normalized trace,
normalized HS norm and unnormalized Frobenius norm, respectively, `(RFP1)`
gives exactly

```text
tr_(md)(W^(rep))=tr_d(W),
||W^(rep)-I||_(2,md)=||W-I||_(2,d),
||W^(rep)-I||_F=sqrt(m)||W-I||_F.                              (RFP2)
```

It remains only to know that the maximum defining-relator defect is
positive.  Let `w=i_0(h)i_1(h)^(-1)` be the fold-kernel word.  Canonical
character gives `tr(sigma_n(w))->0`.  If `sigma_n` satisfied every defining
relator exactly, it would be a genuine finite-dimensional representation of
`D`; `sl3-arithmetic-double-finite-representations-fold` would then give
`sigma_n(w)=I`, whose trace is one.  Hence for all sufficiently large `n`
the maximum relator defect `f_n` is positive.

Choose

```text
m_n >= (L_n/f_n)^2,
```

where `f_n` is measured in unnormalized Frobenius norm.  The last identity
of `(RFP2)` makes the replicated maximum at least `L_n`, while the first two
identities preserve the entire canonical-character normalized-HS problem.
