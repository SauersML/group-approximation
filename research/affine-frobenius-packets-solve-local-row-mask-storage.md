---
rg: 2
id: affine-frobenius-packets-solve-local-row-mask-storage
kind: claim
title: Affine Frobenius packets solve arbitrary rational local row-mask storage at almost full canonical mass
distinct_from:
  affine-frobenius-group-has-almost-full-simple-block: that identifies the simple block and its mass; this places a prescribed context PVM and marginal involutions in it with exact rational ranks.
  rowwise-hecke-crt-certificate-for-nonce-bcs: that also needs one shared involution to interpolate several context marginals; this closes only the independent local storage and deficit ledger.
  tracial-bcs-has-rational-balanced-hyperoctahedral-atlas: that uses a common finite type and literal coordinate permutations to balance overlaps; this uses arbitrary matrices in an almost-full primitive block and supplies no overlap transport.
---

Fix finitely many rational context assignment distributions.  Let `D` clear
all their denominators and choose a prime `p=1 mod D`.  In the block
`q_p C[H_p]q_p=M_(p-1)(C)` from
`affine-frobenius-group-has-almost-full-simple-block`, each context
distribution `lambda_c` is realized by a PVM with

```text
rank(P_(c,a)q_p)=(p-1)lambda_c(a).                    (AFP1)
```

The context marginal involutions are the corresponding signed sums of these
projections.  On the complementary central projection `e_N`, assign all mass
to any allowed answer, producing a full context PVM in `C[H_p]` with no
predicate violation.  Alternatively retain `q_p` as a private predicate
mask; its canonical deficit is exactly `1/p`.

Taking `p` arbitrarily large makes every weighted local row-mask deficit
arbitrarily small while preserving exact finite support and arbitrary local
matrix data.  This solves the storage, rational-rank, and density halves of
the rowwise certificate.  It does not construct one `B_x` shared across
different context packets.

