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

There is a completely explicit Fourier specialization over
`K=Q(zeta_p)`.  Present

```text
H_p=<u,t | u^p=1, t^(p-1)=1, tut^(-1)=u^g>,           (AFP2)
```

where `g` is primitive modulo `p`, and put

```text
e_r=(1/p)sum_(j=0)^(p-1) zeta_p^(-rj)u^j.             (AFP3)
```

The `e_r` are orthogonal self-adjoint projections summing to one,
`e_0=e_N`, and `q_p=sum_(r!=0)e_r`.  Given any labelling

```text
ell:F_p -> {+1,-1}^U                                  (AFP4)
```

whose nonzero labels are allowed context assignments, define

```text
P_a=sum_(ell(r)=a)e_r,
A_x=sum_a a_x P_a.                                    (AFP5)
```

Then `(P_a)` is an exact context PVM in `K[H_p]`, every `A_x` is a
self-adjoint involution, and the predicate mask `q_p` kills every forbidden
atom.  If `ell(0)` is forbidden, the full forbidden projection is exactly
`e_N`; otherwise it is zero.  Thus the predicate-mask deficit is exactly
`1/p`, with no asymptotic or functional-calculus step.

Every coefficient is explicit:

```text
P_a=(1/p)sum_j (sum_(ell(r)=a)zeta_p^(-rj))u^j,
A_x=(1/p)sum_j (sum_r ell(r)_x zeta_p^(-rj))u^j.       (AFP6)
```

This diagonal specialization is enough for the proposed Hecke--CRT
certificate.  Its rigidity under free placement is recorded in
`rowwise-shared-involution-forces-pairwise-marginal-closeness`.

Nor may the context packets simply remain independent.  By
`rowwise-shared-involution-forces-pairwise-marginal-closeness`, two occurrences
which agree with one `B_x` on large masks must already have small canonical
`L2` distance.  Independent free-factor placement has a fixed distance floor
(equal to `1/2` in squared half-distance for unbiased marginals), regardless
of how large `p` is.
