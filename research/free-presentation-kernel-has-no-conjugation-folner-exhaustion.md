---
rg: 2
id: free-presentation-kernel-has-no-conjugation-folner-exhaustion
kind: claim
title: A nontrivial normal kernel in a free presentation has no conjugation-Folner probability exhaustion
distinct_from:
  leavitt-positive-rank-intertwiner-retention: that asks for representation-specific low-energy spectral sectors; this rules out obtaining their equivariance merely by making the kernel-word coefficient weights conjugation invariant.
  unnamed-fixed-space-promotion-is-goal-equivalent: that concerns promotion of an almost-fixed vector to trace-visible rank; this is a coefficient-space obstruction before any rank promotion.
  three-reynolds-plus-kernel-energy-has-vanishing-gap: that gives a finite Pauli rotation with collapsing operator gap; this proves a general nonamenability obstruction for weighted exhaustions of an infinite presentation kernel.
---

**ESTABLISHED.** Let `F` be a nonabelian finitely generated free group and
let `1!=K normal F`. There are a finite set `S<=F` and `eta>0` such that every
finitely supported probability measure `mu` on `K\{1}` satisfies

```text
max_(s in S) ||s_*mu-mu||_1 >= eta,                    (CKE1)
```

where `(s_*mu)(k)=mu(s^(-1)ks)`. Thus no exhaustion of the nonidentity kernel
words can be made asymptotically conjugation invariant in coefficient
`ell^1`.

For an exact unitary representation `Pi:F->U(H)`, put

```text
D_k=(Pi(k)-1)^*(Pi(k)-1),
A_mu=sum_(k in K\{1}) mu(k)D_k.                        (CKE2)
```

Then normality gives the exact covariance formula

```text
Pi(s) A_mu Pi(s)^*=A_(s_*mu),                          (CKE3)
```

and hence the representation-independent estimate

```text
||Pi(s)A_mu Pi(s)^*-A_mu||_op
   <=4||s_*mu-mu||_1.                                  (CKE4)
```

If `P=1_[0,a](A_mu)` and the rest of the spectrum is contained in `[b,4]`
with `b>a`, the standard off-diagonal spectral estimate gives

```text
||(1-P)Pi(s)P||_op
 <=(b-a)^(-1)||Pi(s)A_mu Pi(s)^*-A_mu||_op.            (CKE5)
```

Consequently the proposed weighted-kernel-energy route to `(IR1)` cannot use
a Reiter/Folner choice of the word weights: `(CKE1)` says no such weights
exist. Any successful use of `(CKE2)` must instead prove
**representation-specific cancellation** in the map `mu |-> A_mu`, or find a
moving spectral band whose equivariance is not obtained from coefficient
`ell^1` invariance. Property `(T)` of `F/K` does not supply the missing
weights; it becomes applicable only after an almost quotient representation
has already been constructed.

This does not refute `leavitt-positive-rank-intertwiner-retention`. It removes
the most direct normality-only implementation suggested there and identifies
the extra datum a surviving spectral construction must use.

DERIVATION
free-kernel-conjugation-folner-obstruction-proof
