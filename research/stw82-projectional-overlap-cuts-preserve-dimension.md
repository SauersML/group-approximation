---
rg: 2
id: stw82-projectional-overlap-cuts-preserve-dimension
kind: claim
title: Projectional quasicentral cuts on the two-support overlap make multiplier adjunction dimension-neutral
distinct_from:
  stw82-quasicentral-support-thickening-preserves-dimension: that theorem requires projectional control on the whole one-sided support L=closure(ApA) and manufactures cuts for L+C p; the present theorem requires cuts only on the generally smaller overlap L intersect closure(A(1-p)A).
  stw82-overlap-is-a-full-linking-core: that theorem identifies the full linking core but stops at the residual-diagonal frame obstruction; the present theorem supplies a relative colour-coupling hypothesis which crosses that obstruction.
artifacts:
  - research/artifacts/stw82-projectional-overlap-cuts-audit-2026-08-30.md
---

Let `A` be separable, let `p in M(A)` be a projection, put `q=1-p`, and
define

```text
L=closure(ApA),       R=closure(AqA),       I=L intersect R,
K=A+C p.
```

Suppose `I` has an approximate unit of projections `(e_n)` such that

```text
norm([e_n,a])->0       for every a in A,
norm([e_n,p])->0.                                         (POC1)
```

Then

```text
dim_nuc(A+C p)=dim_nuc(A).                               (POC2)
```

This is an overlap-relative colour-reuse theorem.  No projectional
approximate unit is required for either larger support ideal `L` or `R`, and
neither support is assumed full or complemented.  If `p in A` or `q in A`,
the conclusion is respectively trivial or unitization invariance.  In the
remaining case, the cuts in `(POC1)` are already quasicentral for the
extension

```text
0 -> I -> K -> (A/L) direct_sum (A/R)~ -> 0,             (POC3)
```

so quasidiagonal-extension permanence reuses the same colours.  Both the
overlap and the explicitly split residual quotient have nuclear dimension
at most that of `A`.

The theorem isolates the next firewall sharply: a counterexample with two
proper overlapping supports cannot admit projectional quasicentral cuts on
the common linking core.  Positive finite-spectrum cuts without uniformly
repairable gaps remain insufficient, just as in the one-sided Toeplitz
no-go.

The hypothesis is genuinely weaker than projectional control of `L` or
`R`.  There is a dimension-one example with

```text
I=M_2(K),
L=[P K;K K],       R=[K K;K P],       A=[P K;K P],
```

where `P=K+rho(C_0((0,1]))` for a diagonal faithful essential
representation `rho`.  Standard diagonal finite-rank projections give the
cuts `(POC1)` on `I`, while both `L` and `R` have quotient `C_0((0,1])` and
therefore admit no approximate unit of projections at all.  Both support
ideals are proper essential and hence noncomplemented, both `p` and `q` are
nonfull, and

```text
dim_nuc(A)=dim_nuc(A+C p)=1.
```
