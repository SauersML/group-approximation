---
rg: 2
id: fourier-frobenius-common-carriers-classicalize-bcs
kind: claim
title: Common carriers in the Fourier Frobenius specialization classicalize the BCS
distinct_from:
  common-carrier-lives-in-packet-intersection: that only places a shared coefficient in the literal packet-subgroup intersection; this uses the prime cyclic Fourier support to turn all such intersections into a global classical assignment.
  affine-frobenius-common-negative-carrier: that permits arbitrary PVMs in the full Frobenius matrix block; this rules out its explicit diagonal Fourier specialization, not every nonabelian packet placement.
---

**ESTABLISHED.**  Let a finite BCS have context set `C`.  For one prime
`p`, embed for every context `c` a Frobenius packet

```text
H_c=C_p rtimes C_(p-1) <= Gamma
```

with prime normal subgroup `N_c=C_p`.  Use the explicit Fourier PVM

```text
P_(c,a)=sum_(ell_c(r)=a)e_(c,r),
q_c=sum_(r!=0)e_(c,r),                                  (FFC1)
```

where every label `ell_c(r)`, `r!=0`, is allowed by the context predicate.
Put

```text
A_(c,x)=sum_a a_x P_(c,a).
```

Suppose that for every shared variable `x` there is one projection `p_x` in
the ambient group algebra satisfying

```text
p_x=((1-A_(c,x))/2)q_c                                  (FFC2)
```

for every context containing `x`.  Then the BCS has a classical satisfying
assignment.

Consequently the explicit Fourier specialization of the affine-Frobenius
packet cannot establish `affine-frobenius-common-negative-carrier` for a BCS
with no perfect finite-dimensional strategy.  Any surviving common-carrier
construction must use genuinely nonabelian projections in the full
Frobenius matrix block and packet overlaps larger than the diagonal prime
kernel mechanism.
