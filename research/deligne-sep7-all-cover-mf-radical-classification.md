---
rg: 2
id: deligne-sep7-all-cover-mf-radical-classification
kind: claim
title: One circle subgroup simultaneously classifies the MF radicals of all finite Deligne covers
artifacts:
  - research/artifacts/deligne-sep7-all-cover-mf-classification.md
distinct_from:
  deligne-triple-cover-mf-radical-dichotomy: that gives two possibilities for the triple cover; this constrains all finite cover radicals simultaneously by one finite even integer or the full-circle case.
  maslov-ce-subgroup-classifies-finite-deligne-covers: that classifies hyperlinearity through canonical tracial sectors; this computes the entire operator-norm MF radical for every finite cover.
---

Use the integral Deligne extension and cocycle normalization of
`deligne-sep7-norm-parameter-closed-subgroup`. Let

```text
E_q=E_infinity/<z^q>,    q>=1,
K_q=<z_q> = Z/q,
S_q=P_op intersect ((1/q)Z/Z).
```

Then

```text
Rad_MF(E_q) = {z_q^k : exp(2 pi i k theta)=1 for all theta in S_q}.
E_q is MF  iff  1/q in P_op.
```

In particular, exactly one of these two alternatives holds:

1. Every `E_q` is MF and every radical is trivial.
2. There is one positive even integer `m` such that, simultaneously for
   every `q`,

   ```text
   Rad_MF(E_q)=<z_q^gcd(q,m)>,
   |Rad_MF(E_q)|=q/gcd(q,m),
   E_q is MF  iff  q divides m.
   ```

Thus if one finite Deligne cover is non-MF, all but finitely many covering
degrees give non-MF covers. Conversely, MF covers of unbounded degree force
every finite Deligne cover to be MF. In the finite alternative, the exact
triple-cover target is equivalent to `3` not dividing `m`.

These are structural alternatives. Neither their selection nor the integer
`m`, when finite, is determined here. `K_q` denotes the covering kernel,
which need not equal the full group center.
