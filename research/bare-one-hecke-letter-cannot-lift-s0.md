---
rg: 2
id: bare-one-hecke-letter-cannot-lift-s0
kind: claim
title: A bare one-letter Hecke element cannot lift the Leavitt generator s0
distinct_from:
  rank-five-rectangle-is-one-letter-hecke-element: that normalizes a hypothetical five-term factor already known to have a one-sided inverse; this tests whether such a normalized factor can be chosen directly over s0.
  leavitt-rank-three-unit-lift: that gives a three-unit additive lift; this proves the proposed two-term lift with one term equal to the identity is impossible.
  binary-leavitt-algebra-not-directly-finite: that proves s0 is not a unit; this proves the different element 1+s0 is not a unit by the grading.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

For every `y in R^x`,

```text
pi_e(e(1+[y])e)=1+y != s_0.
```

Indeed equality would give `y=1+s_0`.  If `(1+s_0)b=1` for a finite graded
sum with degree range `[m,n]`, then for `n>=0` the degree `n+1` term is the
nonzero uncancelled `s_0b_n`; for `n<0`, the negative degree `m` term is the
uncancelled `b_m`.  Here `t_0s_0=1` makes left multiplication by `s_0`
injective.  Both cases contradict a degree-zero product, so `1+s_0` is not a
group unit.
