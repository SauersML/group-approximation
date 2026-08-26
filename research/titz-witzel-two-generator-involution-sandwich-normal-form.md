---
rg: 2
id: titz-witzel-two-generator-involution-sandwich-normal-form
kind: claim
title: The final Titz--Witzel gate is an involution-sandwich system
distinct_from:
  titz-witzel-sofic-gate-two-generators-four-approximate-relators: That gives the two-generator five-relator gate in the words inherited from the seven-relator presentation; this replaces its two longest coupling relators by a square-root equation and then by an involution-sandwich equation.
  titz-witzel-two-generator-gate-forces-macroscopic-noncommutation: That extracts one metric obstruction from the derived square; this is an exact Tietze transformation of all three remaining coupling equations and a quantitative equivalence of finite models.
artifacts:
  - research/artifacts/titz-witzel-involution-sandwich-check.py
---

**THEOREM.**  Retain the words `h,a,x,c,f,d,s,rho` from `(TW2G1)` in
`titz-witzel-sofic-gate-two-generators-four-approximate-relators`, and define

```text
beta = rho e rho^(-1),             p = beta a.                    (TWIS1)
```

Then the smallest Titz--Witzel group has the exact presentation

```text
<e,u | e^2,
       c^2,
       rho^2 e u^(-1),
       beta a u d^(-1),
       p u p c>.                                                (TWIS2)
```

In particular, after the exact involution `e` and the derived words have
been evaluated, the four genuinely approximate equations can be read as

```text
c^2=1,            u=rho^2 e,            d=p u,            c=p u p.  (TWIS3)
```

Here `h,a,f,s,beta` are all conjugates of `e`, hence are honest
involutions in every finite model in which `e^2=1`; `c` is the only derived
word which is merely an approximate involution.  Thus `p` is a product of
two exact matchings.  The separating word remains literally `u^8`.

There is also an equivalent square-root-chain form.  The last relator in
`(TWIS2)` may be replaced by

```text
d^2 u^(-1)c.                                                (TWIS4)
```

So, on exact solutions, the final two old quartics say

```text
d=p u,                    d^2=c u.                         (TWIS5)
```

All these replacements preserve asymptotic finite-permutation solutions,
not just the presented abstract group.  More precisely, let `delta_0` be
the defect of `rho^2 e u^(-1)`, let `delta_P,delta_Q` be the defects of the
last two relators in `(TW2G2)`, and let `eta_P,eta_W,eta_J` be the defects
of `beta a u d^(-1)`, `d^2u^(-1)c`, and `pupc`, respectively.  In every
bi-invariant metric, assuming only `e^2=1`,

```text
|eta_P-delta_P| <= delta_0,
eta_W <= delta_Q+delta_P,
delta_Q <= eta_W+delta_P,
|eta_J-eta_W| <= 2 eta_P.                                  (TWIS6)
```

(Replacing `delta_P` by `eta_P+delta_0` in the middle two inequalities
gives bounds entirely in the new defects.)  Hence the old four defects
vanish exactly when the four defects in `(TWIS2)` vanish, and likewise for
the square-root-chain form.  This makes the residual geometry of the gate
considerably more explicit, but it does not construct the required models
or decide soficity.

---

### Proof

titz-witzel-involution-sandwich-proof
