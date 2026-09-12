---
rg: 2
id: steinberg-schur-geometric-row-transform
kind: claim
title: Geometric row sums give a resonance-safe four-exponential Schur transform
invalidates:
  - steinberg-schur-single-geometric-endpoint-extraction
distinct_from:
  steinberg-schur-corrected-endpoint-reduction: that gives the exact endpoint matrix R; this sums all its rows against one geometric weight and identifies the remaining exponential families.
  steinberg-schur-antidiagonal-resonates: that blocks division by individual cyclotomic coefficients; this transform never divides by them.
---

**ESTABLISHED RESONANCE-SAFE TRANSFORM.**  Let `d=p-3`, let `R` be the
matrix in `(SCE7)`, and for `2<=v<=d` put

```text
W_v(t)=sum_(j=3)^d t^(j-1) R_(j,v).                    (SGT1)
```

For `t in F_p\{0,1}`, set

```text
s=(-1)^(v-1),       a=t/(t-1),
b=1+1/(4t),         d_0=1+1/t.
```

Then exact binomial summation gives

```text
W_v(t)=s{a^(v-1)+2b^v-d_0^v-2-v/(2t)
          -[binom(v,2)/8+v]/t^2}
       -t^(v-1).                                      (SGT2)
```

For the Pascal part, use

```text
sum_(n=0)^(p-1) binom(n,v-1)t^n
 =s t^(v-1)(t-1)^(p-v),                               (SGT3)
```

then subtract the diagonal and the `p-3,p-2,p-1` endpoints.  For the
antidiagonal, substitute `k=p-j` to obtain

```text
s sum_(k=3)^v binom(v,k)t^(-k)(2*4^(-k)-1),            (SGT4)
```

and apply the two binomial theorems.  These formulas remain valid at
`v=2,d`: the antidiagonal sum is empty at the first boundary, and the four
subtracted Pascal endpoints cancel the full sum at the second.

The exceptional weights are explicit: `W_v(0)=0`, while

```text
W_v(1)=(-1)^v binom(v+2,2)-1
 +s{2(5/4)^v-2^v-1+v/2+(7/8)binom(v,2)}.              (SGT5)
```

No factor `2^(2j-1)-1` is inverted.

There is also a scoped no-go.  For `p>=11`, no single `W(t)` is a nonzero
scalar multiple of the endpoint row `c_v=s v`.  After division by `s`,
`(SGT2)` is a sum of at most four pure exponentials with bases
`a,b,d_0,-t` and a quadratic polynomial whose `v^2` coefficient is
`-1/(16t^2)`.  On `v=2,...,8`, distinct nonzero bases together with
`1,v,v^2` are independent by the confluent Vandermonde determinant;
coincident, zero, or unit bases only reduce the exponential span and cannot
cancel the nonzero quadratic coefficient.  Formula `(SGT5)` has coefficient
`-1/16`, and `t=0` is the zero row.

Two or more geometric weights can cancel the quadratic coefficient, so this
does not refute a finite-combination extraction.  It reduces that live
problem to simultaneous cancellation of the four Möbius-push exponential
families.
