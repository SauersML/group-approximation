---
rg: 2
id: stw22-diffuse-relative-low-spectrum-three-ball-proof
kind: route
title: Apply degree-two relative selection to each bounded spectral band
target: stw22-diffuse-relative-low-spectrum-three-ball-extension
requires:
  - stw22-diffuse-stiefel-uniform-two-sphere-fillings
artifacts:
  - research/artifacts/stw22-dim3-diffuse-bundle-breakthrough-2026-08-30.md
---

Put `delta_0=tau(e)-tau(p_h)-tau(p_l)>0`. If `b=0`, then
`p_l=0`, `x=0`, and `X=0` proves every assertion, so assume `b` is
nonzero. Choose `E>0` with `b<=E p_l` (for (TR4), take the displayed
`eta`) and split

```text
I_n=(E 2^(-(n+1)),E 2^(-n)],
r_n=1_(I_n)(b),        sum_n r_n=p_l.                   (TR5)
```

Discard zero bands. The boundary band frame

```text
xi_n(z)=x(z)b^(-1/2)r_n                                (TR6)
```

is continuous because the inverse square root is bounded on `r_n`.

Suppose `V_0,...,V_(n-1)` have been extended with orthogonal ranges and
put

```text
g_n(y)=f(y)-sum_(k<n)V_k(y)V_k(y)^*.                    (TR7)
```

Then `g_n` is a continuous projection field and

```text
tau(g_n(y))-tau(r_n)
 =tau(e)-tau(p_h)-sum_(k<=n)tau(r_k)
 >=delta_0.                                             (TR8)
```

Let the full interior value be

```text
Phi_n(y)={v:v^*v=r_n, vv^*<=g_n(y)}.                    (TR9)
```

On `S^2` replace it by the singleton `{xi_n(y)}`. The modified
multifunction is lower semicontinuous. In the interior this is the standard
close-subprojection and close-unitary argument. At `z_0 in S^2`, if an
open set `U` contains `xi_n(z_0)`, lower semicontinuity of the full
multifunction gives a neighbourhood `V_1` on which every full value meets
`U`; continuity of `xi_n` gives `V_2` with
`xi_n(S^2 intersect V_2) subset U`. Thus every modified value over
`V_1 intersect V_2` meets `U`. This is the exact relative argument;
no collar extension is assumed.

Choose, separately for this value, a reference frame `t` with
`t^*t=r_n` and `tt^*<=g_n(y)`. Multiplication `v |-> vt^*` is an
isometry from the full value in (TR9) onto the strong Stiefel space
`St_(g_n(y)Ng_n(y))(tt^*)`; this is an isometric identification, not an
assertion that `r_n<=g_n(y)`. Put `t=tau(g_n(y))`. By (TR8),
`t>=delta_0`. Normalize the corner metric by dividing by `sqrt(t)`.
The universal two-sphere modulus from
`stw22-diffuse-stiefel-uniform-two-sphere-fillings`, together with the
path modulus and the loop modulus from its degree-zero and degree-one
predecessors, and scaled back by `sqrt(t)`, gives common ambient moduli
in degrees `0,1,2` for all full values. Thus the family is equi-`LC^2`
in Michael's sense. Every full value is two-connected by the same three
results. Singleton
boundary values are trivially two-connected and satisfy every local
modulus. Hence the modified value family is equi-`LC^2`, consists of
closed two-connected subsets of the complete operator-norm unit ball of
`L^2(N)`, and is lower semicontinuous.

Michael's *Continuous Selections II*, Theorem 1.2, with `n=2`, now
selects `V_n:B^3->N` from the modified multifunction. Its boundary is
exactly `xi_n`. Equation (TR8) persists, so the construction iterates.

Define

```text
X_N(y)=sum_(n=0)^N V_n(y)b^(1/2)r_n.                    (TR10)
```

Orthogonality gives the uniform tail identity

```text
||X_M(y)-X_N(y)||_2^2
 =sum_(N<n<=M)tau(br_n).                                (TR11)
```

Thus `X_N` converges uniformly in `2`-norm. Since
`X_N^*X_N<=b`, the limit lies in the operator-norm unit ball of `N`.
Passing products to `L^1` gives `X^*X=b` and `fX=X`; (TR6) and
(TR11) give the exact boundary. Finally
`||X-x_0||_2<=2sqrt(tau(b))`, proving (TR4).
