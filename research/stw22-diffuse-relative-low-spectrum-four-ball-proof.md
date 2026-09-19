---
rg: 2
id: stw22-diffuse-relative-low-spectrum-four-ball-proof
kind: route
title: Run the relative dyadic-band recursion with degree-three Stiefel values
target: stw22-diffuse-relative-low-spectrum-four-ball-extension
requires:
  - stw22-diffuse-stiefel-uniform-three-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-three-ball-extension
artifacts:
  - research/artifacts/stw22-dim4-factor-bundle-breakthrough-2026-08-31.md
---

Put `delta_0=tau(e)-tau(p_h)-tau(p_l)>0`. If `b=0`, take `X=0`.
Otherwise choose `E>0` with `b<=Ep_l` and split

```text
I_n=(E2^(-(n+1)),E2^(-n)],
r_n=1_(I_n)(b),       sum_n r_n=p_l.                   (TR4-5)
```

Discard zero bands. The boundary band frame

```text
xi_n(z)=x(z)b^(-1/2)r_n                               (TR4-6)
```

is continuous.

Suppose the preceding bands have been extended by frames `V_k` with
orthogonal ranges and put

```text
g_n(y)=f(y)-sum_(k<n)V_k(y)V_k(y)^*.                  (TR4-7)
```

Then

```text
tau(g_n(y))-tau(r_n)
 =tau(e)-tau(p_h)-sum_(k<=n)tau(r_k)>=delta_0.         (TR4-8)
```

Use the full interior values

```text
Phi_n(y)={v:v^*v=r_n, vv^*<=g_n(y)},                  (TR4-9)
```

and replace them on `S^3` by the singleton `{xi_n(y)}`. The modified map
is lower semicontinuous. In the interior this is the standard close-frame
argument. At a boundary point, lower semicontinuity of the full map and
continuity of `xi_n` give two neighbourhoods whose intersection meets any
prescribed open set. This is the same exact relative argument as in the
three-ball proof and assumes no collar extension.

For each full value choose a reference frame `t` with `t^*t=r_n` and
`tt^*<=g_n(y)`. Multiplication `v |-> vt^*` identifies it isometrically
with a Stiefel space in the diffuse corner `g_n(y)Ng_n(y)`. By (TR4-8),
the corner trace is at least `delta_0`. The universal path, loop,
two-sphere, and new three-sphere Stiefel moduli, after normalized-corner
scaling, give common local moduli in degrees `0,1,2,3`. Every value is
three-connected; singleton boundary values are trivially so.

Michael's theorem with `n=3` selects `V_n:B^4->N` from the modified
multifunction. Its boundary is exactly `xi_n`, and (TR4-8) persists.

Define

```text
X_N(y)=sum_(n=0)^N V_n(y)b^(1/2)r_n.                  (TR4-10)
```

Range orthogonality gives

```text
||X_M(y)-X_N(y)||_2^2
 =sum_(N<n<=M)tau(br_n),                               (TR4-11)
```

uniformly in `y`. Thus `X_N` converges uniformly in `2`-norm inside the
operator unit ball. Passing products to `L^1` yields (TR4-3); the same
tail identity gives the exact boundary. Finally the diameter of the
weighted fibre is at most `2sqrt(tau(b))`, proving (TR4-4).