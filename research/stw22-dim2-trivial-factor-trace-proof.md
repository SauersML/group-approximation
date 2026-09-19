---
rg: 2
id: stw22-dim2-trivial-factor-trace-proof
kind: route
title: Replicate every fibre-gap cut into arbitrarily many selected weighted copies
target: stw22-dim2-trivial-factor-bundles-have-uniform-traces
requires:
  - stw22-diffuse-weighted-purification-uniform-loop-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-dim2-arbitrary-factor-breakthrough-2026-08-30.md
---

Write `M=C_sigma(X,N)`. For `x in X`, let

```text
J_x=closure(C_0(X\{x})M),
K_x={b in M:b(x)=0 in L^2(N)},
I_x=K_x/J_x.                                            (DT2)
```

It suffices, by
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity`, to prove that
`I_x` has no nonzero bounded positive trace.

Let `sigma` be such a trace and let `0<=b<=1` lie in `K_x`. Fix
`epsilon>0` and put `c=(b-epsilon)_+`. For every integer `m>=1`,
Chebyshev's inequality and `2`-norm continuity at `x` give a
neighbourhood `V` of `x` on which

```text
tau(supp(c(t))) < 1/(2m).                               (DT3)
```

Choose a central scalar cutoff `h` equal to one near `x` and supported
in `V`, and set `d=hc`. Then `[d]=[c]` in `I_x`, while `(DT3)`
holds on all of `X` for `d`.

Choose pairwise orthogonal projections

```text
e_1,...,e_m in N,       tau(e_j)=1/m.                   (DT4)
```

For each `j`, apply
`stw22-diffuse-weighted-purification-uniform-loop-fillings` to the field
`d:X->N_+`, with `s=1/(2m)<tau(e_j)`. Michael selection produces a
section `v_j in M` satisfying

```text
v_j^*v_j=d,       v_jv_j^*<=e_j.                        (DT5)
```

Because `d(x)=0`, all `v_j` lie in `K_x`. Their range elements are
orthogonal positive contractions, so traciality in the quotient gives

```text
m sigma([c])
 =sum_j sigma([v_j^*v_j])
 =sigma(sum_j [v_jv_j^*])
 <=||sigma||.                                           (DT6)
```

The integer `m` was arbitrary; hence `sigma([c])=0`. Letting
`epsilon` decrease to zero in norm gives `sigma([b])=0`. Thus every
bounded positive trace on every `I_x` vanishes.

The fibre-gap criterion now shows that every trace on `M` is an integral
of the fibre trace. Its restriction to the central copy of `C(X)`
determines the Radon measure uniquely, and Cauchy--Schwarz gives uniform
`2`-norm continuity. This proves `(DT1)`.
