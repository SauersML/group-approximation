---
rg: 2
id: low-gap-witness-spike-or-balanced-cut-proof
kind: route
title: Clip in operator norm and apply the balanced-cut theorem unless the discarded tail is large
target: low-gap-witness-spike-or-balanced-cut
requires:
  - bounded-low-gap-witness-gives-balanced-cut
---

Let `f=f_C(x)` and `z=x-f`.  The scalar clipping function `f_C` is
1-Lipschitz.  For self-adjoint matrices the Hilbert--Schmidt functional
calculus is Lipschitz with the same constant; applied to `x` and `u_s x
u_s^*`, this gives

```text
||[u_s,f]||_2
 = ||f_C(u_s x u_s^*)-f_C(x)||_2
 <= ||u_s x u_s^*-x||_2
 = ||[u_s,x]||_2.
```

Put `a=||f-tau(f)1||_2` and `b=||z||_2`.  Since `tau(x)=0`,

```text
|tau(f)|=|tau(f-x)|=|tau(z)|<=b.
```

Therefore

```text
1=||x||_2
 <= ||f||_2+||z||_2
 <= a+|tau(f)|+b
 <= a+2b.
```

If `a<1/2`, then `b>1/4`, which is the spike alternative.  Moreover
`z` vanishes on `|x|<=C`, while Markov gives

```text
tau(1_{|x|>C}) <= tau(x^2)/C^2 = 1/C^2.
```

Assume instead `a>=1/2` and normalize

```text
y=(f-tau(f)1)/a.
```

Then `tau(y)=0`, `||y||_2=1`, and

```text
||y||_op <= (||f||_op+|tau(f)|)/a <= 2C/a <= 4C.
```

The clipping estimate above gives

```text
sum_s ||[u_s,y]||_2^2 <= E/a^2 <= 4E.
```

Apply `bounded-low-gap-witness-gives-balanced-cut` to `y` with operator bound
`4C`.  It returns a spectral projection of `y`, hence a projection in
`W*(x)`, with

```text
1/(4(4C)^2) <= tau(q) <= 1-1/(4(4C)^2)
```

and commutator energy at most

```text
2(4C) sqrt(m*4E)=16 C sqrt(mE).
```

This is exactly the balanced-cut alternative.
