---
rg: 2
id: coarse-to-fine-prefix-isometry-proof
kind: route
title: Compare the two minimal-corner ranks and factor the prefix partial swap
target: one-coarse-to-fine-prefix-isometry-closes-the-reservoir
requires: []
---

Exact `r by r` matrix units with identity `P` have Murray--von Neumann
equivalent diagonal projections summing to `P`; hence every `e_ii` has rank
`rank(P)/r`.  The same argument gives `rank(f_aa)=rank(P)/s`.

Because `X=fXe`, the rank of `X^*X` is at most `rank(f)`.  Its kernel inside
`eH` therefore has dimension at least `rank(e)-rank(f)`.  On that kernel
`e-X^*X=1`, so normalized Hilbert--Schmidt norm gives

```text
||e-X^*X||_2^2
 >=(rank(e)-rank(f))/d
 =tr(P)(1/r-1/s).                                      (CFP1)
```

For the prefix bridge, repeated cancellation gives

```text
(s_0t_(00))(s_(00)t_0)=s_0t_0,
(s_(00)t_0)(s_0t_(00))=s_(00)t_(00).                  (CFP2)
```

Finally multiply the three matrices in `(CFI9)`.  In characteristic two,
using `xy=f`, `yx=e`, `fx=x=xe`, the result is

```text
[[1+f,x],[y,1+e]]=[[1-f,x],[y,1-e]]=J_x.              (CFP3)
```

The same identities give `J_x^2=1`.

