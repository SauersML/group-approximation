---
rg: 2
id: hnn-compressed-row-fixed-carrier-proof
kind: route
title: Multiply the HNN commutator by its compressed transporter and apply Britton
target: hnn-compressed-row-is-unnamed-fixed-carrier
requires: []
---

Because `[b,p]=0`, direct multiplication gives

```text
(u-1)tp
 =a t b^(-1)p-tp
 =(a t p-t p b)b^(-1).                                (HCR6)
```

Right multiplication by `b^(-1)` preserves normalized Hilbert--Schmidt
norm, proving the first identity in `(HCR2)`.  Since `t` is unitary and `p`
is a projection,

```text
||tp||_2^2=tau(p).
```

Right multiplication of `(HCR6)` by `t^(-1)` proves `(HCR3)`.  Finally,

```text
(u^2-1)P=u(u-1)P+(u-1)P,
```

so `(HCR5)` costs at most twice `(HCR4)`.

It remains to check the marked word.  In the convention
`tAt^(-1)=C`, the only possible pinch inside

```text
u=a t b^(-1)t^(-1)
```

would require `b in A`.  At the cyclic seam between two copies of `u`, the
only possible pinch would require `a in C`.  Both are excluded.  Hence every
positive power of `u` is Britton reduced and contains stable letters.
Britton's lemma makes every such power nonidentity, so `u` has infinite
order.
