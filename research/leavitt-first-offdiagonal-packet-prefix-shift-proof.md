---
rg: 2
id: leavitt-first-offdiagonal-packet-prefix-shift-proof
kind: route
title: Multiply the inverse-prefix Whitehead swap by the constant coordinate swap
target: leavitt-first-offdiagonal-packet-breaks-locally-finite-amalgam
requires:
  - leavitt-two-compressor-core-has-modular-normal-form
---

Put `p=s_0t_0` and `q=s_1t_1=1+p`; signs disappear in characteristic two.
The diagonal group `Lambda` contains the constant Weyl swap

```text
P=x_ij(1)x_ji(1)x_ij(1).
```

Hence it also conjugates the second member of the adjoined same-root packet
to the opposite root:

```text
P v P^(-1)=x_ji(t_0).
```

On the `i,j` corner form the ordinary Whitehead word

```text
W=u (P v P^(-1)) u
 = [[q,s_0],[t_0,0]].                                  (FOP2)
```

Indeed, multiplication of the three elementary matrices gives the displayed
matrix because `t_0s_0=1` and `1+s_0t_0=q`.  Moreover

```text
q^2=q,       q s_0=0,       t_0 q=0,       s_0t_0=p,
```

so `W^2=I`.  On the faithful binary stream basis, `W` is exactly the cylinder
swap

```text
(i,0x) <-> (j,x),              (i,1x) fixed.           (FOP3)
```

Now put `a=WP`.  Apply the constant swap `P` first and `(FOP3)` second.  This
gives

```text
(i,x)   -> (i,0x),
(j,0x)  -> (j,x),
(j,1x)  -> (i,1x),                                  (FOP4)
```

with every other coordinate fixed.  Iteration of the first row yields
`a^n(i,x)=(i,0^n x)`.  These prefix maps are distinct for all `n`, proving
that `a` has infinite order.

The old modular LEF argument chose finite vertex subgroups containing every
syllable in a retained multiplication table.  For a table containing `a`,
that choice is impossible in either proposed vertex containing
`<Lambda,u,v>`.  This authenticates the precise failure of the old proof but
does not exclude a different finite partial-embedding construction.
