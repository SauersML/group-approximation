---
rg: 2
id: steinberg-fox-chord-actions-are-explicit
kind: claim
title: Every coefficient in the Steinberg Fox rows is an explicit rational chord map plus a tree cut
artifacts:
  - research/steinberg-fox-chord-action-proof.md
---

Let `p` be odd.  Use the chord coordinates `(a,b,c)` of `(SBC2)` and the operators `L_g` of
`(SBC4)`.  Away from the displayed zero denominators,

```text
L_g f(a,b,c)=f(tau_g(a,b,c)),                           (SCA1)
```

where

```text
tau_q(a,b,c)=(a+1/2,b,c),
tau_s(a,b,c)=(a,b+a/2,c+1/2),

tau_A(a,b,c)=(a/d_A,b/d_A,c d_A+2b),
                         d_A=1-2a,

tau_B(a,b,c)=(4(a-b),2b,c/(2d_B)),
                         d_B=1-c,

tau_u(a,b,c)=((a+b/2)/d_P,b/d_P,c/d_H),
                         d_P=1-b,
                         d_H=1+ac-b+c/2,

tau_r(a,b,c)=(a+b,b,c/d_r),
                         d_r=1+c,

tau_(h^(-1))(a,b,c)=(a/2,b/4,c/2).                    (SCA2)
```

If a displayed denominator vanishes, the transformed flag lies in the
fixed tree `T`, and `L_g f(a,b,c)` is exactly the signed cut-sum from
`(SBC3)`.  There are no other exceptional cases.  Moreover

```text
L_(gh)=L_g L_h,                                        (SCA3)
```

so `(SCA2)` and the tree-cut rule evaluate every term in both recurrences
`(SBC5)`, including `Aq,Bs,uq,h^(-1)r`.

In particular, wherever all flags occurring below remain chords, `(SBC5)`
is literally

```text
 f(tau_A x)-f(tau_q tau_A x)
+f(tau_B x)-f(tau_s tau_B x)-f(x)=0,

 f(x)-f(tau_q x)-f(tau_u x)+f(tau_q tau_u x)
-f(tau_r tau_(h^(-1)) x)+f(tau_(h^(-1)) x)=0.         (SCA4)
```

Here juxtaposition of the `tau` symbols means composition from right to
left.  On a zero-denominator locus, exactly the affected evaluation in
`(SCA4)` is replaced by its predetermined tree-cut sum.

DERIVATION
steinberg-fox-chord-action-proof
