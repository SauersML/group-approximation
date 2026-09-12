---
rg: 2
id: order-twelve-long-head-return-exposes-an-eighth-atom-involution
kind: claim
title: The order-twelve long-head return exposes an identity-outer involution on one eighth atom
artifacts:
  - research/order-twelve-long-head-return-proof.md
distinct_from:
  four-cell-marked-star-has-an-eighth-head-flag: that constructs the monotone three-head eighth source and its order-four optimistic Coxeter holonomy; this constructs a different returned eighth source and computes an exact order-twelve group word on it.
  asymmetric-head-reflection-return-erases-deep-flags: that proves inverse-conjugate reflection returns collapse to a half carrier; this keeps the full eighth carrier by using the third head after a cubic two-head return.
  head-square-whitehead-loop-preserves-deep-star-flag: that produces an odd cube loop but moves the full Pauli chart; this compares two literal square roots of one long prefix root and obtains a same-atom identity-outer involution.
  binary-leavitt-two-shared-gauge-selector-compiler: that needs an identity-outer occurrence carrying one named corrected-Whitehead gauge; this produces an odd corrected-Whitehead occurrence with an additional, still-free relative involution.
---

On the four-cell marked star retain the three asymmetric heads and put

```text
P=H_2H_1,
R_8=H_3P^3,
K=U_2R_8.                                              (OTR1)
```

Let

```text
S=E_4(1-Z_2)(1+Z_3)(1+Z_4)/8.                        (OTR2)
```

The source of `R_8` is `S`, while its range is
`E_4(1+Z_2)(1-Z_3)(1+Z_4)/8`.  The corrected Whitehead `U_2` swaps the
second and third signs, so `K` reduces `S`.

There is an exact elementary-matrix identity

```text
K^6=X_14=x_(10,7)(s_(0000)t_0),
K^12=1,                  order(K)=12.                 (OTR3)
```

This is not merely a sign-actor calculation.  It follows from the literal
Leavitt coefficients on a seven-summand reducing module, and all
complementary summands have period dividing two.

Now form the long asymmetric head from cell one to cell four,

```text
H_14=x_(10,4)(b_4)x_(4,7)(a_1).                       (OTR4)
```

It also reduces `S`, and

```text
H_14^2=X_14.                                          (OTR5)
```

The two square roots admit the exact relative comparison

```text
D=K^3H_14^(-1),              D^2=1.                  (OTR6)
```

On `S`, both `K^3` and `H_14` flip the sole unconstrained sign `Z_1` and
fix the three defining signs.  Their relative word fixes `Z_1`.  It also
commutes with the remaining anchored `A_1` arm.  Therefore, in the
one-qubit Pauli decomposition of `SH`,

```text
D|_(SH)=I_2 tensor D_res,              D_res^2=1.     (OTR7)
```

Thus `(OTR6)` is a genuine same-eighth-atom identity-outer involution.  The
word `K^3` contains the corrected occurrence `U_2` three times, so this is
an odd `U_2` comparison rather than an even power fence.

The opposite long prefix arrow does not remove `D_res`.  Put

```text
Y_14=x_(7,10)(s_0t_(0000)),
J_14=X_14Y_14X_14.                                    (OTR8)
```

Both `Y_14` and `J_14` move `S`: they mix or swap the free first sign with
the fixed fourth sign.  On the same seven-summand block,

```text
order(Y_14D)=order(J_14D)=6.                          (OTR9)
```

Their complementary action has order at most two, so `(OTR9)` holds in the
whole elementary image.  Hence neither the opposite arrow nor the long
Whitehead supplies an odd relation killing `D_res`; both give another
moving-atom even-order actor loop.

The new remaining seam is exact.  One must identify `D_res` with the
already braided `U_2` gauge, or kill it by an odd identity-outer occurrence
that itself preserves `S`.  Merely completing `X_14` to its opposite arrow
or Whitehead does not do so.

The power identities are in the elementary image.  Their written
Steinberg lifts retain the standard possible central `K_2` ambiguity.  No
Property `(T)`, Kazhdan input, canonical trace, local heavy computation, or
literature theorem is used.

DERIVATION
order-twelve-long-head-return-proof
