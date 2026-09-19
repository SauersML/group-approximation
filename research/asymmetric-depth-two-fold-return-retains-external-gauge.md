---
rg: 2
id: asymmetric-depth-two-fold-return-retains-external-gauge
kind: claim
title: The asymmetric depth-two completeness return is exactly the old gauged external root
artifacts:
  - research/asymmetric-depth-two-fold-return-proof.md
distinct_from:
  one-asymmetric-prefix-cannot-be-signed-hecke-return: that proves one nonconstant root cannot return to the signed carrier; this gives the first paired nonconstant return, using three private branch excursions whose coefficients sum to one, and computes why it still does not cancel the external gauge.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that closes the complete affine depth-one actor menu; this treats the first genuinely asymmetric complete prefix code with leaf depths two, two, and one.
  one-singer-square-does-not-identify-external-return-gauge: that starts from the constant external root as an opaque occurrence; this expands that root into literal address-dependent Leavitt commutators and shows that the expansion adds no new same-carrier gauge equation.
---

**ESTABLISHED DEPTH-TWO FOLD FENCE.**  Use the asymmetric complete binary
prefix code

```text
P={00,01,1},             e_w=s_wt_w,
e_00+e_01+e_1=1.                                      (DTR1)
```

For the coordinate-matched external return `x_78(1)`, choose distinct spare
indices `10,11,12` and form the literal ordinary EL20 word

```text
R=[x_(7,10)(s_00),x_(10,8)(t_00)]
  [x_(7,11)(s_01),x_(11,8)(t_01)]
  [x_(7,12)(s_1), x_(12,8)(t_1)].                    (DTR2)
```

The three Steinberg commutators are respectively
`x_78(e_00),x_78(e_01),x_78(e_1)`.  Root additivity and `(DTR1)` therefore
give the exact full-group identity

```text
R=x_78(1).                                             (DTR3)
```

Thus `(DTR2)` is a genuine paired nonconstant same-Hecke-carrier return, but
its restriction to the signed Hecke carrier has exactly the old normal form

```text
R|_Q=N_78 tensor E,                                   (DTR4)
```

including the uncontrolled external-return reservoir involution `E`.  The
private arm factors in `(DTR2)` do not individually reduce `Q`, so they do
not provide three independently typed reservoir occurrences whose apparent
parity could be cancelled.

Let `J=J_1` be the first literal Whitehead, put `Q'=JQJ^(-1)`, and let
`R'=JRJ^(-1)`.  The complete mixed Singer/Whitehead square is the ordinary
identity

```text
JR=R'J.                                                (DTR5)
```

Writing the Whitehead gauge as `D` and the target return gauge as `E'`,
removal of the fixed label maps from `(DTR5)` gives only

```text
E'=DED^(-1),                                           (DTR6)
```

exactly as for the unexpanded constant root.  It gives neither `[D,E]=1`
in one fixed Hecke frame nor `D=E`.  The same statement holds for the full
Singer head `Jv_1`, since the source normalizer `v_1` only changes the fixed
label chart.

More generally, for every finite complete prefix code `P` and distinct
private spare indices `k_w`,

```text
product_(w in P)[x_(a,k_w)(s_w),x_(k_w,b)(t_w)]
 =x_ab(sum_(w in P)e_w)=x_ab(1).                      (DTR7)
```

Consequently no pure prefix-code completeness expansion of one of the eight
external returns can be the ungauged bridge `(ESB2)`: it is the same group
element and carries the same reservoir action.  Any Hall--Witt or naturality
cell obtained solely by conjugating `(DTR7)` is functorial covariance of that
same occurrence and again yields `(DTR6)`.

This does not fence a depth-two word in which different nonconstant root
channels interact before the final return, rather than three private arms
folding additively into one root subgroup.  Such a nonseparated mixed-channel
cell is the next possible asymmetric ESB candidate.

No Property T, Kazhdan input, trace assumption, computation, or literature
theorem is used.

DERIVATION
asymmetric-depth-two-fold-return-proof
