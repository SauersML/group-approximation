---
rg: 2
id: minimal-t00-conversion-cannot-return-native-whitehead-root
kind: claim
title: The minimal t00 coefficient conversions cannot return to a native Whitehead root through signed L0
artifacts:
  - experiments/native_coefficient_conversion_l0_return_audit.py
  - research/minimal-t00-native-return-audit-proof.md
distinct_from:
  signed-l0-does-not-attach-cross-returns-to-order-seven-head: that tests the `r` and `b_2` branch-return occurrences against the native head arms; this starts from the two nested chains that already produce `x_1,x_2` and tests the minimal coefficient changes to the missing reverse Whitehead coefficients `y_2,y_1`.
  leavitt-compression-preserves-root-position-support: that shows canonical coefficient compression preserves root positions and therefore misses the Singer move; this shows a Steinberg multiplication can change the coefficient correctly only by changing an endpoint which signed `L_0` cannot return.
  same-center-whitehead-native-selector-subcorner-attachment: that asks for an odd native selector occurrence on a positive model-dependent carrier; this fences only the smallest nested-chain plus one coefficient-conversion cell and signed-`L_0` return menu.
---

**ESTABLISHED MINIMAL-CONVERSION FENCE.**  Write

```text
N_9=x_79(1),       A_1=x_47(r),       B_2=x_84(b_2),
A_2=x_58(a_2),     B_3=x_95(b_3),                       (TCR1)
```

where `a_2=s_1t_00`, `b_2=s_00t_1`, and `b_3=s_000t_1`.
The two exact nested Steinberg chains are

```text
[B_2,[A_1,N_9]]=x_89(b_2r)=x_89(x_1),
[[N_9,B_3],A_2]=x_78(b_3a_2)=x_78(x_2),                (TCR2)
```

with

```text
x_1=s_00t_0,       x_2=s_000t_00.                      (TCR3)
```

These are genuine same-packet coefficient-sensitive chains through the
positive signed-`L_0` root `N_9`.  Their coefficients are the forward arms
of the native Whiteheads, but the missing reverse arms are

```text
y_2=s_00t_000,      y_1=s_0t_00.                       (TCR4)
```

The canonical minimal coefficient changes have degree minus two:

```text
x_1t_00=y_2,        t_00x_2=y_1,       t_00=t_1a_2.   (TCR5)
```

Any elementary Steinberg multiplication realizing the first row of
`(TCR5)` sends `x_89(x_1)` to a root `x_(8,ell)(y_2)` with
`ell!=8,9`; realizing the second sends `x_78(x_2)` to
`x_(ell,8)(y_1)` with `ell!=7,8`.  The endpoint change is forced because a
Steinberg product uses two distinct composable root positions.

There is no signed-`L_0` return to the native positions.  Exhausting all
`8192` signed-`L_0` matrices gives, for every allowed actor spare endpoint,

```text
x_(8,ell)(y_2) is not L_0-conjugate to x_89(y_2),
x_(ell,8)(y_1) is not L_0-conjugate to x_78(y_1).       (TCR6)
```

The first row tests `ell in {2,4,5,6,7}` and the second tests
`ell in {2,4,5,6,9}`.  There are zero conjugators in all ten cases.

Thus the smallest coefficient-conversion cell succeeds algebraically but
cannot be returned to the literal reverse-root occurrence of either native
Whitehead while preserving the signed carrier.  The displayed chains and
conversion cells are nested commutators and contain no odd literal `J_i`
or `v_i` factor.  Appending such a factor would be a new carrier-return
relation, not a consequence of `(TCR1)--(TCR6)`.  This fence does not rule
out a larger opposite-root loop which performs that additional return.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
minimal-t00-native-return-audit-proof
