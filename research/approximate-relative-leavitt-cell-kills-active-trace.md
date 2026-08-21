---
rg: 2
id: approximate-relative-leavitt-cell-kills-active-trace
kind: claim
title: One approximate relative Leavitt cell kills active trace with a dimension-free constant
distinct_from:
  affine-active-corner-has-faithful-binary-leavitt-envelope: that constructs the exact relative corner and compares finite module dimensions; this is the robust normalized-HS trace inequality after its coefficient operators have been decoded.
  finite-window-decoder: that asks to extract Leavitt coefficient operators from group microstates; this assumes those operators are already present and proves the terminal payment inequality.
  finite-packet-cannot-realize-absorbing-contraction: that refutes a universal contraction certified by a finite packet character table; this uses a properly infinite relative Leavitt relation unavailable in the finite packet.
---

Let `P in M_d(C)` be an orthogonal projection and let
`S_0,S_1,T_0,T_1` be contractions.  Put

```text
epsilon_i=||T_iS_i-P||_(2,d),
epsilon_sum=||S_0T_0+S_1T_1-P||_(2,d).                   (ARL1)
```

Then

```text
tr_d(P) <= epsilon_0+epsilon_1+epsilon_sum.                (ARL2)
```

In particular, if all three displayed defects are at most `epsilon`, then

```text
tr_d(P)<=3 epsilon.                                        (ARL3)
```

No off-diagonal relation `T_iS_j=0`, support relation, integrality, or lower
bound on `rank(P)` is needed for this estimate.

Indeed normalized trace is cyclic, so

```text
tr_d(S_iT_i)=tr_d(T_iS_i).
```

The normalized trace functional has norm one with respect to normalized
Hilbert--Schmidt norm.  Hence

```text
|tr_d(S_0T_0+S_1T_1)-2tr_d(P)| <= epsilon_0+epsilon_1,
|tr_d(S_0T_0+S_1T_1)-tr_d(P)| <= epsilon_sum.
```

Subtracting the two target scalars and using `tr_d(P)>=0` gives `(ARL2)`.

Thus the relative Leavitt branch already supplies the desired
amplification-stable local payment.  For an involutive marked carrier
`W=1-2P`, `(ARL3)` gives

```text
||W-I||_2^2=4tr_d(P)<=12epsilon.                           (ARL4)
```

The outstanding group problem is not the return arithmetic.  It is a
decoder which extracts `P,S_i,T_i` with defects controlled by the defining
group-word energy from a normalized-HS almost representation of the affine
Leavitt Steinberg group.
