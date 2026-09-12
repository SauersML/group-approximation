---
rg: 2
id: external-normalizer-dressed-cell-has-full-gauged-gram
kind: claim
title: A second mixed-cell transport exists but its relative loop is an external spectator gauge
artifacts:
  - research/external-normalizer-dressed-cell-proof.md
  - experiments/second_mixed_cell_transport_normalizer_audit.py
  - experiments/external_normalizer_order_five_cell_audit.py
distinct_from:
  mixed-whitehead-cell-moves-signed-source: that constructs the undressed simultaneous transport and computes its moved signed source; this finds a second transport with a nontrivial source-normalizing relative loop.
  eight-external-returns-have-no-whitehead-gauge-lock: that exhausts each external root against the two native Whitehead/Singer rows; this singles out the unique external root centralizing the concrete g-star depth-two cell.
  signed-hecke-normalizer-has-eight-external-root-returns: that enumerates the complete external root-normalizer list and leaves every multiplicity factor uncontrolled; this inserts one such root as the relative loop of two actual cell transports.
---

**ESTABLISHED SECOND-TRANSPORT FENCE.**  Retain the simultaneous mixed
transport `H` from `(SMP1)` and put

```text
n=x_59(1),                 H'=Hn.                     (SCT1)
```

The root `n` is one of the eight external constant-root normalizers of the
signed pair.  It commutes with all three words defining the depth-two cell,

```text
[n,g_*]=[n,Y_2]=[n,A_(2,2)]=1.                        (SCT2)
```

Consequently `H'` is a second exact ordinary transport of the complete
depth-two cell to the same depth-three cell, and

```text
(H')^(-1)H=n.                                         (SCT3)
```

This is nonidentity, belongs to `Norm(L_0,lambda_0)`, and is not the
tautological inverse loop.  Among all eight external root normalizers,
`x_59(1)` is the unique one satisfying `(SCT2)`.  Among all `21` constant
root normalizers there are eight cell centralizers: seven lie in `L_0` and
the remaining one is `n`.

The second transport does not return the moved signed source to `Q`.  Since
`n` preserves `Q`, both `H` and `H'` carry

```text
Q -> Q'=HQH.
```

Their compressed transports

```text
T=Q'HQ=HQ,                 T'=Q'H'Q=HnQ               (SCT4)
```

have the same full Grams

```text
T^*T=(T')^*T'=Q,           TT^*=(T')(T')^*=Q',
T^*T'=nQ.                                               (SCT5)
```

Thus the relative cross Gram is itself a full unitary, not a proper common
subrange or a nonmaximal overlap.  On the signed character carrier the
external return has the established normal form

```text
n|Q=N_59 tensor E_59,                                  (SCT6)
```

where `N_59` is the finite label normalizer and the multiplicity involution
`E_59` is uncontrolled.  The seven internal alternatives instead restrict
to the known character scalars.  Hence the only non-scalar second transport
adds precisely the old external spectator gauge; it does not identify the
two native cell gauges or fix the moved-source chart.

Left or right dressing by the signed normalizer keeps every candidate in
the double coset

```text
Norm(L_0,lambda_0) H Norm(L_0,lambda_0).               (SCT7)
```

Such dressing can change the source and target frames only by their own
normalizer actions.  It cannot change the fact that the middle `H` moves
`Q` to `Q'`, and two candidates with the same target have a full normalizer
cross Gram as in `(SCT5)`.  Coordinate-root Weyl variants either fail one
cell covariance or reduce to the eight centralizers classified above.

Therefore a nontrivial normalizing relative loop does exist, but it is a
maximal-overlap spectator rather than the missing fixed-frame gauge lock.
The next useful second transport must have a proper range Gram or a relative
word whose finite label action removes, rather than introduces, `E_59`.

The adjacent odd anchor does not remove this fence.  With the native
orientation

```text
J_2=x_98(x_2)x_89(y_2)x_98(x_2),
M=J_2B_3A_2,              C=WM,
M^7=C^5=1,                                             (SCT8)
```

exact faithful Leavitt multiplication gives

```text
[n,W]=[n,A_2]=1,
[n,J_2],[n,B_3],[n,M],[n,C] !=1,                      (SCT9)
nCn notin <C>,              |Orb_<C>(n)|=5.
```

More decisively, both odd actors move the entire signed source group off
itself:

```text
L_0 intersect ML_0M^(-1)={1},
L_0 intersect CL_0C^(-1)={1}.                         (SCT10)
```

Thus neither `M` nor the order-five word `C` acts on `Q`; their relations
compare distinct source frames and do not impose an equation on the
multiplicity involution `E_59` in `(SCT6)`.  The ordered product of the five
`C`-conjugates of `n` is also nonidentity, so the odd orbit has no
tautological telescope returning that gauge to the initial frame.  A bounded
reduced-word audit through length eight finds no expression for `n` in
`<W,M>`; this last statement is only a short-profile fence, whereas
`(SCT8)--(SCT10)` are exact.

Tuple orientation is load-bearing in this audit: elementary-word tuples are
`(source,target,coefficient)`.  Hence the native `J_2` above is the helper
call `whitehead(8,9,2)`.  Reversing those arguments produces a different
word for which the seventh- and fifth-power relations are false.
No Property `(T)`, canonical trace, literature input, local computation, or
Lean compilation is used.

DERIVATION
external-normalizer-dressed-cell-proof
