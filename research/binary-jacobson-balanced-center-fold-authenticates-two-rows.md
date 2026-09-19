---
rg: 2
id: binary-jacobson-balanced-center-fold-authenticates-two-rows
kind: claim
title: The balanced Jacobson center folds exactly, but does not inherit the degree-two source
artifacts:
  - research/binary-jacobson-balanced-center-fold-proof.md
distinct_from:
  binary-jacobson-balanced-target-redesign-contains-mixed-root: that computes the redesigned packet and proves its center carries the raw range off itself; this turns that orthogonality into an exact coisometry onto a negative moved-center cut.
  binary-jacobson-closing-root-folds-head-two-to-one: that folds two source sign sectors onto one raw range using the closing constant root; this folds one raw range and its moved-center image onto the negative center carrier of the mixed target packet.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for all four degree-two-to-degree-four covariance rows; this proves a carrier identity and two Q-labelled rows for the redesigned packet, but isolates the missing source-degree authentication.
---

**ESTABLISHED.**  Let `e=F_+`, and let

```text
c_T=I+QT E_11,
D_T=(x_12(Q),x_21(T),x_14(Q),x_41(T))
```

be the balanced target packet of
`binary-jacobson-balanced-target-redesign-contains-mixed-root`.  Put

```text
e'=c_T e c_T,       E=e+e',
q=E(1-c_T)/2,       V=(1-c_T)e/sqrt(2).                 (JCF1)
```

Then `e` and `e'` are orthogonal, `E` commutes with `c_T`, and `q` is a
projection in the negative `c_T` cut.  The literal occurrence `V` is an
exact coisometry from `e` onto `q`:

```text
V^*V=e,             VV^*=q.                             (JCF2)
```

Moreover the two Q-labelled generators preserve both carriers and satisfy
the exact covariance rows

```text
x_12(Q)V=V x_12(Q)|_e,
x_14(Q)V=V x_14(Q)|_e.                                  (JCF3)
```

Thus the moved-center carrier is not an open selection problem: it is
canonically and dimension-independently authenticated by `(JCF1)`.  Exactly
two rows remain for the redesigned packet,

```text
x_21(T) V = V C_2,       x_41(T) V = V C_4,             (JCF4)
```

for contractions on `e`.  The first T-root is the already audited
half-supported alternating polar; the second is a new opposite-coordinate
T-root.

Crucially, this is **not yet a PI bridge**.  The two source rows in `(JCF3)`
are `x_12(Q)|_e` and `x_14(Q)|_e`, not the established folded degree-two
rows `x_12(S^2)|_e` and `x_14(SQ)|_e`; nor does this fold produce the zero
second row of that tuple.  No identity here proves that the four compressed
source contractions have `s_4=0`.  Even if `(JCF4)` closed, the result could
be an ordinary `M_4`-to-`M_4` transport.

Therefore a useful continuation must solve **both** remaining typings:
control the two T-root leakages and identify a degree-two source algebra on
`e` for the same occurrence.  The center fold alone only removes the moved
center ambiguity.

The remaining errors have no hidden gauge.  For
`d in {x_21(T),x_41(T)}` and the literal source compression `C_d=ede`,

```text
dV-VC_d=(1-c_T)(1-e)de/sqrt(2).                          (JCF5)
```

For `d=x_21(T)`, the source support of the unprojected leakage `(1-e)de` is
exactly `e-p`, where `p=e(1+x_23(1))(1+x_23(Q))/4` is the first mixed-polar
support.  Thus the remaining covariance task is a concrete range-incidence
calculation for two named T-roots.  A separate source-degree calculation is
still required.

The underlying word data itself is now completely fenced.
`binary-jacobson-balanced-center-fold-data-is-finite-marked` proves that the
three roots defining the raw source signs together with all four generators
of `D_T` generate a finite group of order at most `2^12`, with the head mark
nontrivial.  Therefore no further manipulation of their uncompressed
conjugation table can supply the missing PI contradiction.  Any successful
use of `(JCF5)` must authenticate a genuinely representation-dependent
raw-range compression or adjoin an occurrence outside that finite envelope.

DERIVATION
binary-jacobson-balanced-center-fold-proof
