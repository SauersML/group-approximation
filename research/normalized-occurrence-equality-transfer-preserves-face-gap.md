---
rg: 2
id: normalized-occurrence-equality-transfer-preserves-face-gap
kind: claim
title: Normalized equality-cloud row squares preserve the whole-face channel gap
distinct_from:
  averaged-pinching-channels-are-row-square-lipschitz: that is the abstract channel perturbation estimate; this matches the face and cloud weights and derives its row-square hypothesis from equality edges.
  row-square-equality-variance-transfers-averaged-pinching-gap: that signs the weighted cloud averages and obtains a two-band spectral statement from an assumed variance bound; this derives that bound from normalized expander edges and transfers the explicit whole-face gap while retaining the contractions.
  repeated-ldpc-shared-face-marginal-synchronization: that asks for literal exact shared marginals; this transfers only the finite-time transverse channel gap to shared averaged contractions.
  parity-exact-shared-contractions-have-intrinsic-cp-gap: that starts with one literally shared exact tuple; this starts with separate exact local face copies.
---

ESTABLISHED CONDITIONAL TRANSFER.  Give each bounded face `c` a weight
`mu_c`, with `sum_c mu_c=1`, and put

```text
 w_(c,i)=mu_c/|c|,       q_0=max_c |c|.                 (NOET1)
```

Let `Q_(c,i)` be exact local face reflections on one finite tracial algebra,
let `Phi_c` be the corresponding whole-face pinching, and suppose

```text
 H_F=sum_c mu_c(I-Phi_c)
     >=gamma(I-E_K)                                     (NOET2)
```

as quadratic forms, where `E_K` projects onto the common commutant.  Define
the normalized local occurrence channel

```text
 A_loc(T)=sum_(c,i) w_(c,i)(T+Q_(c,i)TQ_(c,i))/2.       (NOET3)
```

Then

```text
 ||A_loc|_(K^perp)||_(2->2)<=1-delta_0,
 delta_0=gamma/q_0.                                    (NOET4)
```

For logical coordinate `i`, let its occurrence cloud have stationary
measure `lambda_(i,v)` and Markov gap at least `lambda_eq>0`.  Choose the
regular cloud/face weights so the occurrence law disintegrates as
`w_(i,v)=nu_i lambda_(i,v)`, where `sum_i nu_i=1`, and set

```text
 S_i=sum_v lambda_(i,v)Q_(i,v),
 A_sh(T)=sum_i nu_i(T+S_iTS_i)/2.                       (NOET5)
```

Thus each `S_i` is a selfadjoint contraction, literally shared across its
cloud.  If

```text
 B_eq=sum_i nu_i E_((u,v) edge i)
              (Q_(i,u)-Q_(i,v))^2,
 ||B_eq||_infinity<=b,                                  (NOET6)
```

then for every integer `k>=1`,

```text
 ||(I-E_K)A_sh^k(I-E_K)||_(2->2)
 <=(1-delta_0)^k+k sqrt(b/lambda_eq).                   (NOET7)
```

All constants are independent of the number of faces and occurrences, code
length, matrix dimension, and character multiplicity.  In particular,
choosing one fixed `k=k(gamma,q_0)` and then
`b<b_0(gamma,q_0,lambda_eq)` leaves a strict transverse contraction.

For the balanced repeated overlay, the equality layer has fixed normalized
density.  Hence on a common reducing retained block where the raw balanced
residual square function is at most `beta I`, `(NOET6)` holds with
`b<=C_bal beta`; there is no maximum-over-occurrences or sparse-corner loss.
This closes the **averaged-channel** equality interface after exact local
face copies have been produced on that block.  It does not produce those
exact local copies: preserving the common row-square bound during local
face exactification is the remaining upstream gate.  Nor does `(NOET7)` by
itself make the contractions `(S_i)` satisfy the parity products exactly.
