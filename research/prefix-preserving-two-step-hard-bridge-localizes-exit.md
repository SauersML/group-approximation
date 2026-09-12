---
rg: 2
id: prefix-preserving-two-step-hard-bridge-localizes-exit
kind: claim
title: A prefix-preserving bridge followed by a site swap localizes a global hard exit
distinct_from:
  projected-hard-sign-bridge-selects-joint-exit: that transports an analytically compressed exit into one target hard-sign space; this adds a second site-local swap and proves membership in the full first-hit prefix sector.
  thompson-site-pulses-localize-hard-exits: that assumes the source hard sign already belongs to the current doubled site packet; this permits a global packet hard word and isolates the exact bridge covariance and prefix-commutation conditions.
  packet-hard-transport-preserves-pulse-prefix: that asks the original E5 hard transporter itself to preserve an overlapping polynomial pulse prefix; this uses a separate bridge into independent site pulses.
---

Let `B_0,...,B_n`, `a_n`, and `s_n` be self-adjoint involutions with

```text
[B_j,B_k]=1,
[s_n,B_k]=1                    (k<n),
B_n s_n=s_n a_n.                                      (PPB1)
```

Put

```text
C_n=product_(k<n)(I+B_k)/2,
X_n=C_n(I-B_n)/2.                                     (PPB2)
```

Let `A_n` be any self-adjoint involution, `P_n` a projection satisfying

```text
P_n<=C_n,                  A_nP_n=-P_n,                (PPB3)
```

and `u_n` a unitary with

```text
[u_n,B_k]=1                    (k<n),
a_nu_n=u_nA_n.                                         (PPB4)
```

Then the two-step transporter `v_n=s_nu_n` sends the entire analytically
compressed global exit into the site first-hit sector:

```text
v_nP_nv_n^*<=X_n.                                     (PPB5)
```

For the approximate statement first exactify the finite pulse table, so the
`B_k` remain exactly commuting involutions and `(PPB2)--(PPB3)` are literal
projection relations.  Allow the cross commutator and covariance equations in
`(PPB1),(PPB4)` to have error.  Then

```text
||(I-X_n)s_nu_nP_n||_2
 <= (1/2)sum_(k<n)(||[B_k,s_n]||_2+||[B_k,u_n]||_2)
    +(1/2)||B_ns_n-s_na_n||_2
    +(1/2)||a_nu_n-u_nA_n||_2.                         (PPB6)
```

Thus an independent Thompson pulse reservoir can receive a global Fanizza
hard exit without identifying the two hard words in the abstract group.  The
only new group-theoretic obligation is a family of bridge unitaries `u_n`
whose covariance and off-diagonal pulse commutation have bounded-orbit,
polynomial-area presentations and which extend the exact infinite witness.
