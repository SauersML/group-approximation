---
rg: 2
id: gauge-covariant-site-bridge-proof
kind: route
title: Match balanced involution eigenspaces on one fresh site at a time
target: gauge-covariant-hard-shares-admit-site-bridges
requires:
  - gauge-doubling-gives-selector-flip-symmetries
---

Gauge-orbit covariantization supplies a unitary `g_n` with

```text
g_n pi(A_n) g_n^*=pi(JA_n)=-pi(A_n).
```

Therefore `g_n` bijects the two eigenspaces of `pi(A_n)`.  After tensoring
with the two-qubit `n`th pulse site, `pi(A_n) tensor I_4` and
`I tensor a_n` have the same `+1` and `-1` multiplicities: each is two times
the original representation dimension in the finite case, and both are the
same infinite cardinal after the allowed amplification.  The spectral theorem
therefore gives a unitary `u_n` conjugating the first involution to the second,
which is `(GCS3)`.

Choose `u_n` inside the operators on the original factor and the `n`th pulse
factor.  Every `B_k`, `k!=n`, acts only on the `k`th pulse factor, proving
`(GCS4)`.  No relation among distinct `u_n` is required, so the fact that they
share the original factor causes no conflict.  The local tensor swap proves
`s_na_ns_n=B_n`, and distinct pulse factors commute.  These choices satisfy
all exact relations simultaneously and keep `J=-I`.
