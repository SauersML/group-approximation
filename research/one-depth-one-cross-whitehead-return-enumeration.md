---
rg: 2
id: one-depth-one-cross-whitehead-return-enumeration
kind: route
title: Enumerate one depth-one root or opposite Whitehead against the full signed Hecke signature
target: one-depth-one-occurrence-does-not-return-cross-whitehead
requires:
  - individual-cross-whiteheads-miss-native-hecke-target
  - two-depth-one-leavitt-roots-return-only-constantly
---

Represent a Leavitt monomial `s_mu t_nu` by the prefix replacement pair
`(mu,nu)`.  Multiplication uses prefix cancellation, and the refinement

```text
(mu,nu)=(mu0,nu0)+(mu1,nu1)                           (DORP1)
```

gives a faithful finite normal form for every coefficient reached by the
bounded calculation.

Close the ten constant directed transvections of `L_0` by breadth first
search while carrying their character bit.  This gives exactly `8192`
matrices, and every repeated matrix is reached with the same bit.  For a
candidate relative word `g`, test all ten equations

```text
g^(-1)h_jg in L_0,
lambda_0(g^(-1)h_jg)=lambda_0(h_j).                   (DORP2)
```

For the source target use `g=LK_i`; for the native target use
`g=J_1^(-1)LK_i`.  The exact depth-two coefficients in `J_1` are retained,
although the searched occurrence `L` is restricted to `(DOR2)--(DOR3)`.

The deterministic artifact asserts the menu size `3024`, the total test
count `12096`, zero native-target hits, and two source-target spellings for
each branch.  It additionally evaluates both spellings as the same matrix
`K_i` and asserts that their product with `K_i` is the identity.  Thus the
reported source hits are precisely `(DOR5)--(DOR6)`, completing the scoped
enumeration proof.
