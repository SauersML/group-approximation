---
rg: 2
id: common-source-game-state-proof
kind: route
title: Pull all context measurements back to the common source
target: common-source-partial-isometries-decode-one-game-state
requires: []
---

On `Q C^d`, set

```text
tilde P_(c,a)=S_c^*P_(c,a)S_c,
tilde N_(x,+)=Q(I+B_x)Q/2,
tilde N_(x,-)=Q(I-B_x)Q/2.
```

The first family is a POVM because its effects are positive and sum to
`S_c^*S_c=Q`.  The second family is a binary POVM because compression
preserves positivity and its two effects sum to `Q`.  No range-reduction or
source-invariance hypothesis is needed.  Use the maximally entangled state
on `Q C^d` and its conjugate.

The forbidden probability is `||F_cS_c||_2^2/tau(Q)`.  Put
`tilde A=S_c^*A_(c,x)S_c` and `tilde B=QB_xQ`.  Traciality and
`S_c^*S_c=Q` give

```text
||A_(c,x)S_c-S_cB_x||_2^2
 =2tau(Q)-2 Re tau(S_c^*A_(c,x)S_cB_x)
 =2tau(Q)-2 Re tau(tilde A tilde B).                  (CSG1)
```

The last expression is four times the disagreement probability multiplied
by `tau(Q)`.  Averaging gives loss at most `E_Q/tau(Q)`.  The game gap forces
this to be at least `1-theta`.
