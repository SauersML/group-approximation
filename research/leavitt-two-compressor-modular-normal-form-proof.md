---
rg: 2
id: leavitt-two-compressor-modular-normal-form-proof
kind: route
title: Read the compressor prefix tables and apply ping-pong
target: leavitt-two-compressor-core-has-modular-normal-form
requires:
  - leavitt-two-compressor-diagonal-kernel-is-locally-finite
---

Identify the first two rank-five Cantor copies with the cylinders `[0]` and
`[1]`.  The two active compressor maps have prefix tables

```text
t=tau_0:  0->00,     10->01,     11->1,
tau_1:    0->01,     10->1,      11->00.
```

Thus `r=tau_1 tau_0^(-1)` cycles

```text
[00] -> [01] -> [1] -> [00].                           (1)
```

Put `s=r t^(-1)=tau_1 tau_0^(-2)`.  One refinement gives

```text
[000] <-> [01],                 [001] <-> [1],         (2)
```

so `s^2=1`.  With `X_s=[00]` and `X_r=[01] union [1]`, equation `(2)` swaps
`X_s,X_r`, while `r,r^2` send `X_s` into `[01]` and `[1]`, respectively.
Ping-pong proves `<s,r>=C_2*C_3`, and `t=sr`.

The original diagonal group contains the full locally constant `H`-valued
lamp groups supported on `[00]` and `[01]`.  Conjugating the first by `r` and
`r^2` supplies the full groups supported on `[01]` and `[1]`.  The three
disjoint cylinder groups therefore generate `C_lc(X,H)`, which is exactly
the diagonal normal closure.

Prefix substitutions normalize this lamp group.  Lamps fix every boundary
path and act only in the `H` fiber, while a nonidentity reduced word in
`C_2*C_3` moves a path by the same ping-pong argument.  Their intersection is
trivial, giving the unique semidirect normal form in `(MNF1)`.  The passive
two rank-five blocks add no kernel: their prefix action is obtained from the
active one by the involution conjugating each compressor to its inverse.
