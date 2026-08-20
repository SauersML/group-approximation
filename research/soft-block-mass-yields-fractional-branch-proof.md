---
rg: 2
id: soft-block-mass-yields-fractional-branch-proof
kind: route
title: Spectral truncation, polar decomposition and a bounded inverse
target: soft-block-mass-yields-fractional-branch
requires: []
---

`E_t <= P`.  The support projection of `|X|` equals the support of `X^*X` and
`X^*X = P W^* Q W P <= P`, so `supp|X| <= P` and hence `E_t <= P`.

**(SBM1).**  Split the second moment across the threshold:

```text
||X||_2^2 = tau(|X|^2 E_t) + tau(|X|^2 (1-E_t)).
```

Since `||X||_op <= ||W||_op <= 1`, the first term is at most `tau(E_t)`.  The
operator `|X|(1-E_t)` has norm at most `t` and support under `P-E_t`, so the
second term is at most `t^2 (x - tau(E_t))`.  Therefore

```text
||X||_2^2 <= (1-t^2) tau(E_t) + t^2 x,
```

which is `(SBM1)`.

**(SBM2).**  `|X|^2 >= t^2 E_t`, so `||X||_2^2 = tau(|X|^2) >= t^2 tau(E_t)`.

**(SBM3).**  For the polar decomposition `X=V|X|`, `V` is a partial isometry
with `V^*V = supp|X|` and `VV^* = supp|X^*| <= Q`, the last inequality because
`X = QX` forces the range of `X` into the range of `Q`.  Since `E_t <= supp|X|`,
`T=VE_t` satisfies `T^*T = E_t V^*V E_t = E_t` and `TT^* <= VV^* <= Q`.  Hence
`(1-Q)T = 0`.

**(SBM4).**  On `E_t` the operator `|X|` is bounded below by `t`, so
`|X|^(-1)E_t` is well defined with operator norm at most `1/t`, and
`V E_t = X |X|^(-1) E_t`.  Therefore

```text
T_e^* T_f = E_t |X_e|^(-1) X_e^* X_f |X_f|^(-1) E_t,
```

and submultiplicativity of the normalized Hilbert--Schmidt norm against
operator norms on both sides gives the bound `t^(-2)||X_e^*X_f||_2`.

Every step is valid in an arbitrary finite tracial von Neumann algebra and uses
no dimension.
