---
rg: 2
id: lin-canonical-dilation-twirls-unprotected-left-carriers
kind: claim
title: Lin's canonical dilation twirls every unprotected left carrier
distinct_from:
  lin-state-dependent-gh-preserves-the-commutant: that records the positive exact intertwining of the whole opposite algebra; this computes the complementary left-side operation and gives an exact witness that no analogous preservation follows for a context carrier in the original algebra.
  lin-one-state-pauli-standardization-stops-before-groupification: that is the composite scope conclusion; this is the exact one-step Reynolds formula responsible for the failure of common-carrier transport.
---

Let `G` be finite, let `A subset B(H)` be a finite tracial von Neumann
algebra, and let `phi:G->U(A)`.  The isometry used in the proof of Lin's
Theorem 5.1 is

```text
V xi=|G|^(-1/2) direct_sum_(g in G) phi(g^(-1))xi.       (LCD1)
```

For every `a in A`, it satisfies the exact compression formula

```text
V^*(a tensor I)V
 = |G|^(-1) sum_g phi(g^(-1))^* a phi(g^(-1)).           (LCD2)
```

For every projection `p in A`, its failure to carry `p` through the
dilation is exactly

```text
||(p tensor I)V-Vp||_(2,rho)^2
 = |G|^(-1) sum_g ||[p,phi(g^(-1))]||_(2,rho)^2.         (LCD3)
```

Here the column norm is induced by the same density `rho` as Lin's
state-dependent norm.  Thus the construction transports a left carrier
only when that carrier commutes with the packet (modulo the null space of
the state seminorm).  Lin's spectral layer from Theorem 4.1 is a projection
in `A`, not in `A'`, and that theorem supplies no commutator estimate of the
form on the right of `(LCD3)`.

This is a sharp logical obstruction, not just absence of a stated estimate.
Take `A=M_2`, `G=Z_2`, `phi(s)=Z`, and `a=X`, with the normalized trace and
the Pauli matrices `X,Z`.  Then `phi` is already an exact representation and
Lin's displayed isometry satisfies all conclusions of Theorem 5.1 with
zero error, while

```text
V^*(X tensor I)V=(X+ZXZ)/2=0.                          (LCD4)
```

Likewise, for `p=(I+X)/2`, `(LCD3)` is nonzero.  Hence even at zero defect,
the theorem's `A'`-linearity does not imply preservation of a second left
packet or of a left spectral carrier.

Consequently the theorem cannot be iterated across unrelated context
packets merely by amplifying the next packet as `a tensor I`: after the
first step, compression of that amplification is the Reynolds twirl
`(LCD2)`.  The old exact auxiliary regular packet is protected by a later
isometry only if one accepts this twirling of the new left payload.  A
simultaneous application to a direct product instead builds cross-context
commutation into the exact packet, while a free product of the context
groups is generally infinite and lies outside Theorem 5.1.  Additional
cross-context covariance or a separately authenticated common carrier is
therefore still necessary.
