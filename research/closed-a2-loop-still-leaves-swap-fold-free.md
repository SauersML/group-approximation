---
rg: 2
id: closed-a2-loop-still-leaves-swap-fold-free
kind: claim
title: Even the closed two-return A2 loop leaves the swap fold free
invalidates:
  - hnn-outlier-exclusion-from-closed-a2-loop
artifacts:
  - research/closed-a2-loop-fold-countermodel-proof.md
distinct_from:
  one-mixed-a2-word-does-not-control-fold-square: that M4 packet satisfies only the first Weyl return to the highest root; this finite congruence packet satisfies both competing Weyl returns and identifies them with the root commutator.
  unbalanced-torus-and-swap-commutation-do-not-control-fold-square: that M2 packet keeps the two rank-one branches separate; this closes the first literal rank-two loop between them.
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that consumes a full fixed presentation of the arithmetic actor; this packet deliberately twists the two negative simple-root and Weyl slots by a sheet sign and therefore omits further lattice relations which prohibit that sign character.
---

Work at `p=2`.  Use the notation of
`one-mixed-a2-word-does-not-control-fold-square` and add the competing
Weyl return

```text
W_23^* E_12 W_23=[E_12,E_23].                          (CAL1)
```

Thus both paths

```text
W_12 E_23 W_12^*,       W_23^* E_12 W_23
```

are required to agree with the highest-root commutator.  For every odd
`m>=3` there is an exact finite-dimensional packet satisfying `(CAL1)`, the
first mixed return, both rank-one doubling/Weyl packages, every displayed
swap commutator, and the unbalanced torus word:

```text
S^2=1,                 [S, every displayed coefficient]=0,
A_12=E_12^2,           W_12=E_12 B_21 E_12,
A_23=E_23^2,           W_23=E_23 B_32 E_23,

R_tor=1,
W_12 E_23 W_12^*=[E_12,E_23]=W_23^*E_12W_23.          (CAL2)
```

Nevertheless, with `F=HSH^*S`,

```text
Re tr(F^2)=-1/2,
||F^2-1||_2^2=3,
tr(QPQ-(QPQ)^2)=3/32.                                  (CAL3)
```

Hence closing the two shortest `A_2` returns still does not yield a
dimension-free fold-square estimate.  The obstruction is no longer an
independent Pauli repair: it is a literal two-sheet sign on the two negative
simple-root and Weyl slots, tensored with an exact odd-congruence
representation of the complete rank-two packet.

This does not refute the full HNN residual.  The packet is not a full
representation of `SL_3(Z)`, and it does not satisfy the entire
amalgamated-free moment law.  It precisely invalidates the shortcut which
rounds the Haar letter to its balanced involution and then tries to close
the outlier using only `R_tor` and the closed two-return loop.  At least one
further lattice identity detecting the negative-root sheet sign, or a
genuinely matricial use of the full free law, remains indispensable.

DERIVATION
closed-a2-loop-fold-countermodel-proof
