---
rg: 2
id: order-seven-anchor-stops-at-whitehead-compression-leakage
kind: claim
title: The order-seven anchor reduces native Hecke coercivity to Whitehead compression leakage
invalidates:
  - order-seven-alone-authenticates-native-hecke
artifacts:
  - research/order-seven-compression-telescope-proof.md
distinct_from:
  native-whitehead-hecke-head-has-order-seven-anchor: that proves exact odd parity and reservoir-gauge coercivity on an invariant finite packet; this quantifies the error caused by compressing that relation to the nonreducing Hecke source.
  native-whitehead-corner-collapses-hecke-flags: that computes exact fixed reducing corners and shows they collapse the Hecke distinction; this gives the robust inequality and the exact matrix-only leakage estimate still needed.
  mark-fixed-relative-words-do-not-coerce-native-hecke-kernel: that treats relative words whose mark commutator is identically zero and which retain a common spectator gauge; the order-seven word genuinely removes that gauge once compression leakage is controlled.
---

**ESTABLISHED ORDER-SEVEN COMPRESSION BOUNDARY.**  Let `J` be one native
Whitehead, let `v` be its corresponding Hecke head, and put `T=Jv`.  Thus
`T^7=1` in the exact packet.  For every projection `E`,

```text
||(ETE)^7-E||_2
 <= ||E(T^7-1)E||_2+6||(1-E)TE||_2.                  (OSC1)
```

Indeed each of the six internal multiplications omitted by compression can
cross the boundary only through `(1-E)TE`.

Suppose finite-packet exactification identifies `ETE`, up to normalized-HS
error `zeta`, with the three-corner label operator `M` tensored with a
reservoir involution `D`, where `M^7=1`.  Since `D^2=1` and `7` is odd,

```text
(M tensor D)^7=1 tensor D.
```

The power telescope and `(OSC1)` give

```text
||D-1||_2
 <= 7 zeta+||E(T^7-1)E||_2+6||(1-E)TE||_2.           (OSC2)
```

Thus the new order-seven identity really eliminates the spectator gauge;
it is not another parity fence.  But it does so only after controlling one
new positive operator, the Whitehead return leakage.  Use the actual
order-seven heads

```text
v_1=u_1,                     v_2=u_2A_1,
T_i=J_iv_i.
```

For the two rows, pull their return leakage back to the common source and
put

```text
L_n=sum_(i=1)^2
 Q_n v_(i,n)^*J_(i,n)(1-Q_n)J_(i,n)v_(i,n)Q_n.        (OSC3)
```

A necessary first-exit finite-coordinate input, parallel to `(MFK6)`, is

```text
tau_n(Q_n 1_((C delta_n^(2alpha)),infinity)(L_n))
 <= C delta_n^alpha.                                  (OSC4)
```

On the resulting low spectral source cut `E_n<=Q_n`, both terms
`||(1-Q_n)T_(i,n)E_n||_2` are `O(delta_n^alpha)`.  This is not the boundary
appearing in `(OSC2)`, which is `||(1-E_n)T_(i,n)E_n||_2`.
`order-seven-first-exit-is-not-seven-step-leakage` gives an exact
seven-dimensional counterexample to the omitted inference.  One must
additionally control the exits from the moving cut at all seven stages, or
directly control the full `E_n` boundary.

Neither `T^7=1` nor native involutivity proves `(OSC4)`.  The order-seven
relator is exact in the canonical regular representation, while the fixed
Hecke source is not reduced by the literal Whiteheads and has positive
leakage.  The largest fixed common reducing corner is the one on which the
two Hecke flags collapse.  Consequently an inequality charging `(OSC3)`
only to dimension-free tracial word defects is impossible; `(OSC4)` must be
a genuinely finite-coordinate no-microstate theorem.

The affirmative frontier has nevertheless narrowed: occurrence parity is
closed by the order-seven anchor.  The remaining step is the typed moving
return in `growing-multicut-el20-order-seven-inheritance`.  The first-exit
tail estimate `(OSC4)` may be part of such a construction, but is not
equivalent to the full compression boundary.

DERIVATION
order-seven-compression-boundary-proof
