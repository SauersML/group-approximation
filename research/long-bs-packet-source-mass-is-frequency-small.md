---
rg: 2
id: long-bs-packet-source-mass-is-frequency-small
kind: claim
title: Long BS packet source mass is bounded by inverse cutoff plus cube-root frequency energy
distinct_from:
  cyclic-frequency-ledger-pays-excess-source-rank: that packetwise Ky Fan theorem charges source rank beyond packet multiplicity; this global spectral-counting theorem bounds all source mass on the moving long-packet tail, including the within-capacity direction and fractional cross-packet localization.
  bs14-source-mode-reset-has-exact-frequency-cost: that computes the exact reset cost of a selected scalar mode; this requires no mode selection and works for a positive contraction that mixes all packets.
  bs14-native-cells-cross-every-length-cutoff: that is the surviving cross-threshold X obstruction; this closes only the long source-mass ledger and explicitly does not split the exact endpoint.
---

**ESTABLISHED.**

The packetwise excess-rank estimate leaves a one-mode-per-copy capacity
sector.  Summing that residual packet by packet would require moving packet
localization and integer multiplicity bookkeeping.  For the purpose of
discarding the entire long-packet tail, neither is necessary.

## Theorem

Let `(R,S)` be an exact finite-dimensional `BS(1,4)` core, decomposed into
the usual fourth-power orbit packets.  For an integer cutoff `M>=1`, let
`P_L` be the reducing projection onto the sum of all packets whose orbit
length is at least `M`.  Let

```text
W:E -> H
```

be an arbitrary isometry.  It need not respect the packet decomposition.
Put `d=dim H` and

```text
mu_L = d^(-1) ||P_L W||_F^2,
e_L  = d^(-1) ||(R-I)P_L W||_F^2.
```

For `0<e_L<=1`,

```text
mu_L <= M^(-1) + 2 e_L^(1/3).                    (1)
```

Consequently the normalized Frobenius cost of deleting the entire long
component of the source is bounded by

```text
d^(-1/2)||P_LW||_F
    <= M^(-1/2) + sqrt(2)e_L^(1/6).              (2)
```

The estimates are uniform in the moving packet lengths, return phases,
packet multiplicities, and off-packet mixing of `W`.

## Proof

Diagonalize the return unitary in each orbit packet.  The restriction of
`R` is then an orthogonal sum of scalar rotated root cycles: for every
scalar cycle of length `m`, its spectrum is a rotated copy of the `m`th
roots of unity.  Multiplicity merely repeats these scalar cycles.

Set

```text
A=P_L|R-I|^2P_L.
```

For `0<t<=1`, the portion of the unit circle satisfying

```text
|z-1|^2<t
```

is an arc of normalized length at most `sqrt(t)`.  Therefore a rotated
`m`-gon has at most

```text
1 + m sqrt(t)
```

eigenvalues in that arc.  If the long tail is a sum of scalar cycles with
lengths `m_a>=M` and repetitions `n_a`, its low-frequency spectral counting
function satisfies

```text
N_L(t)
 <= sum_a n_a + sqrt(t) sum_a n_a m_a
 <= d_L/M + sqrt(t)d_L
 <= d/M + sqrt(t)d,                               (3)
```

where `d_L=rank P_L`.

Now let

```text
Q=P_LWW^*P_L.
```

This is merely a positive contraction; it need not be a projection and it
need not commute with the packet projections.  Let `E_<` and `E_>=` be the
spectral projections of `A` for `[0,t)` and `[t,infinity)`.  Then

```text
Tr(QE_<) <= rank E_< = N_L(t),
Tr(QA)   >= t Tr(QE_>=).
```

Hence

```text
Tr Q <= N_L(t) + t^(-1)Tr(QA).                   (4)
```

Since `P_L` commutes with `R`,

```text
Tr(QA)=||(R-I)P_LW||_F^2.
```

Divide (4) by `d` and use (3):

```text
mu_L <= M^(-1) + sqrt(t) + e_L/t.                (5)
```

Choosing `t=e_L^(2/3)` proves (1).  Finally

```text
sqrt(a+b) <= sqrt(a)+sqrt(b)
```

applied to (1) proves (2).  QED.

The same proof works for any contraction `W`, since it uses only
`0<=WW^*<=I`.

## Consequence for the two-carrier source ledger

After `two-source-gram-alignment-pays-frequency-not-mode-purity` aligns the
two residual polar sources, their inversion block defects bound `e_L`.
Equations (1)--(2) then delete the **entire** common source on all packets of
length at least `M` at cost

```text
O(M^(-1/2) + e_L^(1/6)).
```

Thus the last within-capacity direction, fractional packet weights, and
moving packet localization are no longer separate long-tail obstacles.

## What this does not prove

This estimate concerns the source carrier inside the exact core.  It does
not justify repairing the short core independently of the long core.  The
exact native cells in `bs14-native-cells-cross-every-length-cutoff` have
order-one `X` coupling between a length-one packet and packets longer than
every prescribed cutoff.  Cutting `X` at the core threshold can therefore
move an exact endpoint by order one.

Moreover bounded orbit length alone does not make the unpreconditioned core
types finite: the return monodromy still has continuous unitary data.  The
finite-level Iwahori quotient theorem becomes available only after the
preconditioner is authenticated globally.  Consequently the remaining gate
is not long-source multiplicity.  It is global congruence-atom
authentication together with reconstruction of the cross-threshold `X`
coupling.
