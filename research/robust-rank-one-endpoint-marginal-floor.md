---
rg: 2
id: robust-rank-one-endpoint-marginal-floor
kind: claim
title: Rank-one contextual failure retains the whole carrier mass up to endpoint drift
distinct_from:
  rank-one-no-signaling-pairing-floor: that assumes exactly shared probability marginals on a unit-mass fiber; this is the unnormalized robust form needed after approximate packet transport.
  child-carrier-relative-pauli-holonomy: that must manufacture the endpoint transports from group words and charge their failure to relators; this supplies its sharp measure-theoretic endpoint once those transports exist.
---

Let `nu_00,nu_01,nu_11` be nonnegative measures of the same total mass `q`
on `{0,1}^2`.  Write

```text
a_00=nu_00(X=1),  a_01=nu_01(X=1),
b_01=nu_01(Y=1),  b_11=nu_11(Y=1),
Delta_X=|a_00-a_01|, Delta_Y=|b_01-b_11|.
```

Define the three failure masses

```text
p_00=q-nu_00(1,1),
p_01=  nu_01(1,1),
p_11=q-nu_11(1,1).
```

Then

```text
p_00+p_01+p_11 >= q-Delta_X-Delta_Y.                 (RRF1)
```

In particular, exact endpoint sharing recovers a failure mass of at least the
entire carrier mass `q`, without normalizing by `q` and without a small-mass
loss.

If the endpoint marginals arise from projections and unitary transports in a
normalized matrix trace, then

```text
Delta_X <= ||U P U^*-P'||_2,
Delta_Y <= ||V Q V^*-Q'||_2.                         (RRF2)
```

Consequently a group-word realization whose two endpoint drifts have squared
energy at most `E_end` obeys

```text
p_00+p_01+p_11 >= q-sqrt(2 E_end).                   (RRF3)
```

This is the quantitative form needed by the relative rank-one route: if the
three failures are also bounded above by `C sqrt(E_local)` (or their total
mass by `C E_local`), a fixed positive child carrier forces a dimension-free
local energy floor.
