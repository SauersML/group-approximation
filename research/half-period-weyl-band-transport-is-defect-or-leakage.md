---
rg: 2
id: half-period-weyl-band-transport-is-defect-or-leakage
kind: claim
title: Half-period Weyl-band transport is root defect or wrong-sector leakage
distinct_from:
  same-reservoir-weyl-pair-has-fixed-depth-doubling-gap: that treats one global Weyl pair and a unitary conjugator; this treats distinct source and target packets, a rectangular partial transporter, and charges the part which misses the positive target band.
  polar-compression-turns-band-mismatch-into-first-exit: that converts projection mismatch into a partial transition after endpoint bands are supplied; this proves the phase obstruction obeyed by that partial transition when its source and target half-period commutators have opposite signs.
  exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss: that forces same-depth parahoric intertwiners to lose representation mass; this is a local two-root spectral dichotomy independent of congruence representation theory.
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `m>=1`, and let
`P,Q,R,S` be unitaries. Let `E` be a projection reducing `P,Q`, and suppose

```text
[P,Q^m]E=-E,              [P^m,Q]E=-E.                 (HPW1)
```

Put

```text
C_1=[R,S^m],              C_2=[R^m,S],                 (HPW2)
```

and suppose `C_1,C_2` are selfadjoint unitaries. Let `F` be any projection
such that

```text
C_1F=F,                   C_2F=F.                      (HPW3)
```

No commutation between `F` and the four root unitaries is assumed. For every
partial isometry `W` with initial projection `W^*W<=E`, set

```text
mu=||W||_2^2,
delta_P=||RW-WP||_2,      delta_Q=||SW-WQ||_2,
ell=||(1-F)W||_2^2.                                      (HPW4)
```

Then

```text
delta_P+m delta_Q+sqrt(ell)>=sqrt(mu),
m delta_P+delta_Q+sqrt(ell)>=sqrt(mu).                  (HPW5)
```

In particular, if the range of `W` lies in `F`, then

```text
delta_P+delta_Q>=2sqrt(mu)/(m+1),
delta_P^2+delta_Q^2>=2mu/(m+1)^2.                       (HPW6)
```

Thus a negative half-period source Weyl sector cannot be routed into a
positive half-period doubled sector by hiding the map in a rectangular
multiplicity space. Either one of the two root transports pays a fixed-depth
Hilbert--Schmidt defect, or a quantified part of the transported source lands
outside the required target spectral band.

For an exact primitive `d=2^N` Weyl source, take `m=d/2`; its primitive
central-character projection is precisely the `-1` spectral projection of
the half-period commutator. For a literal doubled target the corresponding
half-period commutators are `+1`. Hence `(HPW5)` is the desired local
spectral-band matching/leakage dichotomy. It does not construct the six
arithmetic chart bands: the remaining decoder must show that their wrong-sign
mass is one of the already budgeted conductor first exits.
