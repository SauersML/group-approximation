---
rg: 2
id: non-hyperlinear-from-sl3-relative-commutant-collapse
kind: route
title: The property (T) pair reaches the goal through the same reduction once its collapse holds
target: non-hyperlinear-group
requires:
  - hnn-route-is-relative-commutant-collapse
  - sl3-pair-relative-commutant-route
---

Instantiate `hnn-route-is-relative-commutant-collapse` at the
higher-rank pair: `A = SL_3(Z[1/2])`, `C = SL_3(Z)`,
`a_1 = h = diag(2, 1, 1/2)`, and

```text
G_3 = < SL_3(Z[1/2]), t | [t, SL_3(Z)] = 1 >,
```

a finitely presented group (both `A` and the commutation relations over
a finite generating set of `C` are finitely presentable; `C` is
finitely generated, so `[t, C] = 1` is finitely many relations).
Co-density and properness of the pair are recorded in
`sl3-pair-relative-commutant-route` (congruence subgroup property plus
strong approximation; `h notin C`).  The reduction then says: `G_3` is
not hyperlinear as soon as

```text
pi(SL_3(Z))' cap M = pi(SL_3(Z[1/2]))' cap M               (RC3)
```

for every tracial matrix ultraproduct `M` and every trace-preserving
regular-trace representation `pi` of `SL_3(Z[1/2])` -- which is exactly
the statement of `sl3-pair-relative-commutant-route`.

This wires the (T)-side pair to the goal on its own edge.  The `SL_2`
edge (`non-hyperlinear-from-relative-commutant-collapse`) stays, but
the strategic fork recorded in `no-exact-quasi-regular-leak` points
here: `SL_3(Z[1/2])` has property (T), hence Serre's (FA), so `G_3`'s
enemy admits no amalgam construction surface, the completion
`PSL_3(Q_2)` has property (T), and the Hecke contraction machinery
(`hecke-averaging-realizes-commutant-expectation`) applies on this edge
and not on the `SL_2` one.
