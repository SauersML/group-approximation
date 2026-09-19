---
rg: 2
id: non-hyperlinear-from-exact-quasi-regular-leak
kind: route
title: Refuting one exact quasi-regular configuration makes the codense HNN group non-hyperlinear
target: non-hyperlinear-group
requires:
  - no-exact-quasi-regular-leak
---

Let

```text
G_2 = < SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1 >
    = SL_2(Z[1/2]) *_(SL_2(Z)) ( SL_2(Z) x Z ),
```

the explicit finitely presented group of `(SZ1)` in
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`.  Suppose `G_2` were
hyperlinear: its canonical trace embeds `L(G_2)` into a tracial matrix
ultraproduct `M`, trace-preservingly.  Write `pi` for the restriction
of the embedding to `Gamma = SL_2(Z[1/2])` and `k = u_t`.

1. `Gamma` embeds in `G_2` (amalgam vertex group), so the canonical
   trace of `G_2` restricts on `pi(Gamma)` to the regular trace:
   `tau(pi(gamma)) = delta_e(gamma)`.
2. `k` is a unitary commuting EXACTLY with `pi(SL_2(Z))` — this is a
   defining relation of `G_2`, not an approximation.
3. For `gamma in Gamma`,
   `tau(k* pi(gamma) k pi(gamma)*) = tau_(G_2)(t^(-1) gamma t gamma^(-1))`,
   which is `1` iff `t^(-1) gamma t gamma^(-1) = e` in `G_2`.  By
   Britton's lemma / amalgam normal form, the centralizer of `t` in
   `G_2` is `SL_2(Z) x <t>`, whose intersection with `Gamma` is
   `SL_2(Z)`.  Hence

   ```text
   tau(k* pi(gamma) k pi(gamma)*) = 1_(SL_2(Z))(gamma),
   ```

   the exact quasi-regular profile `(EQL1)`.

So a hyperlinear `G_2` produces precisely the configuration that
`no-exact-quasi-regular-leak` forbids.  Contradiction: `G_2` is not
hyperlinear, and it is an explicit finitely presented group, which is
the goal.

**What this route does NOT need.**  It does not need the relative
commutant collapse `(RCC)` (`relative-commutant-collapse-for-sl2-pair`)
for arbitrary elements, nor flexible HS-stability of the base
(`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`'s corollary), nor
the identification of the two walls
(`hnn-route-is-relative-commutant-collapse`).  Those routes refute the
leak by first controlling ALL of `pi(SL_2(Z))' cap M`; this route asks
only that the single extreme, exactly-quasi-regular configuration be
impossible.  By `hecke-far-commutator-defect-formula` that
configuration is the `s = 0` extreme point of the leak spectrum with
tempered profile, so this is the weakest statement in the entire lane
that still delivers the goal.
