---
rg: 2
id: stw22-use-the-fixed-projection-orbit-bundle-proof
kind: route
title: Lift a continuous support field through the fixed projection orbit and attach the square root
target: stw22-lwcl-on-fixed-support-strata
requires: []
artifacts:
  - research/artifacts/stw22-lwcl-fixed-support-stratum-audit-2026-08-30.md
---

Fix `p_0=p(z_0)`.  The fixed-trace projection orbit

```text
P_r(R)={q in R:q=q^*=q^2, tau(q)=r}
```

with its strong, equivalently `2`-norm, topology is locally lifted by the
partial-isometry bundle.  Concretely, after shrinking around `p_0`, a
`2`-norm-continuous projection field `p(z)` has a `2`-norm-continuous field
`u(z)` of partial isometries satisfying

```text
u(z)^*u(z)=p_0,       u(z)u(z)^*=p(z).                   (FSP1)
```

This follows from the bundle results of Andruchow--Varela,
[*States with equivalent supports*](https://jot.theta.ro/jot/archive/2005-053-001/2005-053-001-002.pdf).
In their notation, Theorem 2.10 gives a continuous section of the modular
state fibration for the hyperfinite factor, and Theorem 7.2 sends a
projection `q` in the fixed orbit continuously (strong topology to norm
topology) to the normalized corner trace `tau_q`.  Composing these maps and
retaining the partial-isometry coordinate gives a continuous `u(q)` with
initial projection `p_0` and final projection `q`.  Restriction along
`q=p(z)` gives `(FSP1)`.  This is a fixed Murray--von Neumann equivalence
class statement; it does not connect different trace strata.

Choose a projection `q_0<=e` with `tau(q_0)=r` and a partial isometry
`v_0` satisfying

```text
v_0^*v_0=p_0,       v_0v_0^*=q_0.
```

Define

```text
w(z)=v_0 u(z)^* a(z)^(1/2).                              (FSP2)
```

Since `u(z)u(z)^*=p(z)=supp(a(z))`,

```text
w(z)^*w(z)
 =a(z)^(1/2)u(z)p_0u(z)^*a(z)^(1/2)
 =a(z),
```

and the range support of `w(z)` is below `q_0<=e`.
The Powers--Stoermer inequality makes
`z |-> a(z)^(1/2)` continuous in `2`-norm, while multiplication by a
uniformly bounded strongly continuous partial-isometry field preserves
`2`-norm continuity.  Hence `(FSP2)` proves `(FSL)`.

The proof uses `(FSS)` twice: continuity places the support field in the
strong projection orbit topology, and constancy of `tau(p(z))` keeps it in
one orbit.  If tiny eigenvalues create new support of varying trace, the
positive field may remain `2`-norm continuous while its support leaves this
bundle.  Fixed-support cross-section theorems then no longer apply.
