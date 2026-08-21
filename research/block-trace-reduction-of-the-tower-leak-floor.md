---
rg: 2
id: block-trace-reduction-of-the-tower-leak-floor
kind: claim
title: The joint tower leak floor reduces to a quadratic form in block-trace coordinates
distinct_from:
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that confines the enemy to the tower and hosts the experimental record; this is the analytic reduction of the per-instance floor to an explicit finite inequality, proved below.
  hecke-averaging-realizes-commutant-expectation: that contracts averaged conjugates onto the commutant expectation with a (T) rate; this controls a SINGLE compressed conjugation pairing by splitting every unitary orbit into its center-valued trace and a Cauchy-Schwarz spread.
---

Setting: a finite group `G` with subgroups `Q_0, Q_1` generating `G`,
a unitary representation `rho` on `H` (`dim H = D`), commutants
`A = rho(Q_0)'`, `B = rho(Q_1)'`, witness algebra
`Z = rho(G)' = A cap B`, and an exact dictionary: a unitary `V_0` with
`V_0 rho(Q_0) V_0* = rho(Q_1)` matching the parahoric generators.  For
`K in U(Z)` and `W in U(B)` define the leak
`ell(K, W) = <V_0 (W K W*) V_0*, K>` (normalized trace pairing).

**Theorem (block-trace reduction).**  Write `B = ⊕_sigma M_(mtilde_sigma)
tensor 1` and let `K_sigma in U(mtilde_sigma)` be the `B`-blocks of
`K`, with block traces `p_sigma = tr(K_sigma)/mtilde_sigma`.  Let
`Y_sigma` be the `sigma`-block compression of `K-tilde = V_0* K V_0`,
with `y_sigma = tr(Y_sigma)/mtilde_sigma`.  Then for every `W`:

```text
| ell(K, W)  -  sum_sigma w_sigma p_sigma conj(y_sigma) |
   <=  sum_sigma w_sigma sqrt(1 - |p_sigma|^2) * spread(Y_sigma),  (BTR1)
```

where `w_sigma = mtilde_sigma d_sigma / D` are the block weights and
`spread(Y)^2 = ||Y - tau(Y)||_2^2` (normalized).  Moreover, since
`V_0` carries the isotypic center of `A` onto that of `B`, the locked
term is a fixed Hermitian quadratic form in the block traces alone:

```text
sum_sigma w_sigma p_sigma conj(y_sigma)  =  p* M p,          (BTR2)
```

with `M` computable from the two branching tables and the dictionary
matching of isotypic projections.  Consequently the joint floor obeys

```text
min_(K, W) |ell|  >=  min_p ( |p* M p| - S(p) ),              (BTR3)
```

a finite explicit inequality over the compact set of admissible
block-trace vectors: `|p_sigma| <= 1` always, `|p_sigma| = 1` FORCED
on every multiplicity-one block, the linear constraint `tau(K) ~ 0`,
the linkage of the `p_sigma` through `K`'s `Z`-block structure and
branching, and the spread budget `S(p)` built from
`sqrt(1 - |p|^2)`-terms — the exact unitarity tradeoff: a block can
evade the locked form only by having small block trace, which is
precisely what unitarity forbids on small blocks and what the trace
condition constrains globally.

This converts the tower-sector floor question, instance by instance,
into finite linear algebra on the computed tables, and explains the
measured anatomy: the indefinite compressed-conjugation form lives in
`M`, the unitarity of `K` lives in the `|p_sigma|`-constraints, and
the off-manifold leak collapse of the soft-penalty probe corresponds
to relaxing `|p_sigma| = 1` on the rigid blocks.

## Attempts

- Proved below (`-proof`); the two-level caveat is genuine: at the
  prototype's single-level pairing no exact dictionary exists (the
  character distance is positive), so `(BTR1)` applies there only
  perturbatively around the control optimum.  The honest exact-
  dictionary instances are the TWO-LEVEL pairings (source level `2^a`
  against target level `2^(a-2)` through the descent map), where the
  computed overlap `<chi_8, chi_2 o phi> = 53 > 0` says the exact
  partial dictionary submanifold is nonempty — the correct design for
  the next probe generation and for any uniform-in-level floor
  statement.
