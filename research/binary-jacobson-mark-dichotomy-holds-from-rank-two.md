---
rg: 2
id: binary-jacobson-mark-dichotomy-holds-from-rank-two
kind: claim
title: The binary Jacobson finitary kernel, faithful mark and MF radical dichotomy hold from rank two
distinct_from:
  binary-jacobson-mf-radical-dichotomy: that states the same alternative for the rank-five elementary group only; this proves it for every rank at least two, the new ingredient being generation of the within-ray transvections without a third outer row.
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that identifies the finitary kernel and the residual quotient in rank five; this extends that identification to ranks two and three.
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that proves head-retaining maps out of the rank-five group are faithful; this proves the same in every rank at least two.
  rank-four-jacobson-head-retention-is-faithful: that is the rank-four case, obtained through a third matrix coordinate; this covers ranks two and three as well.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**ESTABLISHED.**  Let `J = F_2<S,T | TS = 1>`, `Q = 1 - ST`, and for
`n >= 2` put

```text
G_n = EL_n(J),      L_n = GL_fin(N x {1,...,n}, F_2),
Q_0^(n) = EL_n(F_2[z,z^(-1)]),      w_n = e_12(Q).                (JR2)
```

Then for **every** `n >= 2`:

1. the symbol sequence `1 -> L_n -> G_n -> Q_0^(n) -> 1` is exact, and
   `L_n` is infinite and simple;
2. `C_(G_n)(L_n) = 1`, so any homomorphism out of `G_n` retaining any
   nonidentity element of `L_n` — in particular `w_n` — is injective;
3. `Rad_MF(G_n) <= L_n`, hence

```text
Rad_MF(G_n) = 1        if G_n is operator-MF,
Rad_MF(G_n) = L_n      otherwise,                                 (JR3)
```
   with no intermediate value, and in the second case every MF-target
   homomorphism factors through the residually finite `Q_0^(n)`.

The mathematics is the rank-five argument of
`binary-jacobson-mf-radical-dichotomy` run at general rank.  The single
step that previously needed `n >= 3` was the production of within-ray
finitary transvections by commuting through a third outer coordinate;
`two-outer-rows-suffice-for-finitary-transvections` replaces it.

**Scope.**  This is a rank extension of an existing structural
description; it decides neither alternative in `(JR3)`.  Which side holds
is `binary-jacobson-steinberg-head-root-is-mf-invisible` (established at
rank five by rank-weighted Kazhdan transport) and, without property (T),
`property-t-free-jacobson-head-collapse`.

DERIVATION
binary-jacobson-rank-two-dichotomy-proof
