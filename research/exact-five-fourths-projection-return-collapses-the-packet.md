---
rg: 2
id: exact-five-fourths-projection-return-collapses-the-packet
kind: claim
title: An exact stable-letter return of the five-fourths blocks cannot preserve the finite packet
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that produces a regular stationary type flow for every finite graph of finite groups; this rules out the more direct idea of routing the three explicit projections into a smaller parent carrier by canonical-trace conservation.
  finite-subgroup-type-exclusion-is-already-nonhyperlinearity: that shows uniform exclusion of a finite-subgroup irrep from all microstates already solves the global problem; this shows that exact group-algebra projection compression cannot even coexist with an injective copy of the local packet.
  five-fourths-projection-surplus-pays-linear-hs-energy: that is the useful finite-dimensional payment if an exit-capacity theorem is derived analytically; this forbids imposing the required exits as literal exact stable-letter conjugacies.
---

Let `T_f` be the full V4 packet and let

```text
P_f,F_00,F_01,F_11 in C[T_f]
```

be the nonzero projections from
`full-v4-latent-coordinate-has-an-operator-five-fourths-floor`.  There is no
group `Gamma` containing `T_f` injectively, group elements `g_b,h in Gamma`,
and projections `E_b in C[Gamma]` such that

```text
E_b=g_bF_bg_b^-1,
sum_b E_b <= hP_fh^-1.                                  (EFR1)
```

Indeed, the canonical group trace of `C[Gamma]` restricts to the normalized
regular trace of `C[T_f]`.  It is faithful on the finite-dimensional
`C^*`-algebra `C[T_f]`, so `tau(P_f)>0`.  Conjugation preserves trace, while
the operator inequality in `(EFR1)` and the five-fourths identity give

```text
(5/4)tau(P_f)
 =sum_b tau(F_b)
 =sum_b tau(E_b)
 <=tau(P_f),                                             (EFR2)
```

a contradiction.

Consequently a presentation which imposes `(EFR1)` by literal stable-letter
relations necessarily destroys the injective packet copy (and with it the
intended marked carrier).  The local S3/V4 return cannot be an exact
projection atlas.  Its exit-capacity inequality must be a
**finite-dimensional-only consequence** of multiplicity, rigidity, or a
non-Connes-embeddable recurrence; it must fail in the canonical regular
representation of the final group.
