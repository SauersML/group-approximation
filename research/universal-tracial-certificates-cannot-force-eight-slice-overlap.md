---
rg: 2
id: universal-tracial-certificates-cannot-force-eight-slice-overlap
kind: claim
title: No universal tracial SOS or finite-level NPA certificate can force the eight-slice overlap
distinct_from:
  shared-bcs-eight-slice-full-overlap-actuator: that asks for a matrix-ultraproduct-only lower bound; this proves that the lower bound cannot come from an identity or positivity certificate valid in every tracial representation.
  exact-five-fourths-projection-return-collapses-the-packet: that rules out exact projection inclusions; this rules out scalar tracial certificates even when no projection inclusion is asserted.
  trace-functorial-bcs-signal-groupification-impossible: that forbids a functorial decoder lower-bounding a BCS signal by a mark; this applies directly to the final one-overlap scalar and identifies finite-level NPA and cyclic SOS as forbidden proof systems.
---

Let `Gamma=<X|R>` be any proposed marked extension in which the finite
eight-slice packet embeds.  Let `P_f,S,C` be the packet projections of
`eight-slice-bookkeeping-symmetrizes-s3-failures` and
`eight-slice-capacity-deficit-is-one-overlap-moment`, so

```text
tau_Gamma(S)-tau_Gamma(C)=tau_Gamma(P_f)/16>0.          (UTC1)
```

For every group word `W`, in the canonical group von Neumann algebra,

```text
Theta_W=tau_Gamma(S W^* C W S)<=tau_Gamma(C).           (UTC2)
```

Consequently

```text
tau_Gamma(S)-Theta_W>=tau_Gamma(P_f)/16>0.              (UTC3)
```

There is therefore no inequality of the form

```text
tau(S)-tau(S W^* C W S)
 <= K sum_(r in R_0) tau((r-1)^*(r-1))                 (UTC4)
```

valid in every tracial representation of the proposed presentation, for any
finite relator set `R_0` and finite `K`.  Indeed the right side of `(UTC4)`
is zero in the canonical regular representation, while `(UTC3)` makes the
left side positive.

In particular `(UTC4)` cannot be certified by a cyclic sum-of-squares
identity modulo the relator ideal.  Nor can the desired reverse inequality

```text
Theta_W>=tau(S)-K E_rel                                (UTC5)
```

come from a finite level of an NPA/tracial moment hierarchy: finite-level
dual feasibility is a positivity certificate valid for every operator model
of the displayed relations, including the canonical regular model.  The
same observation is forced upstream by the static source game: its commuting
value is one, so no finite NPA upper bound can certify its strictly smaller
finite-dimensional value.

This does not refute `shared-bcs-eight-slice-full-overlap-actuator`.  A
uniform inequality valid in all matrix algebras passes only to tracial matrix
ultraproducts.  It may fail in the canonical regular trace precisely when
that trace is not Connes embeddable.  Thus a valid proof of `(UTC5)` must use
one of the genuinely matrix-origin features which finite tracial SOS does not
see: a dimension-sensitive polynomial identity assembled uniformly, integer
multiplicity with an anti-dilution mechanism, or the finite-dimensional gap
of the fixed non-CE source itself.

The practical consequence is a proof-system firewall:

```text
ordinary cyclic trace / finite positive-definite Hecke inequality /
finite-level NPA dual
    cannot prove the overlap actuator;

matrix-ultraproduct separation tied to the shared non-CE moments
    is the remaining admissible target.                              (UTC6)
```
