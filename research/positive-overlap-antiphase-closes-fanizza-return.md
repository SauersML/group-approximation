---
rg: 2
id: positive-overlap-antiphase-closes-fanizza-return
kind: claim
title: Leakage localization plus the book-tag antiphase cell closes the Fanizza return without near-full overlap
distinct_from:
  shared-bcs-eight-slice-full-overlap-actuator: that asks one actuator to return almost all three source blocks into the smaller capacity; this permits only the positive overlap forced by leakage localization and charges it by antiphase.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that needs overlap close to full source mass to align two transports; this never aligns them and bounds their cross-Gram mass directly.
---

Let `q` denote the total forbidden mass in the fixed shared Fanizza BCS after
the eight-slice construction, and let `E_base` be its original shared-word
energy.  Write the robust source gap as

```text
E_base+q >= beta_B.                                      (PACF1)
```

For each fixed context use the three sources `(BHA2)`, their exits `(BHA7)`,
and the parent capacity projection from `(ESB3)`.  Summed over the finite
context menu,

```text
s-c=q/16.                                                (PACF2)
```

Let `ell` be the total off-capacity leakage, `O` the complete ordered
cross-Gram sum, and `Lambda` the localized non-CE moment functional.  The
Gram-capacity and corner-gap estimates give

```text
q/16 <= 2 ell+O,
ell <= Lambda/beta_B^corner.                             (PACF3)
```

Assume precisely the still-open shared localization estimate

```text
Lambda <= K_loc E_rel+o(1).                              (PACF4)
```

This is `(NCL13)`; no stronger return or near-full overlap hypothesis is
used.  The multiple-HNN book tag of
`three-book-hnn-antiphase-charges-every-cross-gram` gives

```text
O <= K_tag E_rel+o(1).                                   (PACF5)
```

Combining `(PACF3)--(PACF5)` yields

```text
q <= C_ret E_rel+o(1),
C_ret=16(2K_loc/beta_B^corner+K_tag).                    (PACF6)
```

For total energy `E=E_base+E_rel`, `(PACF1)` and `(PACF6)` imply the
dimension-independent floor

```text
E >= beta_B/(1+C_ret)-o(1).                              (PACF7)
```

Equivalently, if the presentation defect tends to zero, then `q` tends to
zero and the native Fanizza signal collapses by the existing NONHALT estimate.
Britton embedding supplies exact marked completeness on the HALT side.
Therefore `(NCL13)` together with the already established native-signal
decoder/diagonal is sufficient for a finitely presented non-hyperlinear
group.

This removes `(SBO1)` from the load-bearing path.  Positive overlap is not by
itself a contradiction, as shown by
`positive-cross-gram-mass-alone-has-no-holonomy-floor`; the explicit
antiphase word relations are essential.  But once they are present, the
cross-Gram **mass**, rather than a near-unit polar gauge, is the correct
observable, and the spectral-corner/return-amplification stage can be omitted.

The sole unresolved theorem in this composite is now `(PACF4)`: the actual
exit leakage projections must approximately reduce the same original shared
Fanizza tuple and be BCS-quiet with cost controlled before the context words
split.  The tag HNN cell neither assumes nor proves that localization.
