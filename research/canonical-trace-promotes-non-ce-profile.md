---
rg: 2
id: canonical-trace-promotes-non-ce-profile
kind: claim
title: Group relations promote the hosted non-CE trace profile from canonical delta microstates
distinct_from:
  non-ce-trace-on-sofic-racg: that constructs the non-CE trace on a sofic host; this is the missing promotion mechanism forcing its finite moments from microstates of a different group's canonical trace.
  trace-functorial-bcs-signal-groupification-impossible: that excludes a decoder functorial on every tracial representation; this decoder is required only on finite-dimensional canonical-trace microstates and must use rank, density, phase, or another matricial feature.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
  - research/artifacts/universal-hilbert-schmidt-obstruction-integration-2026-08-22.md
---

For the explicit pair `(W_*,tilde tau_*)` of
`non-ce-trace-on-sofic-racg`, construct a countable recursively presented group
`Gamma`, a nonidentity marked word `w in Gamma`, a finite moment window
`F subset W_*`, and a uniform finite-dimensional decoder with this property.

If a unitary tuple `U` has group-relator energy `E`, satisfies the canonical
delta-profile conditions on the fixed separation window of `Gamma`, and keeps
`w` separated, then the decoder produces a tuple `Z(U)` for the Coxeter
generators such that

```text
max_(g in F) |tr(g(Z(U)))-tilde tau_*(g)| <= C sqrt(E),       (CTP1)
```

and the robust forbidden-word energy of `Z(U)` is at most `C E`.  The
constants and `F` are independent of matrix dimension.

The construction must not extend functorially to arbitrary tracial
representations.  Its forcing observable must be invariant under tensor
amplification: a trace profile, density, normalized multiplicity, or central
phase, never an additive index or absolute rank.

Equivalently at the rate-free level, it is enough to prove that every exact
regular-trace realization of the finite `Gamma` packet in a tracial matrix
ultraproduct decodes the forbidden finite moment profile.  By
`finite-matrix-defect-zero-is-exact-ultraproduct-realizability`, exact
ultraproduct impossibility then returns a positive finite-dimensional
normalized-HS gap automatically; no dimension-dependent rounding modulus is
an additional obligation.

## Attempts

- `non-ce-algebras-have-finite-symmetry-moment-witnesses` shows that no
  infinite operator-algebra profile is needed: every separable diffuse non-CE
  source has finitely many self-adjoint unitary coordinates, a finite word
  window, and one amplification-invariant matrix gap.  This sharpens the
  decoder target but does not solve it, because those target word traces are
  generally intermediate scalars rather than the canonical delta character.
  Projective closure of the full symmetry basis would force hyperfiniteness.

- **Multiplicity lane:** use the Schur predicate rank jump and a returning
  finite-scale wire. The local gap is established; stationary regular type
  flow is the current escape.
- **Phase lane:** put a predicate word in the tracial projective kernel. This
  avoids type flow but still lacks a phase-safe normal-closure certificate.
- An exact trace decoder is impossible by
  `trace-functorial-bcs-signal-groupification-impossible`; the decoder must
  expose a matrix-only feature before taking a tracial limit.
