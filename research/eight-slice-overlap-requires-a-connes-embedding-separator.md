---
rg: 2
id: eight-slice-overlap-requires-a-connes-embedding-separator
kind: claim
title: The one-overlap actuator is exactly a Connes-embedding separator, not a finite packet lemma
distinct_from:
  single-context-v4-exit-capacity-is-already-nonhyperlinearity: that applies the regular trace to a contextwise capacity theorem; this applies to the global equalized one-overlap scalar and identifies the admissible matrix-only form.
  universal-tracial-certificates-cannot-force-eight-slice-overlap: that excludes universal proof systems; this records the exact positive formulation which survives the exclusion.
---

Fix a proposed finitely presented extension `Gamma` preserving the embedded
eight-slice packet and write

```text
F=tau(S)-tau(S W^* C W S).                              (CES1)
```

The packet calculation gives, in every tracial representation,

```text
F>=tau(S)-tau(C)=tau(P_f)/16.                           (CES2)
```

Suppose instead that every finite-dimensional approximate representation
of `Gamma` obeys

```text
F<=K E_rel+o(1).                                        (CES3)
```

Then every homomorphism of `Gamma` into a tracial matrix ultraproduct obeys
`F=0` at zero relator defect.  Combining with `(CES2)` kills the image of
`P_f`.  If the shared non-CE BCS gap forces positive total forbidden mass
whenever the original mark survives, the mark cannot survive in a matrix
ultraproduct.  The canonical regular representation still has
`tau(P_f)>0`, so it violates `(CES3)` and is therefore non-embeddable.

Thus `(CES3)` is not an auxiliary finite-packet stability statement.  It is
already the separating trace-polynomial assertion at the heart of the final
nonhyperlinearity proof.  Its finite moment list is explicit by `(EOM7)`, but
its truth on matrices cannot be established by a positivity argument that
also holds in arbitrary finite von Neumann algebras.

Equivalently, the correct construction target is not merely to find a word
`W` with attractive finite-group restriction matrices.  It is to couple
`W` to the original shared BCS moments so that the fixed trace polynomial
`F-K E_rel` is nonpositive on every matrix tuple while remaining positive in
the exact marked regular model.  This is exactly a source-specific
Connes-embedding separator in ordinary group-word coordinates.

