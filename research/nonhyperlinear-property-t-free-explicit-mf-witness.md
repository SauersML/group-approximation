---
rg: 2
id: nonhyperlinear-property-t-free-explicit-mf-witness
kind: claim
title: Produce the manuscript's explicit corona-invisible group element without Property T
artifacts:
  - research/artifacts/nonhyperlinear-normal-augmentation-source-audit-2026-08-30.md
  - notes/PROPERTY_T_FREE_CONTEXT_ENERGY_2026-09-07.md
  - research/artifacts/jacobson-two-braid-reduction-2026-09-07.md
distinct_from:
  property-t-free-manuscript-results: that also demands binary-Leavitt full collapse, the full radical calculus, and a torsion-free finitely presented endpoint; this is exactly its first explicit-group obligation.
  perfect-lcs-gap-implies-weak-non-mf: that is a conditional theorem for a hypothetical perfect LCS gap; this asks for an unconditional explicitly specified group and element.
---

Construct an explicitly specified countable group `G` and a named nontrivial
element `j in G` such that every homomorphism

```text
G -> U(product_n M_(d_n) / directSum_(||.||) M_(d_n))
```

kills `j`, using no Property `(T)`, Kazhdan pair, Kazhdan projection, or
theorem whose proof depends on a Kazhdan hypothesis.  Equivalently,

```text
1!=j in Rad_MF(G).
```

This is endpoint 1 of `property-t-free-manuscript-results`.  The exact
source-specific route through a central sign is isolated at
`nonhyperlinear-bloop-central-sign-corner-route`.

## Attempts

- The joint Jacobson two-braid route is refuted:
  `jacobson-two-braid-infimum-is-zero` constructs an amenable quotient
  retaining its entire finite packet. Consequently its matrix infimum is
  zero, even after imposing the tail braid exactly. A Jacobson proof must
  use additional mixed relations beyond that presentation; the full
  Jacobson group and the independent existence goal are not refuted.
  The added TS word gives the stronger marked presentation `Gamma_2`:
  `jacobson-ts-cell-is-independent-after-first-raw-commutation` proves
  its literal head survives and excludes the seven-ray quotient, while
  `jacobson-ts-cell-excludes-monomial-natural-head-models` excludes
  the whole monomial natural-head family in characteristic two.
  Neither statement supplies a complex-unitary matrix obstruction;
  the MF status of `Gamma_2` remains open.
  The stronger candidate with a shifted finite packet and one boundary
  cell has a reconstructed finite subgroup of order 64512:
  `jacobson-boundary-cell-reconstructs-finite-root-packet` also proves
  coherent correction in the original matrix dimension while fixing
  the original packet. This reduces its approximation problem to two
  mixed relators over a specified finite amalgam. A positive matrix
  gap for those remaining relators has not been proved.

- The fixed no-CE BCS and the operator-norm endgame are established.  The
  remaining input on this route is the exact central-sign corner map
  `nonhyperlinear-bloop-central-sign-corner`.
- Conditional perfect-LCS and selected signed-Hecke corners do not establish
  this claim: the first lacks an instance, while the second does not
  authenticate its chosen finite-subgroup type in every corona map.
- The independent finite relation-energy attempt has an exact boundary:
  `finite-context-energy-certificate-iff-word-trivial` shows that allowing any
  fixed finite word contexts still certifies only ordinary word triviality.
  Polynomial contexts do not repair this for a nontrivial mark. This does
  not exclude a global scalar operator-norm estimate or a matrix-dependent
  construction, and leaves the existence target open. The sharper fixed-list
  criterion and linear counterexample-size bound are proved in
  `word-energy-domination-is-free-subgroup-membership`.
