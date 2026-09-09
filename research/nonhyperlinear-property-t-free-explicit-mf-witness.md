---
rg: 2
id: nonhyperlinear-property-t-free-explicit-mf-witness
kind: claim
title: Produce the manuscript's explicit corona-invisible group element without Property T
artifacts:
  - research/artifacts/nonhyperlinear-normal-augmentation-source-audit-2026-08-30.md
  - notes/PROPERTY_T_FREE_CONTEXT_ENERGY_2026-09-07.md
  - research/artifacts/jacobson-two-braid-reduction-2026-09-07.md
  - research/artifacts/jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md
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
source-specific route through a full finite-subgroup augmentation
corner is `nonhyperlinear-bloop-finite-augmentation-route`.
The older central-sign route is a sufficient special case.

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
  The precise remaining premise is now
  `jacobson-boundary-amalgam-mixed-gap`: positivity would imply the
  requested marked collapse by
  `jacobson-boundary-amalgam-gap-characterizes-mark-collapse`.
  Exact TS and braid relations additionally reconstruct the full
  first-level matrix root group, as proved in
  `jacobson-mixed-cells-reconstruct-full-first-level-root-packet`.
  Its smallest nonzero character orbit cannot extend even after adding
  arbitrary root-trivial summands:
  `jacobson-single-rank-one-root-orbit-cannot-extend` proves that every
  exact head-retaining representation has dimension at least 98. The
  resulting gap in dimensions at most 97 does not establish the
  unrestricted positivity premise.
  The doubled-fiber obstruction
  `jacobson-double-rank-one-root-orbit-cannot-extend` strengthens the
  lower bound to 147 and gives an explicit error bound through
  dimension 146. With the additional full boundary packet, the
  separate candidate `Theta` has an embedded `GL_6(F_2) x GL_3(F_2)`
  by `jacobson-full-boundary-forces-six-coordinate-packet`; neither
  finite reconstruction settles the unrestricted matrix gap.

  The separate finitely presented candidate `Theta_shift` adjoins
  seven stable-letter equations. Its explicit bilateral action retains
  the head, and `jacobson-stable-letter-closes-boundary-recursion`
  proves the entire finite boundary recurs under that conjugation.
  The new remaining premise is `jacobson-shift-mixed-gap`: finite
  correction makes all stable-letter relations on the original finite
  packet exact, leaving three mixed norm errors. Its exact infimum
  and the original nine-test infimum differ by at most the explicit
  factor 1337. This establishes a dimension-independent reduction,
  not the required positive lower bound.

  The original literal kernel is now known to be normally generated
  by the nontrivial coherence word `E`. Adding that word gives a
  proper quotient with the same faithful literal head. The claims
  `jacobson-coherent-quotient-has-four-word-gap-criterion` and
  `jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy`
  identify its entire presentation with the explicit bilateral
  operator group and make its four-word infimum exactly an MF
  decision. The required positivity is the open claim
  `jacobson-coherent-matrix-gap`. Separately correcting its three
  finite groups cannot freeze both overlaps of the third group,
  by `jacobson-third-packet-correction-must-move-an-edge`; a
  simultaneous correction or another unrestricted argument is
  still required.

- The fixed no-CE BCS and the operator-norm endgame are established.
  The general remaining construction is
  `nonhyperlinear-bloop-finite-augmentation-corner`: an exact map
  into the full augmentation corner of an embedded nontrivial finite
  subgroup. That subgroup need not be normal. The prior central-sign
  gate adds an optional restriction. The existing noncentral torsion
  endgame and its general finite-subgroup extension justify removing
  it. Affine-field packets supply full matrix corners of arbitrary
  desired unital matrix width, but do not establish the shared BCS
  identities across different contexts.
- Conditional perfect-LCS and selected signed-Hecke corners do not establish
  this claim: the first lacks an instance, while the second does not
  authenticate its chosen finite-subgroup type in every corona map.
- The user-supplied compression-centralizer criterion, recorded as
  `locally-finite-centralizer-derived-subgroup-is-mf-invisible`,
  passes mathematical review and gives ordinary perfect-lamp
  applications without a normal Kazhdan subgroup. Its compression
  lemma explicitly uses the Kazhdan spectral projection of `L`.
  It therefore does not satisfy this goal's proof restriction,
  even when the resulting ambient group itself maps onto `Z`
  and fails property `(T)`.
- The independent finite relation-energy attempt has an exact boundary:
  `finite-context-energy-certificate-iff-word-trivial` shows that allowing any
  fixed finite word contexts still certifies only ordinary word triviality.
  Polynomial contexts do not repair this for a nontrivial mark. This does
  not exclude a global scalar operator-norm estimate or a matrix-dependent
  construction, and leaves the existence target open. The sharper fixed-list
  criterion and linear counterexample-size bound are proved in
  `word-energy-domination-is-free-subgroup-membership`.
