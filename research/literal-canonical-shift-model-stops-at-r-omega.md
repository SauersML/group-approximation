---
rg: 2
id: literal-canonical-shift-model-stops-at-r-omega
kind: claim
title: The canonical literal shift model spatializes in R-omega but not hyperfinitely in R
distinct_from:
  literal-group-embeds-in-hyperfinite-unitary-group: that open claim asks for any faithful hyperfinite character of the literal group; this rules out only the canonical regular crossed-product realization and does not assert that every nonregular character fails.
  literal-group-sofic: that supplies finite permutation packets and hence an ultrapower embedding; this identifies why the corresponding coherent block-shift construction stops at the ultrapower.
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that constrains faithful hyperfinite characters of the Kazhdan base; this proves that the canonical character of the whole nonamenable telescope quotient has nonhyperfinite closure.
---

Let

```text
V=(Z[1/2]^3 semidirect_product SL_3(Z)) semidirect_product Z
```

be the telescope quotient of the literal group `E`.  Let `(A,tau)` be any
hyperfinite finite von Neumann algebra and let `beta:V actson A` be a
trace-preserving action.  Then the canonical tracial crossed product

```text
M=A crossed_product_beta V
```

is not hyperfinite.  In particular, no faithful character of `E` obtained
by putting its lamp/Clifford algebra in `A` and using the canonical regular
crossed-product unitaries for `V` can prove
`literal-group-embeds-in-hyperfinite-unitary-group`, including a central-mark
sector with `w |-> -1`.

More generally, no character of `E` with hyperfinite GNS closure can restrict
to the regular character on the subgroup `V`.  Thus this obstruction applies
to every proposed marked splitting whose `w |-> -1` piece retains the
canonical sofic/regular character on the telescope quotient, even if that
piece is not presented explicitly as a crossed product.

The obstruction exactly separates `R` from `R^omega`.  For a nontrivial
matrix algebra `F`, put

```text
A_0=bar_tensor_(n in Z) F
```

with its product trace and let `sigma` be the bilateral tensor shift.  Then
`sigma` is outer on `A_0`, but its diagonal action is inner in `A_0^omega`.
Thus coherent finite block permutations provide an ultrapower implementing
unitary, while no unitary of the lamp factor itself implements the honest
shift.  Adjoining all of `V` by the canonical crossed product supplies exact
implementers, but the preceding paragraph shows that the resulting von
Neumann algebra is not hyperfinite.

Consequently any successful faithful hyperfinite character of `E` must be
genuinely noncanonical on `V`: its restriction to `V` cannot be the regular
character, and its implementing unitaries cannot arise from the canonical
crossed product of a weakly dense lamp factor.  This is an obstruction to
the proposed central-mark block splitting, not a refutation of the open
embedding claim.
