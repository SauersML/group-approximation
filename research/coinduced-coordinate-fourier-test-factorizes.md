---
rg: 2
id: coinduced-coordinate-fourier-test-factorizes
kind: claim
title: The Haar Fourier test for base-coordinate labels factorizes exactly under pmp coinduction
distinct_from:
  infinite-label-process-is-haar-linear-iff-fourier-binary: that gives the global zero-or-one criterion for one action; this computes every moment after coinduction and compares it exactly with the source criterion.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that compares finite crossed-product inclusions and a semifinite induction corner; this is a probability-law calculation for arbitrary measurable source labels.
  non-ce-property-t-equivalence-relation-exists: that embeds the IRS algebra into an equivalence-relation algebra; this theorem concerns a relation and does not identify that algebra with a transformation crossed product of the IRS actor.
---

Let `H<Lambda`, let `alpha:H acts on (X,mu)` be pmp, and let

```text
Y=X^(Lambda/H)
```

carry the pmp coinduced action.  For finite or countably many labels
`f_i:X->F_p`, define base-coordinate labels

```text
F_i(y)=f_i(y_H).                                        (CFT1)
```

Then the full `Lambda`-translate process of the `F_i` is Haar linear if and
only if the full `H`-translate process of the `f_i` is Haar linear.  More
precisely, every finite Fourier moment upstairs is a finite product of source
Fourier moments, one for each coset touched by its coefficients.

If the `H`-translates of the `f_i` generate the probability algebra of `X`,
then the `Lambda`-translates of the `F_i` generate that of `Y`.  Thus the
canonical coordinate construction cannot manufacture a Haar compiler from a
non-Haar source by adding the independent off-base coordinates.

In particular, if a source action of a virtually free group has generating
labels whose translate process is not Haar linear, ordinary coinduction to a
larger actor does not repair it.  This does **not** directly apply to the
Manzoor witness: `non-ce-property-t-relation-from-irs` puts the IRS GNS algebra
inside an equivalence-relation algebra, not inside the transformation crossed
product of the free-group stabilizer action.  Confusing those two algebras in
the presence of isotropy gives a false shortcut.  Thus actor change by
coinduction remains unavailable until a genuine source algebraic envelope has
already been constructed, agreeing with
`coinduction-preserves-but-cannot-create-algebraic-envelope`.
