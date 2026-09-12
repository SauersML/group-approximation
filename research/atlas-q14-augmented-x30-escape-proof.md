---
rg: 2
id: atlas-q14-augmented-x30-escape-proof
kind: route
title: Use the quotient trace, then Malcev-separate an exact matrix image
target: atlas-q14-augmented-zero-set-has-x30-one-escape
requires:
  - atlas-charts-overlap-trivially
  - atlas-word-19243-is-kernel-relation
  - atlas-q14-forces-t30-covariance-floor
  - atlas-a4-finite-quotient-escape-fence
---

All relators in `(QZE1)` are true kernel words for the canonical two-chart map
to the binary-Leavitt target.  Hence that map factors through `Gamma_+`.
Injectivity and trivial overlap of the two target chart copies imply the same
for their copies in `Gamma_+`.

The canonical trace on `L(Gamma_+)` restricts to the regular trace on both
finite chart algebras.  Include `L(Gamma_+)` trace-preservingly in a finite
factor.  Two trace-preserving copies of the same finite-dimensional algebra
in a finite factor are unitarily conjugate, and the conjugator may implement
the named isomorphism between the two copies of `C[A8]`.  The resulting common
frame satisfies every quotient relator exactly.

In the total-frame notation of the q14 double-coset theorem,

```text
W rho(t23) W^* rho(t30)
```

is the group unitary attached to one element from the second chart times one
from the first chart.  It is nonidentity: equality would put a nontrivial
transvection in the intersection of the two chart copies.  The canonical
group trace of this word is therefore zero.  This proves `(QZE2)`.

Now suppose an exact matrix model exists.  Its two chart images generate a
finitely generated linear group `Lambda`, and the relations give a
homomorphism `Gamma_+ -> Lambda` faithful on both charts.  The cross-chart
word above is also nonidentity in `Lambda`: if it were identity then
`x_30=0`, contradicting the exact q14 lower wall `x_30^2>=1/2`.

Malcev residual finiteness supplies finite quotients of `Lambda` separating
that word and each of the finitely many nonidentity elements in both chart
copies; taking their finite product separates them simultaneously.  The
result is a nontrivial finite quotient of `Gamma_+` with injective chart
restrictions and nontrivial cross word.  Its left regular representation is
an exact regular-margin model, and the nontrivial cross word has trace zero,
so `(QZE3)` holds.

Conversely, a nontrivial finite quotient of `Gamma_+` is also a nontrivial
finite quotient of the packet-plus-19243 quotient.  The established simple
chart dichotomy makes both chart restrictions injective.  Its left regular
representation is therefore an exact augmented regular-margin matrix model.
The q14 wall excludes identity of the cross word; canonical regular trace
then again gives `x_30^2=1`.  This proves the equivalence and all stated
no-go consequences.
