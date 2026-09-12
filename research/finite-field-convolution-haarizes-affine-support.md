---
rg: 2
id: finite-field-convolution-haarizes-affine-support
kind: claim
title: Repeated finite-field convolution canonically Haarizes the affine support of every stationary process
distinct_from:
  infinite-label-process-is-haar-linear-iff-fourier-binary: that tests whether the original process is already Haar linear; this constructs a Haar linear weak limit from every process and computes exactly which information survives.
  coinduced-coordinate-fourier-test-factorizes: that adds independent coordinates indexed by cosets without changing the source test; this adds independent copies in the same coordinate space and then sums them.
  tracial-support-affine-linearization: that replaces each finite BCS constraint support by its local affine hull; this takes the simultaneous closed affine hull of the entire infinite translate process.
---

Let `Lambda` act by coordinate shifts on

```text
E=(F_p^I)^Lambda
```

for finite or countable `I`, and let `nu` be any shift-invariant Borel
probability measure.  Let `nu^(star n)` denote convolution under coordinatewise
addition.  Then

```text
nu^(star pn)  weak-star-converges  m_K,                 (FCH1)
```

where `m_K` is Haar measure on the closed invariant subgroup

```text
K=closure(span_Fp(supp(nu)-supp(nu))).                 (FCH2)
```

Equivalently, take `pn` independent samples of the original process and add
their labels.  Their law converges to the Haar linear process on the closed
linear span of all support differences.  This is a universal constructive way
to meet the zero-or-one Fourier criterion.

There is also an offset-preserving form.  For any `x_0 in supp(nu)`,

```text
nu^(star (pn+1))  weak-star-converges  m_(x_0+K).       (FCH3)
```

Homogenize that invariant affine coset by adjoining one fixed scalar
coordinate:

```text
K_tilde=closure(span_Fp{(x,1):x in supp(nu)}) <= E x F_p. (FCH4)
```

The shift fixes the last coordinate and acts by group automorphisms on
`K_tilde`.  Haar measure on `K_tilde`, conditioned on the invariant positive
measure fiber `t=1`, is precisely `m_(x_0+K)`.  Consequently the affine-hull
action crossed product is a central corner of the Haar algebraic crossed
product on `K_tilde`.  If a non-CE witness survives in the affine-hull action,
this homogenization immediately compiles it into a non-hyperlinear
semidirect product.

It also computes the loss exactly.  A finite affine equation holds
`nu`-almost surely precisely when it holds on `x_0+K`; these and only these
equations survive `(FCH3)` and the `t=1` corner of `(FCH4)`.  Every support
restriction not closed under affine span can be destroyed.

For the perfect tailored-game route this gives a sharp fork.  Perfect
acceptance survives the affine-corner Haarization whenever every accepted
full-answer relation encountered by the source is affine.  But then
`tailored-gap-is-lcs-or-has-a-nonaffine-edge` already turns the game into a
perfect LCS gap and yields a non-hyperlinear solution group.  In the remaining
case some accepted relation is nonaffine, and the Haarized affine hull can add
losing answer pairs.  Thus convolution supplies the canonical Haar process,
but retaining the non-CE witness is exactly the existing nonlinear
control-freezing/groupification gap; taking more convolution powers cannot
repair it.
