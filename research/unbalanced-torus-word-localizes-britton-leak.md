---
rg: 2
id: unbalanced-torus-word-localizes-britton-leak
kind: claim
title: One unbalanced torus word localizes the Britton leak on two negative roots
artifacts:
  - research/unbalanced-torus-britton-leak-proof.md
distinct_from:
  one-britton-moment-forces-uniform-actor-noncorrectability: that compares the whole actor packet with exact arithmetic representations using property T; this uses one explicit arithmetic relator and gives a direct lower bound on two root commutators of the conjugate stable letter, with no representation comparison.
  arithmetic-leak-commutator-localizes-in-overlap-commutant: that places a relative commutator in the commutant of an adjacent overlap; this proves a quantitative finite-matrix alternative on two named negative simple roots.
  two-torus-closures-detect-denominator-multiplicity: that computes the unbalanced arithmetic identity and its action on an exact product twist; this applies the identity to an arbitrary approximate packet and extracts a dimension-free root-leak inequality.
---

Use the notation and torus relator `R_tor=h^(-1)D_12D_23` from
`two-torus-closures-detect-denominator-multiplicity`.  Let `X_g,H,T` be
unitary matrices assigned to the displayed lattice elements, `h`, and the
central HNN letter.  Put

```text
T_1=H^* T H,
eta_R=||ev(R_tor)-I||_2,

eta_L=max_(L in F)||T X_L T^*-X_L||_2,
F={x_12(p),w_12(1),x_23(p),w_23(1)},

eta_21=||T_1 X_(x_21(-1))T_1^*-X_(x_21(-1))||_2,
eta_32=||T_1 X_(x_32(-1))T_1^*-X_(x_32(-1))||_2.       (UBL1)
```

Then

```text
||T H T^*-H||_2
 <=2 eta_R+6 eta_L+eta_21+eta_32.                       (UBL2)
```

If the one-Britton canonical moment also satisfies

```text
|tr([T,H])|<=eta_B,
```

then

```text
eta_21+eta_32
 >=sqrt(2(1-eta_B))-2 eta_R-6 eta_L.                    (UBL3)
```

Consequently, along every canonical arithmetic-centralizer HNN microstate,

```text
liminf max(eta_21,eta_32)>=1/sqrt(2).                   (UBL4)
```

Thus the stable-letter leak cannot remain an unauthenticated global actor
outlier: after one conjugation by the denominator element, a fixed positive
amount appears on one of the two named negative simple roots.  This is a
finite-window, dimension-free localization.

It does not yet prove UCP matrix-range capture.  A central dual separator
commutes with `T`, whereas `(UBL4)` concerns the conjugate letter `T_1`; the
remaining step is to make this root leak charge the separator's off-spectral
multiplicity component rather than merely certify noncommutation.
