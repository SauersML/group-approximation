---
rg: 2
id: compile-thompson-presentation-into-leavitt-root-words
kind: route
title: Compile the eight Thompson presentation relations and kill the native coordinate swap
target: leavitt-has-an-explicit-finite-c-killing-certificate
requires:
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
  - thompson-v-has-no-nontrivial-fd-unitary-representation
artifacts:
  - research/artifacts/leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md
---

The artifact gives explicit words `A,B,D` in the marked free product.
Under the complete prefix code `(00,01,1)`, their native images are the
inverse-map left-matrix realizations of Bleak--Quick's right-acting
generators `(00 01)`, `(01 10 11)`, `(1 00)`. In particular `A=j` is
the previously constructed coordinate transposition `(12)`.

The eight displayed words `rho_i(A,B,D)` are precisely the equations of
[Bleak--Quick, Theorem 2.1, equation (2.3)](https://arxiv.org/html/1511.02123#S2),
written as relators. They therefore vanish in the native Leavitt group.
The root compiler and the length accounting are proved in the artifact;
no finite-group enumeration or unspecified word search is used.

If a homomorphism `pi:P -> U(n)` kills these eight words, the presentation
gives a homomorphism `V -> U(n)` sending its first generator to `pi(j)`.
The required representation theorem makes this homomorphism trivial.
Thus `pi(j)=I`. The ninth word `r_*=jcjc` then forces `pi(c)^2=I`, while
the free-product relation already gives `pi(c)^3=I`. Hence `pi(c)=I`.

Embed a finite target group into its unitary regular representation to
obtain the finite-group conclusion. In each fixed frozen-factor dimension,
the defect is a continuous function on a compact unitary group; a zero
would contradict the nontrivial regular `C_3` factor. Its minimum is
therefore positive in that dimension. This last argument supplies no
uniform minimum as the dimension varies.
