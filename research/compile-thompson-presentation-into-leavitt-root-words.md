---
rg: 2
id: compile-thompson-presentation-into-leavitt-root-words
kind: route
title: Compile the Thompson relations and remove one exact marked-word consequence
target: leavitt-has-an-explicit-finite-c-killing-certificate
requires:
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
  - thompson-v-has-no-nontrivial-fd-unitary-representation
artifacts:
  - research/artifacts/leavitt-eight-word-reduction-and-s3-repair-2026-09-08.md
  - research/artifacts/leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md
  - research/artifacts/leavitt-nine-word-dag-verification-2026-09-08.json
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
the shorter compiler uses `q_0=[gamma^2(b_1),a]` and `p_1=[e,u]`,
giving `|B|<=164` and a largest relator bound of `9880`. The accompanying
exact prefix verifier evaluates shared subexpressions without expanding
the words. No finite-group enumeration or unspecified word search is used.

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

The new reduction artifact proves the literal free-product identity
`rho_4=[((A c)^(-1)c^(-1))^2,r_*]`. Thus `r_*` already implies
`rho_4=1`. It also proves `rho_1=a c d^2 c^(-1)a^(-1)`.
Consequently killing the eight words
`r_*,d^2,rho_2,rho_3,rho_5,rho_6,rho_7,rho_8` kills the entire
nine-word packet used above, proving the strengthened target. The same
identities give `E_8<=E_9<=2 E_8` for all unitary evaluations.
