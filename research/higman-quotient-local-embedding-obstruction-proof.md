---
rg: 2
id: higman-quotient-local-embedding-obstruction-proof
kind: route
title: The class of groups without finitely generated finite-quotient-free subgroups is closed under Chou's operations, and local embeddings transport the Higman relations
target: nontrivial-higman-quotients-are-not-locally-elementary-amenable
requires:
  - nontrivial-higman-quotients-keep-all-four-bs-subgroups
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

Call a group *bad* if it is nontrivial, finitely generated and has no nontrivial
finite quotient. A bad group `T` is perfect: `T^ab` is a finitely generated
abelian group with no nontrivial finite quotient, hence trivial. `D` is the class
of groups with no bad subgroup.

**Item 1.**
- *Residually finite groups.* Subgroups of residually finite groups are
  residually finite. A nontrivial residually finite group has a nontrivial
  finite quotient.
- *The auxiliary class.* Let `D*` be the class of groups all of whose
  subquotients lie in `D`. Then `D*` is closed under subgroups and quotients.
  Finite and abelian groups lie in `D*`, since nontrivial finitely generated
  finite or abelian groups have nontrivial finite quotients.
- *`D` is closed under extensions.* Let `K` be normal in `X` with `K` and `X/K` in
  `D`, and let `T <= X` be bad. Its image in `X/K` is finitely generated with no
  nontrivial finite quotient. So that image is trivial, `T <= K`, and `T` is
  trivial, a contradiction.
- *`D*` is closed under extensions.* Let `N` be normal in `G` with `N, G/N` in `D*`.
  Take a subquotient `X = S/M` of `G`. It has the normal subgroup
  `(S cap N)M/M`, which is isomorphic to `(S cap N)/(S cap N cap M)`, a
  subquotient of `N`. The quotient by it is a quotient of `S/(S cap N) = SN/N <= G/N`.
  So `X` is an extension of groups in `D`, and `X` lies in `D`.
- *`D*` is closed under directed unions.* Let `G` be a directed union of groups
  `G_lambda` in `D*`, and `T <= S/M` bad. Lifts of finitely many generators of `T`
  lie in some `G_lambda`, so `T` is a subquotient of `G_lambda`. Then `T` lies in
  `D`, and `T` is a bad subgroup of itself, a contradiction.
- *Conclusion.* By minimality of Chou's class, every elementary amenable group
  lies in `D*`, hence in `D`.

**Item 2.** Let `psi : Q -> Gamma` with `Gamma` in `D`. Then `psi(Q)` is finitely
generated. Its finite quotients are finite quotients of `H4`, which are trivial
by the no-finite-quotients corollary of
`nontrivial-higman-quotients-keep-all-four-bs-subgroups`. So `psi(Q)` is trivial.

**Item 3.**
- *The finite set.* Let `F` in `Q` contain `1`, the generators, their inverses,
  and every element represented by a subword of the words
  `a^-1 b a`, `b^2`, and their three rotations.
- *The partial homomorphism.* Suppose `phi : F -> Gamma` is injective with
  `Gamma` in `D`, and `phi(xy) = phi(x) phi(y)` whenever `x, y, xy` lie in `F`.
  Then `phi(1) = 1` and `phi(x^-1) = phi(x)^-1`.
- *The relations transfer.* `phi(a)^-1 phi(b) phi(a) = phi(a^-1 b a) = phi(b^2) = phi(b)^2`,
  and likewise for the other three relations. So `phi(a), phi(b), phi(c), phi(d)`
  generate a quotient of `H4` inside `Gamma`, which is trivial by item 2.
- *Contradiction.* `Q` is nontrivial, so some generator is not `1`, while
  `phi` sends it to `1 = phi(1)`. This contradicts injectivity.
