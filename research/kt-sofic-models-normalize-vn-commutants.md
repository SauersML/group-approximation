---
rg: 2
id: kt-sofic-models-normalize-vn-commutants
kind: claim
title: Sofic models of an infranormal Kazhdan pair normalize their whole von Neumann Gamma-commutant
distinct_from:
  kun-thom-sofic-centralizer-normalization: that normalizes only the permutation centralizer in the universal sofic group; this asks the same permutation model to normalize every operator of the matrix ultraproduct commuting with sigma(Gamma).
  kt-centralizer-normalization-hs: that quantifies over all trace-preserving unitary models; this keeps sigma permutation-valued, so Kun's expander decompositions and the Kun--Thom cluster calculus remain available for the model while the commutant is linear.
  kt-canonical-hs-normalization-fails: that is the existence of some Connes-embeddable counterexample model; a sofic counterexample to this claim at the Theorem E pair would be one.
  kt-sofic-monomial-commutant-core-is-normalized: that proves normalization on the monomial core; this is the full commutant, where the open content is the part orthogonal to that core.
---

**OPEN.** Let `Gamma < G` be infranormal with `Gamma` and `G` Kazhdan, and let
`sigma : G -> S_U` be an injective sofic representation with canonical trace,
realized by permutation matrices in `M = prod_U M_n`. Then `sigma(G)` normalizes
`R = sigma(Gamma)' cap M`.

**Position.**
- It sits strictly between two statements: Kun--Thom 4.1, which normalizes
  `C_(S_U)(sigma(Gamma))`, and `kt-centralizer-normalization-hs`, which implies it
  (route `kt-sofic-models-normalize-vn-commutants-from-hs-normalization`).
- **If it fails** at some pair, `H = <sigma(G), z> <= U(M)` is hyperlinear and carries a
  nontrivial rigid defect, so it is nonsofic
  (`rigid-compression-defect-normalization-dichotomy`,
  `sofic-groups-kill-rigid-compression-defects`), and Question 3.4 is answered
  negatively. At the Theorem E pair the model is an instance of
  `kt-canonical-hs-normalization-fails`.
- **If it holds**, it strengthens Kun--Thom 4.1 from permutation centralizers to
  von Neumann commutants. Every Question 3.4 witness produced by commutant
  failure would then need an actor model that is not permutation-valued, although
  the canonical models of the residually finite actor are permutation models.

## Attempts

- **Monomial core.** Proved: `kt-sofic-monomial-commutant-core-is-normalized`.
  Kun--Thom 4.1, together with a doubling of the model for invariant diagonal
  projections, normalizes `N_sigma = (C_(S_U)(sigma(Gamma)) union (D cap R))''`. A
  witness can be taken in `R`, orthogonal to `N_sigma`. What remains is exactly the
  non-monomial part of the commutant.
- **Schur structure is where permutation structure enters.** Conjugation by a
  permutation commutes with entrywise operations on matrices, and a general unitary
  does not. For a unitary `z in R`, the entrywise square `|z|^(o2)` is doubly
  stochastic, and

  ```text
  (1/n) sum_(y',y) | |a_(y'y)|^2 - |z_(y'y)|^2 |  <=  2 ||a - z||_2,
  a = sigma_n(gamma) z sigma_n(gamma)^-1,  and  |a|^(o2) = sigma_n(gamma)|z|^(o2) sigma_n(gamma)^-1.
  ```

  So `|z|^(o2)` is a `Gamma`-almost invariant self-coupling of the uniform measure,
  and its transport by `sigma(t)` is `|sigma(t) z sigma(t)^*|^(o2)`. Normalization therefore
  splits into (i) a doubly stochastic analogue of Kun--Thom 4.1, which for
  permutation matrices is 4.1 itself, and (ii) a phase problem, since the modulus
  loses phases: every diagonal unitary has `|d|^(o2) = 1`. Neither half is
  settled. Birkhoff decompositions of `|z|^(o2)` do not respect `Gamma`-invariance, so
  (i) does not reduce to 4.1 term by term.
- **Reduction to rounding sofic approximations (Theorem E pair).** An injective sofic
  representation with canonical trace is a trace-preserving model. So the per-model unit-type
  chain applies to it: `nonunit-projection-bounded-by-root-spectral-mass`,
  `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`,
  `vertex-rounding-deep-nonunit-root-mass-vanishes` and
  `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`, as assembled in
  `kt-hyperlinear-coset-wreath-forces-nonroundable-vertex-proof`, Step 3. So this claim holds
  for the Theorem E pair as soon as every sofic model of `G` satisfies (H1) on the vertex: its
  permutation asymptotic action of `Gamma` must flexibly round to genuine unitary
  representations. That is weaker than rounding to genuine permutation actions, and nothing in
  the graph excludes it. For the Fournier--Facio pair the claim is vacuous: the
  group is nonsofic, and rounding fails at every faithful model
  (`fournier-facio-vertex-rounding-fails-at-every-model`).
- **Exact coordinates.** Coordinatewise genuine permutation actions normalize, as
  genuine finite-dimensional coordinate models
  (`ccr-holds-for-all-genuine-fd-coordinate-models`). A witness needs
  positive-density non-exactness of `sigma` itself, not only of `z`.
- **The core and its bicommutant.** An ultraproduct of right group algebras of
  finite quotients contains Fourier-spread projections which are not 2-norm limits
  of bounded combinations of centralizer permutations and invariant diagonals, so
  `N_sigma` is expected to be proper in `R` even for exact regular models (unproved).
  The relative bicommutant `A_sigma` of the core repairs this. It is also normalized
  (item 4 of `kt-sofic-monomial-commutant-core-is-normalized`), and through the
  Alekseev--Thom genuine centralizer groups it contains `prod_U C[A_n]`. Hence:

  ```text
  (DENS)  R = A_sigma, i.e.  R' cap M = (C_(S_U)(sigma(Gamma)) union (D cap R))' cap M
  ```

  implies normalization for `sigma`. (DENS) is Alekseev--Thom Open Problem 6.2(a) for
  the sofic model of `Gamma`, with the coordinate algebras prescribed as group algebras
  of the permutation centralizers. It is not covered by
  `at-op62-holds-for-representation-lifts`: that instance needs genuine unitary
  representation lifts of `Gamma`, while a non-exact sofic model supplies only
  asymptotic permutation actions. Under (DENS) the model is in the finite-dimensional
  setting of `wall-coordinate-reduction-under-at-op62`.
- **(DENS) is stronger than needed.** Already at coordinate level it fails for exact
  transitive models `Q ↷ Q/Delta` with `Delta` not normal: the commutant is the Hecke
  algebra `C[Delta\Q/Delta]`, while the centralizer group algebra is `C[N_Q(Delta)/Delta]`.
  Normalization still holds there, because the finite image of `Gamma` is normal. So
  the Hecke content of `R` needs a mechanism other than permutation density. Large-girth
  `Delta` keep the canonical trace, so canonical-trace exact models carry it too
  (coordinate-level remark, not transferred to the ultraproduct).
- **Literature check (bounded).** Alekseev--Thom, arXiv:2608.05362, read from the arXiv
  HTML on 2026-09-12 on MSI. Theorem 3.1 (verbatim): "Let G be a Kazhdan group and let
  π:G→∏_𝒰 Sym(X_n) be a sofic embedding represented by homomorphisms α_n:F_S→Sym(X_n).
  Then there exist an essentially equivalent sofic embedding π′:G→∏_𝒰 Sym(Y_n), and
  subgroups A_n≤Sym(Y_n) such that C_{∏_𝒰 Sym(Y_n)}(π′(G))=∏_𝒰 A_n." Proposition 4.5
  represents centralizer elements by bisections of the cluster groupoid, and Proposition
  5.1 upgrades them to genuine homomorphisms by Becker--Chapman. The paper states no
  result on the von Neumann or unitary commutant of a sofic embedding; Open Problem
  6.2 asks about arbitrary unitary representations. No other source was checked.
