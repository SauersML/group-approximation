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
- **Exact coordinates.** Coordinatewise genuine permutation actions normalize, as
  genuine finite-dimensional coordinate models
  (`ccr-holds-for-all-genuine-fd-coordinate-models`). A witness needs
  positive-density non-exactness of `sigma` itself, not only of `z`.
- **Expected excess, unproved.** Even in exact regular congruence models the core
  should be a proper subalgebra of `R`. An ultraproduct of right group algebras of
  the finite quotients contains Fourier-spread projections which are expected not
  to be 2-norm limits of bounded combinations of centralizer permutations and
  invariant diagonals. If so, Kun--Thom's permutation calculus cannot reach `R` even
  where normalization is known, and the linear content has to come from elsewhere.
