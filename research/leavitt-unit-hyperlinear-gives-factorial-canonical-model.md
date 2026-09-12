---
rg: 2
id: leavitt-unit-hyperlinear-gives-factorial-canonical-model
kind: claim
title: A hyperlinear binary Leavitt unit group has a canonical matrix model with factorial global commutant
distinct_from:
  leavitt-unit-has-no-factorial-canonical-model: that asserts nonexistence of factorial canonical models; this asserts their existence whenever any canonical model exists, and the two together are nonhyperlinearity.
  binary-leavitt-unit-group-hyperlinear: that asks for a faithful model; this upgrades any faithful model to one whose global commutant is a factor.
---

**OPEN.** Let `H = L_(F_2)(1,2)^x`. If `H` is hyperlinear, some homomorphism
`pi : H -> U(prod_omega M_(d_n))` with regular trace has a factor as global
commutant `pi(H)' cap prod_omega M_(d_n)`.

This is the factorial commutant embedding problem for the property (T)
factor `N = L(H)`, in matrix-ultraproduct form. By the full character
simplex, hyperlinearity of `H` is exactly embeddability of `N`.

## Attempts

- **Brown's extreme points.** Brown, arXiv:1010.1214, Proposition 5.2: an
  embedding class in `Hom(N, R^omega)` is extreme exactly when its commutant
  is a factor.
  - The theorem is for `R^omega` (and McDuff ultrapowers, following
    Atkinson). No source extends it to `prod_omega M_n`.
  - Existence of extreme points is open. Goldbring, arXiv:2003.10004,
    Question 1.1 calls it "open for the class of property (T) factors".
    Kunnawalkam Elayavalli, arXiv:2511.20377v3, Problem 37.
  - The withdrawn Brown--Capraro preprint arXiv:1010.6033 is not a source.
- **Character rigidity plus finite-dimensional irreducible representations.**
  Popa, arXiv:1308.3982, Section 1, uses Bekka's operator-algebraic
  superrigidity. For `PSL(n,Z)`, `n >= 3`, irreducible representations of
  unbounded dimension generate a copy of the group factor with trivial
  relative commutant in `prod_omega M_(k_m)`.
  - `H` has the character rigidity (`binary-leavitt-full-character-simplex`).
  - It has no nontrivial finite-dimensional representations
    (`binary-leavitt-unit-group-is-minimally-almost-periodic`), so no such
    sequence exists.
  - Dead for `H`.
- **The trivial-commutant form is also open.** Kunnawalkam Elayavalli,
  arXiv:2511.20377v3, Problem 2, the ergodic Connes embedding problem
  credited to Ioana and Popa, asks for `N' cap prod_U M_n = C` for every
  embeddable non-Gamma II_1 factor `N`. Property (T) factors are full
  (standard, Connes; not re-read at source). A positive answer for `L(H)`
  would imply this claim.
- **Free group factor targets.** Peterson, arXiv:2605.16669v1, Theorem 1.3:
  a property (T) subfactor of `(LF_n)^U` with factorial relative commutant
  lies in an ultraproduct of finite-dimensional subfactors. The target is
  different, and the result gives neither existence nor internality in
  `prod_omega M_n`.
- **Positive 1-bounded entropy.** The trivial-commutant constructions of
  Jekel and of Hayes--Jekel--Kunnawalkam Elayavalli need `h(N) > 0`. Kazhdan
  factors are strongly 1-bounded. Dead for `H`.
- **Finite centre.** Atkinson, arXiv:1608.08189, Corollary 1.3 turns an
  embedding into `R^omega` with finite-dimensional commutant centre into a
  factorial one. It needs such an embedding first, and it lives in `R^omega`.
  Open for `H`.
- **Component selection.** Uniform rounding of the global heat selects a
  scalar-commutant model
  (`research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md`,
  Section 2). Using it here is circular, because that rounding is the premise
  the single-use route is meant to avoid.
