---
rg: 2
id: random-complex-mid-range-group-is-perfect
kind: claim
title: Mid-range Linial--Meshulam groups are perfect, so they have no nontrivial abelian quotient of any order
distinct_from:
  random-complex-group-no-quotients-below-exp-pn: that excludes every finite quotient of order at most exp(pn/8) by counting cochains; this excludes abelian quotients of every order through integral homology, including cyclic groups of prime order far beyond where counting works
  random-complex-group-no-quotients-above-exp-pn: that is the open claim excluding every finite quotient above exp(n^eta/8); this is proved, and excludes only the abelian ones, at every order
  meshulam-random-complex-no-polynomial-quotients: that excludes quotients of polynomial order; this excludes abelian quotients of all orders and says nothing about nonabelian ones
  random-complex-mid-range-pair-properties: that collects hyperbolicity, nontriviality and local expansion; this is vanishing of integral first homology, a property on the profinite side that those do not give
artifacts:
  - research/artifacts/nrfh-kazhdan-quotientless-2026-09-12.md
---

**ESTABLISHED (literature import).** C. Hoffman, M. Kahle and E. Paquette,
*The threshold for integer homology in random d-complexes*, arXiv:1308.6232v2
(10 Apr 2014). Theorem 1 (p. 3), read from the PDF on 2026-09-12:

> Let d ≥ 2 be fixed and Y ~ Y_d(n,p). If p ≥ 80d log n / n then
> H_{d−1}(Y;Z)=0 w.h.p.

Here `Y_2(n,p)` is the Linial--Meshulam model (their p. 1): complete 1-skeleton
on `n` vertices, with each triangle present independently with probability `p`.

The sharp threshold is `2 ln n / n`. This is T. Łuczak and Y. Peled, *Integral
homology of random simplicial complexes*, arXiv:1607.06985v1, Theorem 1 (p. 3),
proved as a hitting-time statement for the random 2-complex process. Only the
cruder bound of Hoffman--Kahle--Paquette is used below.

**Mid-range form.** Let `0 < η < 1` and `p = n^(-1+η)`.
- For all large `n`, `p >= 160 log n / n`, so a.a.s. `H_1(Y;Z) = 0`.
- `Y` is connected, so `H_1(Y;Z) = π_1(Y)^ab`.

Hence a.a.s. `π_1(Y)` is perfect, and every homomorphism from `π_1(Y)` to an
abelian group is trivial. In particular `π_1(Y)` has no quotient `Z/ℓ` for any
prime `ℓ`, however large.

**What it changes.**
- **The cyclic case is closed.** "What is left" in
  `random-complex-group-no-quotients-above-exp-pn` listed cyclic quotients. A.a.s.
  every finite simple quotient of `π_1(Y)` is nonabelian, so none remain.
- **Calibration.** Hoffman--Kahle--Paquette (p. 2) note that the Meshulam--Wallach
  counting argument does not handle `Z/q` coefficients with `q` growing
  superpolynomially in `n`. For abelian quotients the counting barrier at
  superpolynomial order was real, and the integral theorems go past it. The
  corresponding barrier for nonabelian quotients is in the artifact, §2.2.

CITATION
random-complex-mid-range-group-is-perfect-citation
