---
rg: 2
id: stw99-problem-xxxviii-noncommutative-crossed-z-stable
kind: claim
title: Outer actions of amenable groups on Z-stable stably finite algebras give Z-stable crossed products (STW Problem XXXVIII)
root: true
distinct_from:
  stw99-problem-xxxix-szabo-equivariant-z-stability: that is Szabo's stronger conjecture on the ACTION (equivariant Z-stability, no outerness); this asks only for Z-stability of the crossed product, and follows from it (route stw99-xxxix-implies-xxxviii).
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

**Problem XXXVIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(their "when is..." question, recorded in the closed form its known
positive cases suggest): for every outer action of a countable discrete
amenable group `G` on a unital simple separable nuclear `Z`-stable
stably finite C\*-algebra `A`, the crossed product `A ⋊ G` is
`Z`-stable.  Open even for `G = Z`.

Known: Kirchberg-algebra targets (always, via
Kishimoto--Kumjian-type pure infiniteness + Kirchberg absorption);
Rokhlin `Z`-actions (Hirshberg--Winter); polynomial-growth groups with
finite Rokhlin dimension (SWZ); strongly outer actions of elementary
amenable groups when `∂_e T(A)` is finite (Matui--Sato's weak Rokhlin +
(SI)).

## Attempts

* The non-amenable-`G` variant of STW's question collapses to
  tracelessness: a trace on `A ⋊_r G` restricts to a `G`-invariant
  trace on `A`, whose GNS crossed product would be finite injective
  (amenable action) and contain `L(G)` with expectation — impossible
  for non-amenable `G`.  So for non-amenable `G` the crossed product
  is traceless and the question merges into the traceless
  `Z`-stability problem; the stably finite content of XXXVIII is
  amenable `G`, as encoded.
* Beyond Matui--Sato the obstruction is the SAME wild-trace-simplex
  glueing isolated across XXI/XXVIII/XXX: their weak Rokhlin property
  lives fibrewise over `∂_e T(A)` and (SI) globalizes it only through
  finitely many extremal traces; CPoU (which would do arbitrary
  compact boundaries) is available exactly when uniform Γ is — and `A`
  `Z`-stable DOES have uniform Γ, so the missing step is an
  EQUIVARIANT CPoU: complemented partitions of unity in the fixed
  point/central sequence algebra of the action.  Recorded as the sharp
  frontier; Szabo's conjecture (XXXIX) is the systematic version.
