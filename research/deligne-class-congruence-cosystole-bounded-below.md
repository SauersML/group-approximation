---
rg: 2
id: deligne-class-congruence-cosystole-bounded-below
kind: claim
title: The Deligne class restricted to congruence subgroups of Sp_4(Z) has normalized Hamming cosystole bounded below on the congruence covers
distinct_from:
  gohla-thom-class-norm-drops-under-weak-containment: that imports cosystolic inequalities known for p-adic Bruhat--Tits quotients, for all classes; this asks for one class on real rank-2 arithmetic covers, where no expansion theorem is known.
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-sofic-transfer-and-sp4-2026-09-13.md
---

**OPEN.** Setup:
- `alpha in H^2(Gamma(3), Z/3)` is the restriction of the class of Deligne's triple cover of `Sp_4(Z)`.
- `BGamma(3)` is a fixed finite model, and `BGamma(m)` is its covering model for `3 | m`, with Gohla--Thom's normalized
  cell weights.

There are `eps > 0` and a descending chain `m_1 | m_2 | ...` with `Gamma(m_k)` intersecting trivially, such that every
2-cocycle on `BGamma(m_k)` cohomologous to `alpha|Gamma(m_k)` is nonzero on at least an `eps`-fraction of the 2-cells.

**Well posed.** Changing the model or the weights changes the fraction only up to bi-Lipschitz constants, by
Gohla--Thom Section 2.2. By their Lemma 2.5, the fraction is the norm of `alpha` on the finite action
`Gamma(3)/Gamma(m_k)`.

**Payoff.** It implies `deligne-triple-cover-no-weakly-bernoulli-liftable-action`, through the profinite action of
the chain and Bernoulli maximality.

**Model test.**
- A virtually split class fails the statement. Once it vanishes on some `Gamma(m)`, the cosystole is 0 from then on.
- For torsionfree lattices in `PSp_2d(Q_p)` with `d >= 4`, the analogous bound holds for every class (Gohla--Thom Theorem
  2.10).
- Deligne's theorem makes `alpha|Gamma(m) != 0` for every `m`, so the claim is not vacuous.

## Attempts

- **Property (T) (ex2-rokhlin-almost-cocycle, 2026-09-13).** It gives cosystolic inequalities in dimension 1 only:
  small representatives of `H^1(Λ, A)` classes contradict uniform expansion of Schreier graphs. Dimension 2 needs
  local-to-global expansion. Gohla--Thom get it from Kaufman--Mass on buildings, and no such link structure is known
  for `Gamma(m)\Sp_4(R)/U(2)`.
- **Cycle packing.** Detecting 2-cycles are surfaces with every essential loop of length at least the injectivity
  radius `~ c log m`, so they need `>~ (log m)^2` cells. Disjoint packings therefore give only `cosys >~ (log m)^-2`,
  which tends to 0.
- **Local patching (heuristic, supports the claim).** Trivializing on pieces below the injectivity radius leaves
  mismatches near the walls. Walls of a tiling of a non-amenable symmetric space carry a constant fraction of the
  volume. Non-local constructions are not excluded.
