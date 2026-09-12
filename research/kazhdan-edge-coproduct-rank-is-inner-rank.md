---
rg: 2
id: kazhdan-edge-coproduct-rank-is-inner-rank
kind: claim
title: Over an amalgam with an infinite Kazhdan edge, the von Neumann rank on the coproduct of vertex division closures is the inner rank
distinct_from:
  atiyah-amalgam-rank-from-cohn-coproduct: that proves the reduction for every amalgam; this is the maximality input it names, stated for an infinite property (T) edge where no permanence framework applies.
  atiyah-kazhdan-edge-blocks-both-permanence-routes: that shows two frameworks fail at a (T) edge; this is a single ring-theoretic statement whose truth would give the permanence those frameworks cannot.
artifacts:
  - research/artifacts/atiyah-vertex-mixing-2026-09-12.md
---

**OPEN.** Let `A` and `B` be torsion-free groups with a common infinite property (T) subgroup
`C`, let `K <= C` be closed under complex conjugation, and assume `A`, `B` and `C` satisfy the
Strong Atiyah conjecture over `K`. Let `G = A *_C B`, `R = D_A *_(D_C) D_B` and
`phi: R -> U(G)` as in [[atiyah-amalgam-rank-from-cohn-coproduct]]. Then

```text
rk_G(phi(Y)) = rho_R(Y)     for every matrix Y over R,
```

where `rho_R` is the inner rank of `R`.

By [[atiyah-amalgam-rank-from-cohn-coproduct]] (4) this implies Strong Atiyah over `K` for `G`.
It is stronger than necessary: integrality needs only that `phi*rk_G` is the rank function of
some epic `R`-field, and maximality asks for the universal one.

## Attempts

- **Lück's amenable-edge dimension flatness.** Dead: `C` is nonamenable
  ([[atiyah-kazhdan-edge-blocks-both-permanence-routes]]).
- **Hughes-free division rings for locally indicable groups.** Dead: property (T) gives `C`
  finite abelianization, so `G` is not locally indicable (same node). In the locally indicable
  case that framework proves exactly this maximality, so a proof here needs a replacement for
  the Hughes-free uniqueness argument.
- **Property (T) through `L^2`-homology.** (T) gives `b_1^(2)(C) = 0` (Bekka–Valette), i.e.
  `dim Tor_1^(K[C])(N(C), K) = 0`. The Bass–Serre Mayer–Vietoris computation for a
  vertex-mixing matrix needs `dim Tor_1^(K[C])(N(C), M|_C)` for restricted modules, which (T)
  does not control.
- **Approximation by finite-dimensional representations.** (T) isolates the finite-dimensional
  representations of `C` but produces no approximation of `G`. Lück approximation needs residual
  chains or sofic approximations of `G`, and none is known for the compression-host amalgams.
- **Single-factor matrices.** Equality holds on matrices over `K[A]`, `K[B]` and `K[C]` by the
  induction formula ([[atiyah-amalgam-unmixed-matrices-reduce-to-factors]]). So the content is on
  alternating products of elements from `D_A \ D_C` and `D_B \ D_C`.
- **Counterexample side.** A failure needs a full matrix over `R` whose image in `U(G)` is not
  invertible, and non-integrality needs strict deficiency with a non-integer value. No
  construction of either is known.
