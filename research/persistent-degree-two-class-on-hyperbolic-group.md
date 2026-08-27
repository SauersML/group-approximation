---
rg: 2
id: persistent-degree-two-class-on-hyperbolic-group
kind: claim
title: A degree-two class on a residually finite hyperbolic group that survives every finite-index subgroup
distinct_from:
  finite-infranormal-subgroup-is-normal: that is an elementary normalizer lemma — a finite subgroup whose compression semigroup generates the group is normal; this is a cohomological persistence statement about degree-two classes over the whole finite-index subgroup lattice, and the shared vocabulary of "finite" and "index" is coincidental
  finite-central-extension-rf-iff-virtually-splits: that is the established criterion converting persistence into failure of residual finiteness; this is the cohomological existence statement the criterion consumes, and it is open
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Produce a residually finite word-hyperbolic group `H`, a prime `p`, and a
class

```text
0 != α in H^2(H; C_p)
```

such that `res^H_(H_0)(α) != 0` for **every** finite-index subgroup
`H_0 ≤ H`.

By `finite-central-extension-rf-iff-virtually-splits` the associated central
extension `E_α` is then not residually finite, and it is hyperbolic because a
finite extension of a hyperbolic group is hyperbolic.  So this is a complete
counterexample target, stated entirely in cohomology.

## Attempts

- **Arithmetic, via a finite congruence kernel.**  Hill's construction gives
  non-residually-finite finite central extensions of arithmetic groups whose
  congruence kernel is finite.  A cocompact arithmetic lattice in a rank-one
  group is hyperbolic, so a finite congruence kernel there would finish the
  problem immediately.  That input is exactly what rank one does not supply:
  the congruence subgroup property fails badly for rank-one lattices, which is
  the same reason they have many finite-index subgroups.  The 2026 work of
  Rapinchuk on `S`-arithmetic groups with `S` of positive Dirichlet density
  does not reach cocompact rank-one lattices.
- **Ball quotients.**  The natural rank-one candidates are cocompact lattices
  in `SU(n,1)`, which are hyperbolic and residually finite.  Stover,
  *Cohomological nonvanishing for algebraic fundamental groups of ball
  quotients*, arXiv:2508.20847 (28 August 2025; the external attempt this node
  ingests cites an August 2026 revision, which the arXiv listing did not
  confirm on 2026-08-17 — it lists v1 only), pushes the wrong way for this
  purpose: for congruence lattices the restriction from the profinite
  completion is almost surjective in low degrees, i.e. the classes are in the
  profinite image, and by the profinite half of
  `finite-central-extension-rf-iff-virtually-splits` those extensions are
  residually finite.
- **Where a persistent class must live.**  Outside the image of
  `H^2_cont(H_hat; C_p) → H^2(H; C_p)`.  That is a sharp requirement and it is
  also the reason the search is not merely unfinished: for every family where
  the comparison map is understood, it is understood to be surjective enough
  to kill persistence.
- **Not attempted here:** any construction of a hyperbolic group designed to
  have such a class.  This graph has no technique for controlling `H^2` of a
  hyperbolic group along its whole finite-index subgroup lattice, and does not
  pretend to.
