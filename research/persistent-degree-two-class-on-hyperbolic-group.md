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
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
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

[[finite-hyperbolic-residual-iff-persistent-class]] proves an exact
equivalence: this approach succeeds if and only if some word-hyperbolic
group has a finite nontrivial finite residual. More generally,
[[finite-kernel-nonrf-has-central-prime-reduction]] shows that an arbitrary
non-residually-finite finite-kernel extension of an RF hyperbolic base
already supplies a prime central example over a finite-index subgroup of
that base. These are conditional reductions; the existence question
remains open. They do not cover a counterexample whose residual is infinite.

## Attempts

- **Arithmetic, via a finite congruence kernel.**  Hill's construction gives
  non-residually-finite finite central extensions of arithmetic groups whose
  congruence kernel is finite.  A cocompact arithmetic lattice in a rank-one
  group is hyperbolic, so a finite congruence kernel there would finish the
  problem immediately. The required finite congruence kernel is not established
  for the quaternionic rank-one candidates used here; the Sp(2,1) nodes keep
  it open. Failure of the congruence subgroup property in other rank-one
  families is not a theorem for every rank-one arithmetic lattice. Hill
  explicitly formulates general rank-one infinitude conjecturally; see the
  source audit in `research/artifacts/hyperbolic-rf-alternatives-2026-09-20.md`.  The 2026 work of
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
- **Not attempted here:** any construction of a general hyperbolic group
  designed to have such a class.  For general hyperbolic groups this graph has
  no technique for controlling `H^2` along the whole finite-index subgroup
  lattice.
- **Triangle colimits (2026-09-13, lane ex-hyperbolic-triangle-theory).**
  `edge-twist-extensions-of-triangle-colimits-moment-test` supplies such a
  technique for one explicit family.
  - Twisting the edge embeddings of a nonpositively curved triangle of finite
    groups by homs `E_e -> C_p` gives hyperbolic central extensions `Λ_c`.
  - `Λ_c` splits over a torsion-free normal `N` iff a linear first-moment
    identity holds on the `F_p` 2-cycles of `N\X`.
  - The moment spaces decrease along covers and only `p`-covers change them.
  - When the vertex groups are perfect with Schur multiplier prime to `p`, these
    twists exhaust `H^2(Λ;F_p)`.
  First-level data (`hyperbolic-triangle-colimit-with-persistent-edge-twist`):
  in nine hyperbolic `PSL(2,q)` coset triangles with `C_5` or `C_7` edges, no
  nonzero twist splits over the first kernel `N`, and `b_1(N;F_p) = 0`. This does
  not assume residual finiteness of the colimit; route
  `non-rf-hyperbolic-via-persistent-edge-twist`.
