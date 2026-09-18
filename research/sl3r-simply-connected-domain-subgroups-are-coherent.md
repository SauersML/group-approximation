---
rg: 2
id: sl3r-simply-connected-domain-subgroups-are-coherent
kind: claim
title: A subgroup of SL_3(Z) acting properly on a simply connected open set in the plane, the dual plane or the flag manifold is coherent
distinct_from:
  sl3z-incoherence-witnesses-are-zariski-dense-thin: that excludes witnesses through Zariski closures and trees; this excludes witnesses through proper actions on domains of the projective plane and the flag manifold
  sl3z-parabolic-subgroups-are-coherent: that treats subgroups with a fixed rational point or line; this treats Zariski-dense subgroups with a simply connected domain of discontinuity
  two-dimensional-coxeter-coherence-criterion: that is an abstract criterion for Coxeter groups; this is a geometric obstruction for linear actions in rank three
---

Let `H <= SL_3(R)` be finitely generated and virtually torsion-free, and let
`M` be one of

- the projective plane `RP^2`,
- the dual projective plane `(RP^2)^*`,
- the full flag manifold `F = SL_3(R)/B` (dimension three),
- `R^3 \ {0}`.

If `H` preserves a connected, simply connected open subset `Omega` of `M` and
acts properly discontinuously on it, then `H` is coherent. More precisely,
every finitely generated subgroup of `H` is virtually free, virtually a
surface group, or virtually the fundamental group of a 3-manifold, and so it
is finitely presented. Every finitely generated subgroup of `SL_3(Z)` is
virtually torsion-free by Selberg's lemma.

**Consequences for Serre's question.** Let `K <= SL_3(Z)` be finitely
generated and not finitely presented, or let `K` contain such a subgroup.
Then no subgroup of `K` containing that witness has a simply connected domain
of discontinuity in `RP^2`, `(RP^2)^*`, `F` or `R^3 \ {0}`. In particular:

- (i) `K` preserves no properly convex open subset of `RP^2`. So no
  incoherence witness is a convex projective (divisible or non-divisible)
  group. A witness also preserves no convex open subset of an affine chart
  that is not properly convex: such a set has a finite invariant set of
  projective lines, so a finite-index subgroup of `K` fixes a line and `K`
  is not Zariski dense, which `non-zariski-dense-subgroups-of-sl3z-are-coherent`
  excludes.
- (ii) If a Coxeter group `W` has a faithful reflection representation in
  `GL_3(Z)` whose image acts properly on the interior of its Tits cone, as
  under Vinberg's hypotheses, then `W` is coherent. Faithfulness of an
  incoherent reflection subgroup of `GL_3(Z)` cannot be certified by
  Vinberg's theorem, bending or any other convex-domain argument.
- (iii) For a projective Anosov witness, any Kapovich–Leeb–Porti domain of
  discontinuity in `F` is not simply connected. This complements the
  Canary–Tsouvalas lead recorded on
  `sl3z-contains-rfrs-cd2-subgroup-with-positive-b2`.

The `R^3 \ {0}` and `F` cases add something: `H` may act properly on a
3-dimensional domain without preserving any domain of `RP^2`.

**ESTABLISHED 2026-09-17** by
[[sl3r-simply-connected-domain-subgroups-are-coherent-proof]].
