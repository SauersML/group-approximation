---
rg: 2
id: finite-residual-transports-across-commensurability
kind: claim
title: The finite residual is a commensurability invariant, and comparing residuals separates groups
distinct_from:
  mf-is-commensurability-invariant: that is the analogous statement for the MF property itself, a yes-or-no predicate; this is about the residual *subgroup* as an object, and its content is that the object can be compared across an isomorphism of finite-index subgroups.
  corona-finite-index-radical-heredity: that is the finite-index heredity of the corona MF radical, an analytic radical; this is the purely group-theoretic finite residual, and the two coincide only under extra hypotheses recorded elsewhere.
  alternating-lamp-noncommensurable-family: that is the family this criterion is applied to, and its separation argument consumes this claim; this claim knows nothing about any particular group.
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Algebra/FiniteResidualCommensurability.lean
---

Three transport facts about the finite residual, jointly the separation
criterion that noncommensurability arguments consume:

- **finite index changes nothing.**  For a finite-index subgroup `K <= G`, the
  finite residual of `K` is literally the trace of the ambient one:
  `Res_fin(K) = Res_fin(G) ∩ K`, as subgroups of `K`;
- **isomorphisms carry residual onto residual.**  An isomorphism `G ≅ H` maps
  `Res_fin(G)` onto `Res_fin(H)`, so the two residuals are isomorphic as groups;
- **hence the criterion**, in both the forms an application needs: if the
  residuals are non-isomorphic then the groups are non-isomorphic, and — using
  the first fact — no finite-index subgroup of one is isomorphic to a
  finite-index subgroup of the other.

Sections 49--52 of the dossier use this mechanism repeatedly; it is Lemma 49.4 in
subgroup form together with the full-invariance statement 50.1, packaged as the
comparison the separation argument actually invokes.

## Why the packaging matters

Nothing here knows the residual of any particular group; that is the job of a
radical computation.  This claim is the **transport**, and separating it out is
what makes the noncommensurability arguments short: once the residual is
identified for each member of a family, distinguishing the members up to
commensurability reduces to distinguishing the residuals up to isomorphism —
with the finite-index step already discharged, and with no need to track how a
hypothetical isomorphism between finite-index subgroups was built.

For an arbitrary subgroup `K <= G`, the immediate inclusion is
`Res_fin(K) <= Res_fin(G) ∩ K`: every finite homomorphism of `G` restricts
to one of `K`. The converse uses finite index. Every finite-index subgroup
of `K` then has finite index in `G`, so it contains `Res_fin(G)`; intersect
these subgroups to obtain the equality. A finite homomorphism of an
arbitrary subgroup need not extend to the ambient group, so this converse
is not asserted without finite index.
