---
rg: 2
id: kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers
kind: claim
title: A Bernoulli deficit witness over a finite-lamp wreath with residually finite actor must see a profinitely non-closed stabilizer
distinct_from:
  sofic-radical-localizes-bernoulli-deficit-witnesses: that says every witness folds on a sofic-invisible element of the subgroup it generates; this makes the condition explicit for permutational wreaths with abelian lamps and residually finite actor, as nonamenability of the actor image plus a non-closed site stabilizer.
  kun-thom-wreath-bernoulli-rokhlin-maximal: that is the open maximality question over the Kun--Thom wreath; this is a necessary condition any deficit over it must meet.
artifacts:
  - research/artifacts/kun-thom-wreath-rokhlin-test-case-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be residually finite, `X` a `G`-set, `B` a nontrivial finite abelian group,
`W = B^(X) ⋊ G`, and `π: W -> G` the projection. Let `(k, E, F, ψ)` be a configuration over `W`
with `Φ < log q` (`bernoulli-rokhlin-deficit-has-a-finitary-witness`), and `K = <E ∪ F>`. Then:

1. `π(K)` is nonamenable;
2. some site in the lamp supports of `E ∪ F` has stabilizer in `π(K)` that is not closed in the
   profinite topology of `π(K)`.

*Proof sketch.* `K` lies in `B^(O) ⋊ π(K)`, where `O` is the union of the `π(K)`-orbits of those sites.
- If `π(K)` is amenable, `K` is amenable.
- If every orbit stabilizer is closed, summing lamps over the fibres of `O -> π(K)/(S_i Δ)` gives
  finite quotients that separate points, so `K` is residually finite.

Either way `K` is sofic and carries no witness. Section 4 of the artifact.

**For the Kun--Thom wreath** `(Z/2) wr_(G/Γ) G`, a deficit must generate a subgroup where the
profinite non-closedness of `Γ` is visible. The sofic radical lies in the lamp configurations with zero
sum on every fibre of `G/Γ -> G/Γ̂`, where `Γ̂` is the profinite closure; the rigid defect is one of
them.

**ESTABLISHED 2026-09-12** by [[kun-thom-wreath-deficit-nonclosed-stabilizer-proof]].
