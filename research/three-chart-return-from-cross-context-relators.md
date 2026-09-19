---
rg: 2
id: three-chart-return-from-cross-context-relators
kind: route
title: Two cross-context radical relators make the endpoint events word-level
target: three-chart-affine-clifford-return-incidence
requires:
  - covariant-model-satisfies-cross-context-radical-relators
  - every-predicate-has-s3-equivariant-raw-radical-drop
  - three-radical-twist-crossed-products-have-uniform-scale
  - fanizza-radical-charts-admit-common-symplectic-reset-subgroups
  - derived-lifted-gauge-reset-spin-bridge
  - rank-one-no-signaling-pairing-floor
---

Quotient the affine Clifford return presentation by the two cross-context
radical relators `(CCR1)`.  Everything the target asks for then follows
from established finite facts plus the single covariant-model obligation.

**Word-level events.**  Set `t_X = u_beta r_(a,0) u_beta^(-1)` and
`t_Y = u_beta r_(a,1) u_beta^(-1)`.  After a complete semantic character
is fixed, the central value of `J` is a known sign and the squares of the
`r`-words are pinned central elements, so the corrected spectral
projections `P = (1+chi t_X)/2` and `Q = (1+chi' t_Y)/2` are defined.  By
`(CCR1)`, the alpha-side X-event and the gamma-side Y-event are the SAME
group words as `t_X,t_Y` up to fixed central signs.  In any
finite-dimensional tuple of total relator energy `E`, every word-image
differs from its relator-mate by `O(sqrt(E))` in normalized HS: the three
binary endpoint events of `(RNS1)` are represented by the same two
projections `P,Q` up to `O(sqrt(E))`.  This is exactly the multiplicity
holonomy constraint the target isolates: the loop form `(CCR2)` kills the
independent commutant rotations `V_i` because the events are no longer
chosen projections at all — they are images of fixed words.

**The events live in the fresh multiplicity algebra.**  On the marked
forbidden carrier both `r_(a,j)` lie in the radical of `A_f(a)`, hence
commute sector-centrally with the fixed hyperplane subgroup `L` of
`(CHR3)`; their transports therefore commute with the shared fresh edge
image up to `O(sqrt(E))`, i.e. `P,Q` sit in the merged `2 rho_15` type's
multiplicity commutant, as required.  Moreover
`[r_(a,0),r_(a,1)] = J^(A_f(a)(r_0,r_1)) = 1` sector-centrally on the
marked atom, so `[P,Q] = O(sqrt(E))` there and the joint masses
`p_00,p_01,p_11` are defined up to `O(sqrt(E))`.

**The floor.**  The endpoint marginals of the three contexts now agree up
to `O(sqrt(E))` because they are traces of the SAME projections against
the same carrier: `(RNS1)` holds within `O(sqrt(E))`.  The telescoping
proof of `(RNS2)` in `rank-one-no-signaling-pairing-floor` is stable
under an additive marginal perturbation: with marginal mismatch `eps`,

```text
p_00+p_01+p_11 >= 1 - 2 eps.
```

Integrating over the marked forbidden carrier of normalized mass `q`
gives

```text
p_00+p_01+p_11 >= q - O(sqrt(E)),                       (TCR1)
```

and every failure mass traces to a violated relator of the quotiented
presentation — the packet relators, the edge relators, or `(CCR1)` — all
of which are summands of `E`.  So the failure is charged to relator
energy, which is the second half of the target statement.

**Completeness.**  The quotient admits the countably amplified exact
HALT representation and embeds its marked base — this is precisely
`covariant-model-satisfies-cross-context-radical-relators`, the one open
requirement.  On the honest model the forbidden carrier is unpopulated
(`q=0`), so `(TCR1)` is vacuous there and no frustration is inherited.

**Why this evades the recorded dead ends.**  No common fresh vertex is
used, so the `I tensor V_i` counterexample never arises; no
`S_3`-semidirect edge closure audit is needed, in contrast to
`s3-equivariant-edge-closes-common-marginals`; and only the two
`(RNS1)`-required identifications are imposed, so no old selector
character is identified across contexts and the reset discipline of
`fresh-selector-renewal-after-symplectic-chart-reset` is untouched.
