---
rg: 2
id: literal-group-sofic
kind: claim
title: Soficity of the literal finitely presented non-MF group
root: true
invalidates: [literal-nonsofic-via-stable-central-quotient]
distinct_from:
  sofic-non-mf-witness: That established claim proves soficity of the quotient witness W; this claim asks whether the finitely presented source E itself is sofic.
  torsion-free-finitely-presented-non-mf: This asks for a permutation approximation of one concrete torsion group; the other asks for existence of a torsion-free operator-norm counterexample.
  literal-mf-radical-exact: This asks whether E is sofic; the other asks for an exact computation of E's MF radical.
  literal-group-not-sofic: That claim is the negation of this one, carried as a separate node because both directions now have live routes.
artifacts:
  - non_mf_groups_exist.tex
  - docs/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
  - docs/E_SOFICITY_SELF_CONTAINED_2026-08-16.md
---

The literal finitely presented group `E` is sofic.

PROVED 2026-08-14 via `literal-sofic-via-block-tower`
(`docs/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`).  The proof is the finite-stage
tower that proves the witness `W` sofic, with the finite invariant Clifford
subgroup replaced by a finitely generated virtually free invariant block
sub-amalgam: a finite window of `E_T = N_E semidirect T` lies in one telescope
level and finitely many blocks, level orbits on blocks are finite, and the
resulting `M_J semidirect Gamma_n` is residually finite; then `E = E_T x| Z`
is sofic by sofic-kernel/amenable-quotient permanence.

**UNCONDITIONAL, and with no literature input, since 2026-08-16.**  Two
outside dependencies of the 2026-08-14 argument are gone.  The conditional
input `B ~= Gammabar` that the 2026-08-15 adversarial audit found — it made
soficity of `E` conditional while failure of MF was not, inverting the usual
trust surface — is now the theorem `literal-base-presentation-complete`.  And
the Karrass--Pietrowski--Solitar virtual-freeness step is replaced by
`clifford-block-amalgam-residually-finite`.  The route that consumes both is
`literal-telescope-core-lef-via-central-embedding`, and the whole chain is
re-derived from the presentation in
`docs/E_SOFICITY_SELF_CONTAINED_2026-08-16.md`, which also proves the final
split-`Z` step directly rather than citing Elek--Szabó (the same construction
as Lean `SoficIntegerExtension.isSofic_int_semidirectProduct`).

**MACHINE-CHECKED since 2026-08-16.**
`LiteralSoficAssembly.markedGroup_isSofic : IsSofic MarkedGroup` compiles,
takes no hypothesis, and `#print axioms` returns exactly `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx`, no repo axiom, no literature
premise.  The module is in the root import closure and the whole root target
builds green.

What unblocked it was not new mathematics.  `BlockCliffordTowerSofic.isSofic_blockClifford_tower`
was already the finished theorem and `LiteralBlockNormalForm` already computed
`E = C(G) semidirect Vertical`; the two could not be composed because the two
vertical groups were recorded as "unrelated types".  They are the same group —
see `literal-vertical-bridge` in `Sofic/LiteralVerticalBridge.lean`, where
`lampKernel_agree` is `rfl`.  Two facts kept the chain cheap: only
`blockSubgroup <= B_1` is needed (presented blocks may refine geometric ones),
and no step needs the doubling index to be exactly eight.

Still open on the manuscript side: whether to strengthen the printed
Theorem E from the finitely generated witness `W` to the finitely presented
source `E`.  That now has a declaration to cite, so it is an editorial call,
not a formalization gap.

Consequences and dead ends recorded here so they are not retried:

* `E` is a finitely presented sofic non-MF (hence hyperlinear non-MF) group —
  `finitely-presented-sofic-non-mf`, strengthening Theorem E from the
  finitely generated witness to the finitely presented source.
* The amenable-kernel route died twice over: `ker(E -> W)` is free of infinite
  rank (`literal-witness-kernel-free`), and its permanence direction
  (amenable kernel, sofic quotient) is not a theorem — see the warning in
  `docs/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` §3.
* The opposite claim `literal-group-not-sofic` is refuted, and with it the
  stability route through `E/<w>`; by contraposition, modulo the Gohla--Thom
  citation, `E/<w>` is not flexibly permutation-stable.
* The Kun--Thom non-soficity mechanism cannot reach here: `Ehat = V *_B
  (B x Z/2)` has its free-lamp shape with `B` Kazhdan and infranormal in `V`,
  and the element it would kill is the unsquared defect `u` with `w = u^2`,
  but `V` is not Kazhdan — the stable-letter exponent maps it onto `Z`.  That
  failing hypothesis is exactly what the soficity proof consumes.
