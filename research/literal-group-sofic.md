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
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
  - notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md
---

The literal finitely presented group `E` is sofic.

PROVED 2026-08-14 via `literal-sofic-via-block-tower`
(`notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`).  The proof is the finite-stage
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
`notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md`, which also proves the final
split-`Z` step directly rather than citing Elek--Szabó (the same construction
as Lean `SoficIntegerExtension.isSofic_int_semidirectProduct`).

Two things that are NOT settled by any of this.  No Lean declaration concludes
`IsSofic` for the literal carrier — the endpoint drafts
(`Sofic/Literal{LampKernelSplit,BlockGeometry,LampKernelAmalgam,TelescopeCoreLEF,SoficEndpoint}.lean`)
do not compile into one closed theorem, so under the
formalized-or-not-in-manuscript doctrine this cannot enter the manuscript yet.
And `non_mf_groups_exist.tex` still says, at the line introducing the
open-questions list, that "whether `E` itself is sofic is open" — the graph and
the manuscript disagree, and the manuscript is the stale one.

Consequences and dead ends recorded here so they are not retried:

* `E` is a finitely presented sofic non-MF (hence hyperlinear non-MF) group —
  `finitely-presented-sofic-non-mf`, strengthening Theorem E from the
  finitely generated witness to the finitely presented source.
* The amenable-kernel route died twice over: `ker(E -> W)` is free of infinite
  rank (`literal-witness-kernel-free`), and its permanence direction
  (amenable kernel, sofic quotient) is not a theorem — see the warning in
  `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` §3.
* The opposite claim `literal-group-not-sofic` is refuted, and with it the
  stability route through `E/<w>`; by contraposition, modulo the Gohla--Thom
  citation, `E/<w>` is not flexibly permutation-stable.
* The Kun--Thom non-soficity mechanism cannot reach here: `Ehat = V *_B
  (B x Z/2)` has its free-lamp shape with `B` Kazhdan and infranormal in `V`,
  and the element it would kill is the unsquared defect `u` with `w = u^2`,
  but `V` is not Kazhdan — the stable-letter exponent maps it onto `Z`.  That
  failing hypothesis is exactly what the soficity proof consumes.
