---
rg: 2
id: maximal-group-cstar-infinite-under-strict-compression
kind: claim
title: A strict Kazhdan compression makes the maximal group C-star algebra infinite while the reduced one stays traced
distinct_from:
  literal-stably-finite-non-mf-reduced-group-algebra: That is about the REDUCED algebra of the literal group, which is stably finite and not MF; this is about the MAXIMAL algebra of the same group, which is not even Dedekind finite -- the two conclusions are opposite and both hold.
  exact-stably-finite-non-mf-reduced-group-algebra: That adds exactness to the reduced-algebra statement; this is the maximal-algebra side and shares none of its conclusions.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Analysis/MaximalCStarParagraphEndpoint.lean
  - GroupApproximation/Analysis/MaximalGroupCStar.lean
  - GroupApproximation/Analysis/MaximalCStarKazhdanAverage.lean
  - GroupApproximation/Analysis/MaximalCStarLiteralBase.lean
---

ESTABLISHED.  `Analysis/MaximalCStarParagraphEndpoint.manuscriptMaximalCStarStrictCompressionRemark`
is the manuscript remark `rem:maxinfinite` (in the appendix `app:maxcstar`) as
one proposition with no premises.  For every group `E` carrying a strict
Kazhdan compression `t Γ t⁻¹ ⊊ Γ`:

* the Kazhdan projection `p` exists in the maximal algebra, is self-adjoint and
  idempotent;
* conjugation by the compressor dominates it on both sides --
  `(u p u*) p = p` and `p (u p u*) = p` -- and the domination is **strict**,
  `u p u* ≠ p`;
* consequently the maximal algebra is not Dedekind finite, not stably finite,
  carries no faithful tracial state, is not residually finite dimensional, has
  no MF embedding and is not MF;
* the averaging operator's spectrum is confined, `μ ≤ rate` or `μ = 1`, and
  `avg · p = p`;
* while the **reduced** algebra of the same group does carry a faithful tracial
  state and admits no proper projection compression at all.

The second conjunct instantiates all of it at the literal non-MF group: a
strict Kazhdan compression exists for it, so its maximal algebra is infinite in
every sense above.

## Why the two algebras pointing opposite ways is the content

The reduced algebra of the literal group is stably finite and not MF; the
maximal algebra of the same group fails even Dedekind finiteness.  So "the
group C-star algebra is not MF" is ambiguous until the completion is named, and
this endpoint is what makes the two statements coexist rather than contradict.
It is also why the undecidability lane parameterizes over *five* separate
recognition predicates rather than one.
