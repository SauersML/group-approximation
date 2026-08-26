---
rg: 2
id: property-t-free-manuscript-theorem-dependency-audit
kind: claim
title: The non-Kazhdan manuscript endpoints have one analytic input and an internal rank-transfer bridge
artifacts:
  - non_mf_groups_exist.tex
  - metadata/NON_MF_SENTENCE_CENSUS.md
  - research/property-t-free-manuscript-theorem-dependency-audit-proof.md
  - GroupApproximation/Manuscript/OneSidedMFRadical/LiteralMFClosure.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/RankTwelveSimplicity.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/PrescribedQuotients.lean
---

The theorem-by-theorem dependency audit of `non_mf_groups_exist.tex` has the
following exact conclusion.

After deleting the statements whose mathematical content is explicitly about
property `(T)`, Kazhdan projections, or Kazhdan transport, every retained
manuscript endpoint follows without a literature theorem from one new input:

```text
Rad_MF(St_20(L_(F_2)(1,2))) = St_20(L_(F_2)(1,2)).
```

The passage from this proposed rank-twenty Steinberg result to the literal
rank-twelve group in the manuscript is not automatic by notation and must be
present in the proof.  It is nevertheless internal: use the canonical
surjection `St_20(R) -> EL_20(R)`, preservation of full MF radical under
surjective images, and the prefix-code matrix self-similarity together with
`GL_n(R)=EL_n(R)` to identify `EL_20(R)` with `EL_12(R)`.  No external
`K`-theory theorem is used in that rank transport.

The retained endpoints are:

1. the literal MF radical and MF-kernel-closure calculus, including the
   universal MF quotient and the criterion for an MF quotient;
2. finite-dimensional commutant rigidity and finite-dimensional sterility of
   the compression-centralizer defect, together with the residually finite
   and finite-source sterility consequences;
3. the exact binary-Leavitt Whitehead compressor identities, the nontrivial
   marked root, and its normal generation;
4. countability, finite generation, nontriviality and simplicity of the
   binary-Leavitt elementary group;
5. the Property-`(T)`-free stable-finiteness and central-corona-corner lemmas,
   which may be retained although the new collapse proof does not need them;
6. full MF radical, triviality of all maps to MF groups, non-MF, and the
   separable stably finite non-MF reduced-group-C-star consequence;
7. functoriality, normal-generation saturation, full-kernel pullback, the
   visible MF quotient, universal factorization, and the prescribed-quotient
   amalgam construction.

The statements to remove, rather than rename, are the one-sided compression
criterion with property-`(T)` hypotheses, the Kazhdan projection order lemma,
one-sided Kazhdan transport, the Hilbert--Schmidt defect corollary, the normal
Kazhdan radical theorem, the property-`(T)` clauses in the headline and the
Leavitt-compression proposition, the property-`(T)` terminal clauses of defect
saturation, and the amenable-plus-Kazhdan remark.

The cited Leavitt normal-structure facts do not remain as literature inputs.
The sandwich property and simplicity of the coefficient ring, the center and
central-unit calculation, elementary-root detection, and elementary-group
simplicity all have internal Lean proofs.  The amalgam vertex injections and
normal-form consequences, the radical/closure calculus, the canonical reduced
group C-star trace and stable-finiteness argument, and the rank transport are
also internal.  Historical citations defining MF or attributing earlier work
are not proof inputs.

Two source-organization changes are still needed for the requested
`Unconditional.lean`, even after the analytic input is proved.  Generic
camouflage theorems currently share a module with a Property-`(T)`-mediated
Hilbert-hotel instance, and some clean algebraic rank-twelve/rank-transport and
reduced-C-star declarations live in files that also import or expose Kazhdan
machinery.  The declarations used by the final endpoint must be split or
restated in clean modules so its import and declaration dependency cone is
literally Property-`(T)`-free.  This is proof engineering, not an additional
mathematical or literature assumption.

There are also four non-`(T)` historical sentences which are not proved in the
repository: Blackadar--Kirchberg's converse `nuclear + MF => NF`, the
Goldbring--Hart route from the negative Connes-embedding result, Shulman's MF
permanence theorem for doubles, and the cited finite-Schatten
non-approximability results.  They are not used by any theorem of the paper.
They may remain explicitly quarantined literature attributions or be deleted;
formalizing them would be independent work and is not discharged by the
binary-Leavitt MF-radical endpoint.  The fifth partial sentence in the current
sentence census is the Ershov--Jaikin-Zapirain Property-`(T)` theorem itself and
belongs to the deleted Kazhdan material.
