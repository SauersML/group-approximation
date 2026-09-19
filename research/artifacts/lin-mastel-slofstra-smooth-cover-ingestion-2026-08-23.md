# Lin / Mastel--Slofstra / smooth-label-cover ingestion

**Date:** 2026-08-23  
**Scope:** theorem-level consequences for the nonhyperlinear-group graph.

## Direct new source

Junqiao Lin, *MIPco = coRE*, arXiv:2510.07162v1, proves that the
`1/2`-Bell-test separation problem is RE-complete.  The proof records a
stronger promise on synchronous twelfth-level conditionally-linear games:

```text
equal case:     omega_* = omega_co = 1,
separated case: omega_co = 1 and omega_* <= 1/2.
```

The reduction maps a known nonhalting program, such as an unconditional
infinite loop, to the separated case.  This yields an effective finite gap
game without the recursion-theorem selection in
`kleene-mipco-self-destroying-game`.

## What the weighted-BCS paper supplies

Kieran Mastel and William Slofstra, *Two Prover Perfect Zero Knowledge for
MIPstar*, STOC 2024, DOI `10.1145/3618260.3649702`, develops weighted BCS
algebras and quantitative homomorphisms.  In particular, private context
augmentation has constant-one defect transport and bounded context
subdivision has polynomial defect loss.  These results are already represented
by `mastel-slofstra-private-context-augmentation-preserves-defect`.

They do not prove a general quantitative lowering of nonlinear BCS predicates
to binary LCS relations.  Consequently they do not by themselves convert
`G_loop` into a solution group.

## Low-individual-degree and smooth-label-cover inputs

Ji--Natarajan--Vidick--Wright--Yuen, arXiv:2009.12982v1, prove quantum
soundness of the two-prover low-individual-degree test.  Lin uses this as a
component of the conditionally-linear compression verifier; it does not by
itself expose LCS syntax.

Culf--Mastel--Paddock--Spirig, *The quantum smooth label cover problem is
undecidable*, arXiv:2510.03477v3, reduce constant-gap BCS/3SAT protocols to
smooth label-cover projection constraints using the weighted-algebra
formalism.  The output edge predicates have the structured form
`pi_(e,u)(a)=pi_(e,v)(b)`.  Whether the whole commuting-versus-tensor gap
source can be functorially passed through this reduction, and whether local
label validity can then be represented by a full-corner monomial/LCS gadget,
are separate compiler obligations.  They are not claimed established in this
ingestion note.

