---
rg: 2
id: mf-radical-godel-word
kind: claim
title: Every sound computably axiomatized theory misses a true nontrivial word in the fixed MF-radical computer
root: true
distinct_from:
  single-finitely-presented-mf-radical-computer: that fixed-carrier theorem and its undecidable promised word family are fully formalized; this additionally internalizes coded proof systems, restricted soundness, and Kleene recursion.
  self-aware-finite-approximation-trichotomy: that classifies self-reference architectures; this asks for a theory-relative independent word inside one fixed finite presentation.
artifacts:
  - GroupApproximation/Computability/MFRadicalComputer.lean
  - GroupApproximation/Computability/MFRadicalGodel.lean
  - GroupApproximation/Endpoint/ChosenNonMFAudit.lean
---

For a computably axiomatized theory `T` sound for assertions `r_e != 1` about
the fixed MF-radical computer, proof search plus Kleene recursion selects an
index `e_T` such that

```text
1 != r_(e_T) in Res_MF(U_MF),
T does not prove r_(e_T) != 1.
```

The Lean theorem
`MFRadicalGodel.exists_true_unprovable_radical_word` implements the fixed-point
contradiction.  `MFRadicalGodel.ProofSystem` packages a partial-recursive proof
search, `ProofSystem.Sound` is restricted soundness for the concrete formulas
`codeWord c != 1`, and Mathlib's `Nat.Partrec.Code.fixed_point₂` supplies the
self-referential code.  The selected word is nontrivial, MF-invisible, and lies
in `[Res_MF(U_MF), U_MF]`; its formula is not proved by the supplied system.

## Attempts

The controller was strengthened while formalizing this endpoint: it now
retains an exact computable reduction from Mathlib partial-recursive codes to
Boone configurations, rather than choosing only an arbitrary machine with an
undecidable halting predicate.  This exact universal semantics is what makes
the Kleene fixed point apply to the same fixed finitely presented carrier.
