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
---

For a computably axiomatized theory `T` sound for assertions `r_e != 1` about
the fixed MF-radical computer, proof search plus Kleene recursion selects an
index `e_T` such that

```text
1 != r_(e_T) in Res_MF(U_MF),
T does not prove r_(e_T) != 1.
```

The paper proof is the standard fixed-point contradiction.  This node remains
OPEN until Cairn contains explicit syntax for the relevant proof systems,
restricted soundness, and the recursion-theorem interface.  The underlying
fixed group, radical-valued word family, and undecidability theorem are already
closed in `single-finitely-presented-mf-radical-computer`; no analytic or
literature input is missing here.

## Attempts

The fixed-point paper argument is complete, but encoding it as a Lean theorem
without a concrete datatype for proof systems would merely move the missing
input into an abstract hypothesis.  The active route therefore waits on
`computable-proof-system-kleene-interface` instead of laundering that syntax
as a premise of a closed endpoint.
