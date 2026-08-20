---
rg: 2
id: character-rigid-signed-bcs-quotient
kind: claim
title: Put a non-CE BCS quotient in a finite-dimension-free character-rigid signed sector
distinct_from:
  same-context-s3-endpoint-atlas: that seeks matrix-only multiplicity curvature from three local packet comparisons; this may use an algebraic quotient because sector character rigidity supplies the missing canonical-trace promotion globally.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that embeds the BCS algebra into a positive canonical corner, so pulling the corner trace back is automatic; this uses a quotient in the reverse direction and therefore needs character rigidity to identify its source trace.
---

Construct a finitely presented group `Gamma`, a finite normal subgroup
`K`, a `Gamma`-invariant irreducible type `rho in Irr(K)` with central block
projection `q=z_rho`, and a unital surjection

```text
q C^*(Gamma) q -> B,                                  (CRQ1)
```

where `B` is one fixed finite BCS algebra with tracial states and no
Connes-embeddable tracial state, such that:

1. no finite-dimensional representation of `Gamma` contains `rho` on `K`;
2. every extremal normalized character of `Gamma` supported on `q` is either
   finite-dimensional or the canonical `q`-regular character.

Then the signed corner has unique trace, and
`unique-trace-signed-corner-quotient-forces-nonhyperlinear` proves that
`Gamma` is nonhyperlinear.

This target separates the two construction jobs cleanly.  The quotient in
`(CRQ1)` is weaker than the signed-Hecke **embedding** target: local BCS
generators may be images of corner operators and no algebraic injectivity is
needed.  Character rigidity supplies the trace promotion which a general
quotient lacks.  Conversely character rigidity without `(CRQ1)` has no
reason to place a non-CE trace in the selected sector.

Promising inputs are a higher-rank character-rigid group or lattice together
with a finite central extension whose marked type is absent from every
finite-dimensional representation.  The unresolved operation is to install
the BCS quotient without destroying that sector character classification.

## Attempts

- Start from a higher-rank lattice with the regular-versus-finite-dimensional
  character dichotomy and pass to a finite central extension whose selected
  type is killed by every finite-dimensional representation.  This supplies
  trace uniqueness but no map onto the BCS algebra.
- Start from the signed-Hecke predicate packets, where a quotient onto each
  local context block is explicit.  Ordinary finite amalgamation can glue the
  local blocks only along amenable edges and remains hyperlinear; equivalently
  it cannot preserve the required global BCS quotient.  Adding those packet
  vertices to a rigid lattice also gives no known permanence theorem for the
  lattice's character classification.
- The next concrete test is whether a known character-rigid central extension
  admits a finite set of matrix-valued Hecke operators satisfying the BCS
  relations **as a quotient**.  Failure should be recorded at the level of
  double-coset support or sector characters rather than by demanding the much
  stronger corner embedding.
