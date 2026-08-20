---
rg: 2
id: toeplitz-schur-bcs-shift-amalgam
kind: claim
title: One finite amalgam synchronizes the Fanizza shift with every Toeplitz Schur tape cell
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

OPEN. Construct a finitely presented group `Gamma_*` with the following
simultaneous syntax and completeness properties.

1. It contains the Toeplitz--Steinberg base and one stable letter `t`
   implementing the injective coefficient endomorphism `sigma`.
2. The same word `t` is the shift `U` in the fixed Fanizza BCS tape.
3. For the finite menu of base BCS propagation predicates, finitely many
   Schur packet generators lie in one bounded Toeplitz head. Their central
   selector words are identified with the corresponding base BCS involution
   words. Conjugating these finitely many relations by `t^n` gives every
   level-`n` selector/packet relation used in `(SDL2)`.
4. All derived level-`n` packet, expander, and overlap relations have
   polynomial derivation cost. In particular, every term in the fixed
   decomposition of `(FDB1)` is wired to a packet return incidence so that an
   inactive selector sector contributes to the adjacent weighted
   multiplicity-vector discrepancy.
5. There is an exact unitary representation in which the marked involution
   word `w` corresponding to `x_D` is nonidentity.

The packet predicates are oriented to equal one on propagation-satisfying
assignments. In the exact BCS representation all supported selector sectors
therefore have the same enlarged spin dimension, so local packet extensions
exist. Clause 5 must nevertheless be proved for the **joint** amalgam: local
extensions cannot simply be declared compatible with the whole
Toeplitz--Steinberg representation.

## Attempts

- Add one unrelated packet at every tape level: syntactically infinite and
  therefore unusable. Identifying `t=U` reduces all controls to finitely many
  base relations.
- Tensor independent BCS and Toeplitz representations: this does not satisfy
  the selector identifications.
- Active exact-model construction: extend the nonzero BCS representation by
  its contextwise satisfying Schur spin packets, add countably infinite
  universal multiplicity for every finite base packet type, and use induced
  representations of the finite amalgam so the Toeplitz--Steinberg and BCS
  restrictions agree. The desired BCS summand must remain reducing so its
  nonzero `D` carrier is not lost. The unresolved check is simultaneous
  compatibility of all base context packets with the single stable-letter
  action.
