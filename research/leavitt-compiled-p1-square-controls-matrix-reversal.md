---
rg: 2
id: leavitt-compiled-p1-square-controls-matrix-reversal
kind: claim
title: The compiled p1 square defect controls matrix reversal and has an exact spectral boundary
distinct_from:
  leavitt-seven-cell-thompson-completion-requires-moved-pairs: That uses eventual-tail classes of Thompson prefix actions to obstruct specified completions; this gives identities for the actual unitary compiler and characterizes the corresponding unrestricted finite-matrix conditions.
  leavitt-eight-word-packet-is-quantitatively-equivalent: That compares the existing eight and nine packet rows; this controls another compiler word conditionally on its own square defect, without proving that defect follows from the eight rows.
artifacts:
  - research/artifacts/leavitt-compiler-square-reversal-and-spectral-boundary-2026-09-08.md
---

For any unitary evaluation of the exact marked finite factors, use the
current shared compiler and put

```text
P=p_1, Q=q_1, R=X_0^(-1) B=PQP,
S=PQP^(-1), J=P B_1 P^(-1), delta=||P^2-I||.
```

Then `J` is an involution, `S` is a commutator of two involutions,
and for every unitarily invariant norm with the triangle inequality,

```text
||R-S||=delta,        J S J=S^(-1),
||J R J-R^(-1)||<=2 delta.
```

For normalized Hilbert--Schmidt norm and trace,
`|Im tr(R^m)|<=m delta` for every integer `m>=1`.
The artifact also records exact and quantitative commutator identities
supplied by the `d^2` anchor, isolating the extra commutation that
would imply `p_1^2=1`.

A finite-dimensional unitary is a commutator of two involutions exactly
when its spectrum is invariant under complex conjugation, with
multiplicity, and its `-1` multiplicity is even. In even dimension,
the two involutions can both be chosen to have trace zero. For the
actual word `R`, determinant one holds identically, so the parity
condition is automatic once its spectrum has that symmetry.

These freely reconstructed involutions need not be the shared
compiler involutions or preserve their relations with `C,B_i`.
Whether the true native row `p_1^2` lies in the normal closure of
`T_8` remains unresolved here. No bound of `delta` by the eight-row
defect, dimension-uniform gap, or nonhyperlinearity result is proved.
This is a written proof, not newly Lean-verified.

DERIVATION
compiler-commutators-control-reversal-and-unitary-spectra
