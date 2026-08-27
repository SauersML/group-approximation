---
rg: 2
id: two-qubit-clifford-closes-transverse-m2-chord
kind: claim
title: One multiplicity qubit closes the transverse M2 chord by literal Clifford transports
distinct_from:
  full-root-separators-force-uniform-chord: that proves every chord over full matrix separators has uniform conditional trace in any tracial extension; this realizes the uniform boundary case in the smallest possible extension.
  free-relative-placement-closes-one-balanced-chord: that makes the endpoint separators commute by freely choosing a classical joint-cell placement; this retains a genuinely noncommuting transverse pair and closes the chord in its relative commutant.
  finite-relative-commutant-chord-is-bounded-integer-feasibility: that gives an abstract Wedderburn integer criterion; this is the smallest explicit noncommuting solution and makes all transports literal elements of one finite Clifford group.
---

On `C^2 tensor C^2`, write `X_i,Z_i` for the Pauli matrices on qubit `i`.
Take the two endpoint separator signs and chord signs

```text
S_0=Z_1,          Y_0=Z_1 Z_2,
S_1=X_1,          Y_1=X_1 Z_2.                         (TQC1)
```

Then `[S_i,Y_i]=0`, while the two separator algebras are transverse and

```text
C[S_0] vee C[S_1]=M_2(C) tensor I_2.                   (TQC2)
```

Let `CNOT_(1->2)` be controlled `X_2` in the `Z_1` basis and put

```text
U_0=CNOT_(1->2),
U_1=(H_1 tensor I_2) U_0 (H_1 tensor I_2),             (TQC3)
```

where `H_1` is the Hadamard on qubit one.  These are finite-order Clifford
unitaries and satisfy

```text
[U_i,S_i]=0,                 U_i Y_i U_i^*=Z_2.         (TQC4)
```

Thus the two noncommuting endpoint separator positions admit exact
separator-preserving regauges to one common chord sign.  All Pauli and
Clifford matrices in `(TQC1)--(TQC4)` lie in a finite two-qubit Clifford
group `K`.  Its defining four-dimensional representation is irreducible
(the Pauli subgroup spans `M_4(C)`), so its primitive central idempotent `q`
gives

```text
q C[K]q isomorphic to M_4(C),                           (TQC5)
```

and `U_0,U_1` are literal finite-group transports in that signed corner.

This is the smallest transverse solution.  In `M_2(C)` itself, the
commutant of `C[Z_1] vee C[X_1]` is scalar and contains no nontrivial chord
projection.  One multiplicity qubit changes the commutant to
`I_2 tensor M_2(C)`, where

```text
p=(I+Z_2)/2                                              (TQC6)
```

has rank one over each rank-one separator atom.  Hence every conditional
plus fraction is exactly `1/2`.

The model supplies a concrete contextual cycle block impossible in a
simultaneously diagonal root placement, with exact Hecke translations.  Its
scaling limit is sharp: tensoring more multiplicity cannot make the table
nonuniform while `(TQC2)` remains fixed, by
`full-root-separators-force-uniform-chord`.  Therefore this block can glue
only chord incidences whose endpoint sign is conditionally balanced on every
separator atom.  A nonlinear/NAND-type conditional table still requires a
proper multi-block separator algebra before the chord is installed.

