---
rg: 2
id: atlas-kernel-relators-couple-cross-gram-to-four-pauli
kind: claim
title: Full Atlas kernel relators couple the compulsory overlap to all four Pauli words
distinct_from:
  compulsory-pauli-cross-gram-is-four-word-intertwiner: that incorrectly asks the local raw/comb packet alone to supply the coupling and is refuted by the canonical rectangular model.
  atlas-five-row-operator-phase-lift: that controls five global covariance energies; this asks only for four mixed intertwining residuals on the already forced positive overlap.
  four-pauli-cross-gram-exact-completeness-firewall: that proves ordinary quotient-algebra coupling is impossible; this retains only the finite-matrix rank/multiplicity extraction which can evade the exact regular model.
---

**OPEN, FINITE-MATRIX-ONLY.**  Work in the regular-`A_8` microstate normal form of
`leavitt-regular-atlas-hyperlinearity-criterion`, and assume the complete
fixed normal-generating packet `bar_S` has defect `delta`.  Form the two
compressed raw/comb coefficient contractions `X_0,X_1` and choose the heavier
ordered overlap

```text
T=X_j^*X_i,
||T||_2^2>=5/64-o_delta(1).                            (AKC1)
```

Using at least one relation in `bar_S` outside the local one-cell Pauli
tables, decode four contractions `C_1,...,C_4` in one recovered
`M_2 tensor I` coefficient algebra and the four transverse Pauli target
words `D_1,...,D_4` such that

```text
sum_(k=1)^4||D_kT-TC_k||_2<=omega(delta),              (AKC2)
||s4(D)-8D_1D_2D_3D_4||_2<=omega(delta),              (AKC3)
```

for one dimension-independent modulus `omega(delta)->0`.

The same orientation and the literal overlap `(AKC1)` must occur in all four
rows.

## Exact algebraic interpretation is refuted

`four-pauli-cross-gram-exact-completeness-firewall` gives, already at zero
error,

```text
sum_(k=1)^4 ||D_kT-TC_k||_2^2 >= 5/2304.              (AKC4)
```

Consequently `(AKC2)` cannot be obtained as a fixed quotient group-algebra
identity, a coefficient-ideal membership certificate, or a van Kampen
consequence of the full kernel packet.  Any such consequence would also hold
in the exact regular quotient representation, where all kernel defects are
zero and the canonical cross-Gram overlap remains positive, contradicting
`(AKC4)`.  The exact rectangular packet is therefore not merely a warning
against using the local one-cell relations: exact completeness rules out
every ordinary algebraic derivation from the full kernel as well.

## Remaining target

The source factor and common carrier in `(AKC2)` must be extracted by a
genuinely finite-coordinate operation: normalized-rank separation,
finite-multiplicity balance, or an equivalent matrix-integrality theorem
which has no analogue in the exact regular von Neumann model.  After that
finite-only extraction, the mixed hard/comb/interior relations may control
the four residuals on the selected matrix carrier.  The load-bearing claim is
now precisely this finite-multiplicity extraction; no fixed algebraic kernel
identity can replace it.
