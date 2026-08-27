---
rg: 2
id: schur-pauli-words-name-atomwise-half-quarter-flags
kind: claim
title: Schur packet words name exact half and quarter flags on every forbidden atom
distinct_from:
  every-forbidden-atom-has-fixed-schur-pauli-words: that names the relative Pauli pair and proves its commutation properties; this combines it with one baseline Pauli pair to construct the exact coarse and fine selector projections required by the cyclic decoder.
  forbidden-weighted-type-carrier-coverage-is-rank-rounding: that chooses anonymous analytic subprojections of prescribed finite rank; these flags are joint spectral cuts of a fixed finite list of literal packet words and require no multiplicity-space choice.
  predicate-rank-gate-doubles-restriction-multiplicity: that records the factor-two restriction multiplicity; this gives the two concrete balanced cuts which read that factor inside each forbidden selector atom.
---

Fix one forbidden assignment `a` in a Schur--Clifford predicate packet.  Let
`C_a` be its central selector atom in the marked packet sector.  By
`every-forbidden-atom-has-fixed-schur-pauli-words`, there are literal words
`X_a,Z_a` which commute with the baseline packet on `C_a` and satisfy

```text
X_a Z_a=-Z_a X_a.                                     (SPF1)
```

Choose one literal baseline Pauli pair `X_0,Z_0`.  It commutes with the
relative pair on `C_a` and satisfies `X_0Z_0=-Z_0X_0`.  Define

```text
e_a=C_a(I-Z_a)/2,
f_a=C_a(I-Z_a)(I-Z_0)/4.                              (SPF2)
```

Then `e_a,f_a` are projections, `f_a<=e_a<=C_a`, and in every exact marked
packet representation

```text
tr(e_a)=tr(C_a)/2,
tr(f_a)=tr(C_a)/4.                                    (SPF3)
```

For the first equality, conjugation by `X_a` exchanges the two spectral
halves of `Z_a` while fixing `C_a`.  For the second, conjugation by `X_0`
exchanges the two spectral halves of `Z_0` inside each `Z_a` half, because
`X_0` commutes with `Z_a`.  The statement holds separately on every
irreducible multiplicity block and is therefore independent of spectator
multiplicity.

The flags in `(SPF2)` are finite star-polynomials in literal group words.
Their normalized Hilbert--Schmidt perturbation after approximate packet
exactification is bounded by the fixed packet stability modulus.  The
underlying atoms `C_a`, over the finitely many forbidden assignments, sum to
the entire marked forbidden Schur-packet carrier, while `(SPF3)` supplies its
half and quarter flags.  No four-divisibility trimming and no noncanonical
choice in an anonymous multiplicity algebra is needed.

This does not supply the global actuator.  It replaces the old within-type
authentication question by the narrower problem of returning these named
Pauli flags through one common finite-matrix holonomy while preserving the
perfect non-CE trace.
