---
rg: 2
id: sl3-positive-density-projective-fold-sector
kind: claim
title: Canonical SL3 double microstates have a macroscopic projective fold singular sector
distinct_from:
  sl3-regular-arithmetic-double-fold-mark-collapse: that asks for the global scalar conclusion `|tr(w)| -> 1`; this asks only for a fixed positive-density right-singular sector on which the two h-matrices agree up to a model-dependent phase.
  sl3-canonical-double-has-a-correctable-vertex: that corrects one whole A-vertex to an exact representation; this neither corrects a vertex nor asks for invariance of the carrier under either vertex group.
  projective-trace-square-transfer-for-sl3-pair: that quantifies over every approximate A-assignment and every auxiliary unitary and concludes a global trace-square estimate; this is restricted to canonical microstates of the fixed arithmetic double and asks only for a macroscopic near-kernel of one projective difference.
  unnamed-positive-density-fixed-space-is-terminal: that is the general phase-one Fejer endpoint for an already supplied group word and contraction; this is the arithmetic source assertion, allows a varying projective phase, and identifies the exact singular-value datum which would supply the contraction.
---

**OPEN POSITIVE-SECTOR ARITHMETIC TERMINAL.**  Put

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),       D=A *_C A,
h=diag(2,1,1/2).
```

There is a constant `alpha>0` with the following property.  For every
canonical-character normalized-Hilbert--Schmidt microstate sequence of `D`,
write

```text
H_(n,j)=pi_(n,j)(h),             j=0,1,
```

for the two vertex matrices.  There are contractions `Y_n` and phases
`lambda_n in T` such that

```text
||Y_n||_2^2 >= alpha-o(1),
||(H_(n,0)-lambda_n H_(n,1))Y_n||_2 -> 0.              (PFS1)
```

Equivalently, after optimizing over one scalar phase, a fixed positive
fraction of the singular values of `H_(n,0)-lambda H_(n,1)` tend to zero.
No invariance, projection structure, functorial choice, or convergence of
the carrier is required.

This is strictly weaker than either global projective folding or correction
of one vertex.  Nevertheless
`nonhyperlinear-from-sl3-positive-density-projective-fold` proves that it
already makes the explicit arithmetic double `D` non-hyperlinear.  The
model-dependent phase is harmless: a phase-twisted Fejer kernel sees the same
vanishing canonical moments of the fold word.

There is a semantic caveat.  By
`canonical-moments-bound-projective-fixed-carrier-density`, every actual
canonical microstate sequence of `D` excludes `(PFS1)` for every fixed
`alpha>0`.  Therefore the universal assertion in this node holds exactly
when no such sequence exists: it is equivalent to non-hyperlinearity of this
specific arithmetic double.  It is a weaker **certificate shape** than
global folding or vertex correction, but not a logically weaker existence
statement.  Canonical moments supply the contradiction after arithmetic
relations produce the carrier; they cannot produce the carrier themselves.

The constant density is load-bearing.  If only carriers of density
`alpha_n->0` are known, the needed Fejer order moves to infinity and the
canonical microstate definition gives no uniform control of that moving word
window.  Direct-sum replication preserves carrier density.  For the naive
tensor carrier `Y_n^(tensor k)`, the squared normalized-HS mass is
`alpha_n^k`, so diagonal tensor amplification does not convert a vanishing
sector into a macroscopic one.  Tensor powers remain useful for amplifying
global trace-square energy when it dominates presentation defect, as in
`projective-trace-square-transfer-for-sl3-pair`, but do not prove `(PFS1)`.

Exact finite-dimensional folding also does not imply `(PFS1)` by abstract
compactness.  Promoting the zero-defect theorem to even one fixed-density
near-kernel is already a normalized-HS robustness statement.  What this node
removes is the unnecessary demand for full-vertex stability or global
trace-modulus-one collapse: the remaining arithmetic task is only a
macroscopic projective singular-sector estimate for one denominator element.

## Attempts

- **Use exact finite-dimensional folding and compactness.**  Exact folding
  says all singular values vanish at defect zero, but without normalized-HS
  stability it supplies no fixed-rank near-kernel at positive defect.
  `exact-fd-invisibility-has-no-general-hs-robustification` records the
  general obstruction; arithmetic input is still required here.
- **Amplify a dilute singular sector.**  Direct sums preserve its normalized
  density, while the evident all-good tensor carrier has density
  `alpha^k`.  If density tends to zero, the Fejer order must move with the
  model, outside the fixed canonical moment window.
- **Use only Bass--Serre regularity and property (T).**  The exact regular
  double representation contains the nonfolded block swap while satisfying
  those tracial hypotheses, by
  `sl3-regular-double-bass-serre-rigidity-firewall`.  A proof must see the
  finite-coordinate obstruction, not just the limiting tracial inclusion.
- **Derive the carrier from the canonical moments.**  This has the wrong
  direction.  The phase-uniform Fejer bound in
  `canonical-moments-bound-projective-fixed-carrier-density` shows that the
  first `N-1` vanishing moments force every such carrier to have density at
  most `1/N`, and the regular `C_N` clock attains that threshold exactly.
