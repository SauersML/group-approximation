---
rg: 2
id: balanced-parity-excludes-perfect-matching-pauli-mixtures
kind: claim
title: Balanced parity excludes perfect-matching Pauli mixtures at constant energy
distinct_from:
  erasure-cleaning-rounds-all-projective-parity-valleys: that gives the general projective rounding theorem from an abstract bad-check set; this applies it to the proposed high-type perfect-matching direct sum and computes why balanced original and pair-sum faces expose every attempted Pauli repair.
  bounded-type-balanced-occurrences-synchronize: that handles noncentral bounded-type algebras; the matching blocks have irreducible dimension exponential in code length, but their commutators remain central projective signs.
  sparse-clifford-cycles-refute-average-commutator-rounding: that is a valid countermodel to bare average commutation; this proves the balanced Tanner parity layer rules out its high-type matching symmetrization.
---

Let `H` be a robust-erasure-cleaning parity matrix with `M=Theta(L)` rows,
and use the balanced overlay: `Theta(M)` copies of every original check,
all pair-sum checks, and the complete logical-pair commutation layer.

Consider any central direct sum of Pauli blocks.  On a block write

```text
 Q_i=sigma_i W(v_i),       v_i in F_2^(2m),              (BPM1)
 s_a=sum_i H_(a,i)v_i.                                    (BPM2)
```

If `s_a!=0`, the original parity word is a nonidentity Pauli and has squared
normalized Hilbert--Schmidt defect two.  If `s_a=0`, its residual scalar sign
can still be wrong, in which case the defect is four.  Put

```text
 E={a: product_i Q_i^(H_(a,i)) !=I},
 eta=|E|/M.                                              (BPM3)
```

The pair-sum face `(a,b)` has vector syndrome `s_a+s_b`.  Since the repeated
original layer has constant weight inside the balanced presentation, its
energy alone controls `eta`.

The complete-pair commutator energy is four times the density `beta` of the
symplectic sign matrix

```text
 B_(i,j)=omega(v_i,v_j).                                 (BPM4)
```

On every good check `a` outside `E`, each row of `B` lies in the kernel of
the surviving parity matrix.  Robust erasure cleaning and projective
rounding therefore give, blockwise and after central integration,

```text
 dist_code^2 <= C(eta+beta)
              <= C' E_balanced.                         (BPM5)
```

The constants are independent of `L`, Pauli rank, block dimension, and the
number of central summands.  Hence no direct sum of exponentially large
perfect-matching Clifford blocks can be both a constant distance from the
commuting code variety and have balanced-overlay defect tending to zero.

For the naïve proposed block, the `v_i` are a symplectic basis paired by one
perfect matching.  They are linearly independent, so every nonempty Tanner
row has `s_a!=0`; the balanced original parity layer already has constant
energy.  More elaborate Pauli labels can make many `s_a` vanish or make the
pair-sum syndromes equal, but any residual scalar phase remains in `E`, and
`(BPM5)` shows that repairing these failures removes the far obstruction
rather than hiding it.

This exclusion is specific to projective blocks.  It does not control the
remaining high-type sector whose commutators are genuinely noncentral.
