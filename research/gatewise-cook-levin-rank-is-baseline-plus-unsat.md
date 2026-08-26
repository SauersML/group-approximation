---
rg: 2
id: gatewise-cook-levin-rank-is-baseline-plus-unsat
kind: claim
title: A gatewise affine Cook--Levin matrix has rank equal to its baseline plus the number of violated gates
artifacts:
  - experiments/gatewise_cook_levin_rank_energy.py
distinct_from:
  boolean-predicate-is-one-rank-jump: that compiles one arbitrary Boolean predicate into one rank bit; this takes a direct sum over every gate of a complete circuit assignment, so its excess rank is the integer number of locally inconsistent gates.
  three-xor-violation-is-one-clifford-rank: that is one affine parity check; the AND block here has affine entries but a nonlinear determinant, and the direct sum records the full gatewise Cook--Levin energy.
  predicate-rank-gate-doubles-restriction-multiplicity: that gives one factor-two restriction for a Boolean predicate; this is its gatewise direct-sum analogue and gives one factor of two for every violated gate in a fixed complete-assignment sector.
---

Let `C` be a Boolean circuit with `m` fan-in-at-most-two gates, using AND,
COPY, NOT, and XOR, and assign bits to every input and internal wire.  For a
gate `g`, let `v_g` be one exactly when its assigned output disagrees with its
Boolean gate function.

For an AND gate with assigned wires `z=x AND y`, put

```text
R_g(x,y,z) = [[1,x],
              [y,z]].                                          (CLR1)
```

All entries are affine-linear in the wire bits.  Over `F_2`,

```text
det R_g = z+xy = v_g.
```

The first row is nonzero, so `rank_F2 R_g=1+v_g`.  For COPY, NOT, and XOR use

```text
R_g = diag(1,v_g),
v_copy=x+z,   v_not=1+x+z,   v_xor=x+y+z.                       (CLR2)
```

These entries are also affine and again `rank_F2 R_g=1+v_g`.  Therefore the
block diagonal matrix

```text
R_C = direct_sum_(g in C) R_g
```

obeys, for every complete wire assignment,

```text
rank_F2 R_C = m + sum_g v_g = m + UNSAT_C.                       (CLR3)
```

Here `UNSAT_C` is an ordinary integer count, not its parity.  Equation `(CLR3)`
is just rank additivity across the displayed direct sum; it makes no claim
about approximate operator occurrences or about consistency between distinct
contexts using the same logical wire.

The principal submatrix obtained by retaining the first coordinate in every
gate block is `I_m`.  Hence the class-two packet dictionary gives a baseline
spin module of dimension `2^m`, while a simple module for the full assigned
packet has dimension `2^(m+UNSAT_C)`.  Restriction to that baseline packet has
exact multiplicity

```text
2^(UNSAT_C).                                                     (CLR4)
```

In particular, a classical gap `UNSAT_C>=alpha m` gives restriction
multiplicity at least `2^(alpha m)` inside that one assignment sector.
This is the gate-by-gate direct-sum form of the established Schur
rank-to-restriction-multiplicity mechanism.

This is an exact sectorwise finite-group statement.  It does not identify the
multiplicity spaces produced by different gate occurrences, scales, or branch
states.
