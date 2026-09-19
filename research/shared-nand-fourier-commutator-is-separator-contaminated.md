---
rg: 2
id: shared-nand-fourier-commutator-is-separator-contaminated
kind: claim
title: A shared-NAND Fourier commutator returns the separator, not a bare central phase
distinct_from:
  nand-sheet-swap-cannot-be-a-pure-central-phase: that treats a monomial swap of the two separator-plus atoms and obtains a contaminated conjugation word; this treats a genuinely noncommuting Fourier transform between the two private context signs and computes their group commutator.
  finite-sheet-transport-networks-are-exactly-matricial: that fences coordinate bijections and permutation monodromy; this leaves that class, uses a Hadamard Fourier block, and shows that the first nontransport cell still has an exact finite Clifford model.
  boolean-predicate-central-phase-word: that constructs a phase reader in a selected finite predicate representation; this proves the bare private-sign commutator is impossible on the full shared NAND support and identifies the necessary separator correction.
  bcs-projective-kernel-phase-compilation: that requires payload coupling and a matrix soundness gap; this is the smallest exact two-context Fourier gadget and proves it supplies neither by itself.
---

Let `S,A,B` be self-adjoint involutions in a complex C-star algebra, with

```text
[S,A]=[S,B]=1.                                          (SNF1)
```

Assume both contexts `(S,A)` and `(S,B)` have NAND support: their `(-,-)`
joint atoms vanish.  If

```text
e_-=(1-S)/2,
```

then NAND gives

```text
e_- A=e_-,             e_- B=e_-.                      (SNF2)
```

Consequently the group commutator is trivial on the separator-minus fiber:

```text
e_- [A,B]=e_-.                                          (SNF3)
```

It follows that a bare negative phase equation

```text
[A,B]=J,                 J=-1                           (SNF4)
```

forces `e_-=0`.  In particular `(SNF4)` is incompatible with **full** NAND
support, where the `(-,+)` atom is nonzero.  This obstruction is
representation-independent and applies equally in a commuting-operator
model: imposing the bare commutator phase would delete the intended shared
marginal sector rather than distinguish matrices from a tracial model.

The sharp nontransport alternative is

```text
[A,B]=-S=J S.                                           (SNF5)
```

It already forces the minimal dimension.  On the nonzero separator-plus
fiber, `(SNF5)` says that `A` and `B` anticommute, so that fiber has even
dimension at least two.  Full NAND support also has a nonzero separator-minus
fiber.  Hence every such cell has dimension at least three.

It has an exact three-dimensional Fourier/Clifford realization.  On the
ordered atom basis `(+,+),(+,-),(-,+)`, put

```text
S=diag(1,1,-1),
A=diag(1,-1,1),
F=(Hadamard on the first two coordinates) directSum 1,
B=F A F^*=X_2 directSum 1.                              (SNF6)
```

The unitary `F` commutes with `S` and is genuinely nonmonomial.  Each of
`(S,A)` and `(S,B)` has the three rank-one NAND atoms
`(+,+),(+,-),(-,+)`.  On the separator-plus block, `A=Z_2` and `B=X_2`
anticommute; on the separator-minus line both equal `1`.  Therefore

```text
[A,B]=(-I_2) directSum 1=-S,
W=[A,B]S=-I_3=J.                                       (SNF7)
```

The matrices in `(SNF6)` generate a finite group: the one-qubit real
Clifford group on the plus block, extended trivially on the minus line and
adjoined the finite diagonal sign `S`.  Hence `(SNF7)` is an exact finite-
dimensional, indeed finite-group, marked model.  Arbitrary direct sums give
exact marked models in unbounded dimensions.

Thus finite Fourier transport does accomplish something permutation sheets
cannot: two contexts sharing the literal marginal `S` can occupy genuinely
noncommuting private blocks, and their corrected predicate word returns a
bare central `J`.  But the correction is forced by the shared NAND atom, and
the whole relation table is already Clifford-matricial.  It cannot supply
the finite-dimensional soundness demanded by projective-kernel phase
compilation.  Any successful use of this cell must add a payload relation
that prevents the exact Clifford sector from extending while preserving the
non-CE tracial sector; the Fourier/Heisenberg relations alone do not do so.
