---
rg: 2
id: sparse-pauli-pair-defeats-random-order-blr
kind: claim
title: One sparse Pauli pair defeats randomized ordered-product BLR despite vanishing balanced parity energy
invalidates: [random-order-operator-blr-centralization]
distinct_from:
  averaged-commutators-do-not-give-abelian-table: that uses a linear-size disjoint Clifford matching and discards parity; this uses one Pauli pair and verifies that the balanced all-dual parity and redundant-check energies vanish.
  sparse-clifford-cycles-refute-average-commutator-rounding: that proves constant distance from commuting generator tuples; this tuple is average-close to the trivial exact tuple but its ordered full table still has constant BLR defect.
  operator-tail-contraction-misses-uniform-diffuse-matching: that identifies a diffuse scalar profile invisible to tail recurrence; this is a sparse profile which tail peeling can repair, and proves peeling must precede ordered-product table construction.
---

ESTABLISHED.  Let `H_L` be any binary bounded-width parity family with `M`
rows, column degree at most `D`, and `M>=cL`.  Form the balanced quadratic
overlay by taking `M` copies of every original row and one face for every
pairwise row sum.  For all sufficiently large `L`, choose coordinates `1,2`
which do not occur together in an original row.  Such a pair exists because
the row-cooccurrence graph has degree at most `D(w-1)`.

Put on one qubit

```text
Q_1=X,   Q_2=Z,   Q_i=I  (i>=3).                          (SPB1)
```

Use the same reflection at every occurrence copy, so equality energy is
zero.  Then the balanced parity-product energy is `O(D/M)=O(1/L)`, and the
within-face commutator energy is `O(D^2/M^2)`.  Nevertheless, for **every**
choice of an ordering `pi_a` for each `a in F_2^L`, the ordered-product map

```text
f(a)=product_(i in supp(a), in order pi_a) Q_i             (SPB2)
```

has average BLR defect bounded below by

```text
E_(a,b)||f(a)f(b)-f(a+b)||_2^2 >=3/4.                     (SPB3)
```

The same lower bound holds after averaging over any random seed which first
chooses one complete ordering table `(pi_a)_a`.  Hence random ordering does
not convert balanced occurrence energy into average multiplicativity with a
length-independent modulus.

There is also no low-loss escape by averaging the products over an
independent uniform ordering before polarizing.  Whenever `a_1=a_2=1`, the
two relative orders give `XZ` and `ZX=-XZ` with equal probability, so

```text
E_pi f_pi(a)=0.                                           (SPB4)
```

This happens for one quarter of all labels.  Any unitary extension of the
polar part on that kernel has mean squared distance `2` from the raw random
product on those labels.  Thus amenable/order averaging destroys a constant
amount of the table before unitary BLR self-correction can be invoked.

This is not a counterexample to same-Hilbert rounding of the balanced
presentation: `(SPB1)` differs from the trivial exact code tuple on only
`2/L` of the coordinates.  It is a sharp sequencing no-go.  Sparse-tail or
shortened-core repair must occur **before** any construction which expands
the generators into the exponentially large ordered-product table.

