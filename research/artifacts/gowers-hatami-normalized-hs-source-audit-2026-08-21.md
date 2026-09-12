# Gowers--Hatami normalized-HS source audit

Date: 2026-08-21

## Source inspected

The supplied archive `/Users/user/Downloads/arXiv-1510.04085v2.gz` is the TeX
source of W. T. Gowers and O. Hatami, *Inverse and stability theorems for
approximate representations of finite groups*, arXiv:1510.04085v2.

The source uses normalized Schatten norms

```text
||A||'_p = d^(-1/p) ||A||_p.
```

For `p=2` this is exactly Cairn's normalized Hilbert--Schmidt norm.

## Precise quantitative interface

Section 6 proves flexible stability: the dimension discrepancy is
`O(epsilon^2 d)` and the uniform approximation error is `O(epsilon)`.  The
enlarged-isometry formulation used by Cairn is quoted explicitly as Theorem
3.2 of Slofstra, arXiv:1806.05267, citing Gowers--Hatami and the exact
formulation of De Chiffre--Ozawa--Thom:

```text
epsilon < 1/16,
d <= m <= d/(1-4 epsilon^2),
||f(g)-V^* rho(g)V||_2 <= 42 epsilon.
```

The constant and dimension correction are uniform in the finite group and
in `d`, but the input is a map on the **complete multiplication table**.

## Correction made to Cairn

The generic claim had incorrectly recorded `epsilon<1/2`.  It now records
the cited `epsilon<1/16` threshold.  Downstream Schur-replica compiler nodes
which invoked the theorem without a mark separation were corrected likewise.

The Clifford capacity lemmas remain valid with their displayed
`epsilon<1/2` precondition because they also assume

```text
||f(J)-I||_2 > 42 epsilon.
```

The left side is at most two, so this forces

```text
epsilon < 1/21 < 1/16.
```

Slofstra makes exactly this reduction in the proof of his Clifford lemma.

## Consequence for the active proof

Nothing in the fixed twenty-qubit packet or equivariant-edge argument needs
a large error threshold: each packet is fixed, so presentation defect can be
chosen small enough that its complete table defect is below `1/16`.  The
paper therefore robustifies the new finite-symmetry lemma exactly as needed.
It does **not** constrain the arbitrary multiplicity unitary left by Schur's
lemma.  The one-equivariant-edge construction is still needed to replace
three independent commutant rotations by one shared holonomy word.
