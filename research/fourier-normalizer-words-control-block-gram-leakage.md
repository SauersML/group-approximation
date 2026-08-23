---
rg: 2
id: fourier-normalizer-words-control-block-gram-leakage
kind: claim
title: Fourier normalizer words exactly control off-type block-Gram leakage
distinct_from:
  hadamard-selector-commutator-charges-two-path-leakage: that is the binary two-block Hadamard reflection identity for one already selector-central return; this is the general m-phase Parseval identity for all source blocks of an arbitrary unitary.
  disjoint-tag-covariance-controls-cross-gram: that uses finite-group intertwiner gaps and parent exclusivity to bound tagged overlaps approximately; this is an exact Fourier equality for one spectral phase tag.
  unitary-offdiagonal-block-gram-is-support-leakage: that bounds one off-diagonal block by support leakage; this sums and exactly diagonalizes every cross-Gram term through normalizer word energies.
---

Let `(E_j)_(j in Z/m)` be orthogonal projections summing to `1`, put

```text
D=sum_j zeta^j E_j,             zeta=exp(2 pi i/m),
P_(ij)=E_i P E_j
```

for a unitary `P`.  Then

```text
sum_(r=1)^(m-1) ||[P D^r P^*,D]_add||_2^2
 =m sum_(i!=k) |zeta^k-zeta^i|^2
       sum_j ||P_(ij) P_(kj)^*||_2^2.                 (FNG1)
```

Consequently

```text
sum_(i!=k,j)||P_(ij)P_(kj)^*||_2^2
 <=1/(4m sin^2(pi/m))
      sum_(r=1)^(m-1)||[P D^r P^*,D]_add||_2^2.       (FNG2)
```

Each norm on the right is exactly the defect of the ordinary multiplicative
commutator word

```text
(P D^r P^*) D (P D^(-r) P^*) D^(-1).
```

Replacing `P` by `P^*` gives the row analogue controlling
`P_(ij)^*P_(ik)`.  The identity is dimension-independent and valid in every
finite tracial von Neumann algebra.  It therefore converts authenticated
spectral blocks to word energy, but is not by itself a matrix-only
authentication of a noncanonical forbidden cut.
