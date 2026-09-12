---
rg: 2
id: atlas-first-root-relator-is-half-block-commutant-face
kind: claim
title: The first rank-five relator is exactly a half-block commutant face in the two-unitary moment system
distinct_from:
  atlas-first-rank-five-relator-kills-order-one-weyl-slice: that evaluates the relator only in the order-one Weyl trace and obtains a constant defect; this identifies the exact operator face cut out by the same relator for arbitrary two-unitary coefficients.
  atlas-three-label-mode-two-unitary-moment-reduction: that expands every literal word as an affine system of noncommutative moments; this uses the special root-subgroup form of the first word to turn its affine equation into one positive off-diagonal energy.
---

**ESTABLISHED EXACT FACE.**  In the three-label controlled-unitary slice, put

```text
G = lambda(I+E_34) tensor I,
H_Z = U_Z (lambda(I+E_32) tensor I) U_Z^*,             (FRF1)
```

where `U_Z` is `(TLM3)`, and put

```text
A = lambda(I+E_31) tensor I,
C = lambda(I+E_24) tensor I,
B_Z = A H_Z A H_Z C H_Z A H_Z C A.                    (FRF2)
```

(The indices in `(FRF1)`--`(FRF2)` are one-based.)  The packet word
`root_12_1e` is exactly

```text
[G,B_Z]=G B_Z G B_Z^*.                                (FRF3)
```

Let `R=(I+G)/2`.  The transvection `I+E_34` has order two, so `G` is a
self-adjoint involution; in the regular `A8` label representation both of its
spectral projections have normalized trace `1/2`.  Define

```text
Omega(Z_1,Z_2)
 = ||R B_Z (I-R)||_2^2 + ||(I-R) B_Z R||_2^2.          (FRF4)
```

Then the first literal defect and its affine moment equation are exactly

```text
||[G,B_Z]-I||_2^2 = 4 Omega(Z_1,Z_2),                 (FRF5)

Re sum_(i,j in {0,1,2}^8)
     c_root(i,j) tr(M_root(i,j))
   = 1 - 2 Omega(Z_1,Z_2).                            (FRF6)
```

Here `c_root` and `M_root` are the explicit coefficients and coefficient
words of `(TLM5)` for the displayed seventeen-syllable relator.  Thus `(FRF6)`
is the requested exact affine noncommutative two-unitary moment constraint,
but its positivity is hidden by the expanded coordinates.

Consequently this first relation forces precisely the smaller face

```text
R B_Z (I-R) = (I-R) B_Z R = 0,                        (FRF7)
```

or asymptotically the same statement in normalized Hilbert--Schmidt norm.
Equivalently, `B_Z` must commute with the fixed transvection `G`; the two
trace-`1/2` eigenspaces of `G` are common reducing subspaces for `G` and
`B_Z`.  This is a constraint on the **transported nine-syllable root word**,
not a proof that `Z_1` and `Z_2` commute in the coefficient algebra.  Any
positive two-unitary construction must therefore solve this half-block
commutant equation before the other 4,647 packet entries are considered.

For the refuted order-one Weyl family, the balanced-area calculation becomes

```text
Omega = 24333991 / 82575360,                          (FRF8)
```

independently of the phase.  Hence `(FRF5)` recovers its fixed first-relator
defect and explains geometrically why changing the Weyl phase cannot help.

DERIVATION
atlas-first-root-half-block-proof
