---
rg: 2
id: stw84-untwisted-coefficient-symbols-pay-covariance-gap
kind: claim
title: Untwisted coefficient symbols pay a linear covariance gap
distinct_from:
  stw84-scalar-fourier-row-two-colour: that theorem uses the multiplicative circle evaluation for scalar rows; the present theorem proves quantitatively that no u.c.p. replacement on an untwisted coefficient tensor product can approximate a genuinely covariant coefficient pair.
  stw84-invariant-coefficient-stages-restore-two-fourier-colours: that theorem replaces the untwisted tensor product by the correct finite-dimensional crossed product; the present theorem shows why this replacement is necessary whenever the coefficient action is nontrivial.
artifacts:
  - research/artifacts/stw84-untwisted-coefficient-covariance-gap-audit-2026-08-30.md
---

Let `D` and `A` be unital C-star algebras, let `z` denote the coordinate
unitary in `C(T)`, and let

```text
Phi:C(T) tensor D -> A
```

be c.p.c.  If `v in D` and `U,d in A` are unitaries, put

```text
eta=||Phi(1)-1||.
```

If

```text
||Phi(z tensor 1)-U||<=epsilon_U,
||Phi(1 tensor v)-d||<=epsilon_d,                     (UCG1)
```

then

```text
||[U,d]||
 <=2 sqrt((eta+2epsilon_U)(eta+2epsilon_d))
   +2(epsilon_U+epsilon_d).                           (UCG2)
```

For a u.c.p. map `eta=0`.  In particular, if both errors are at most
`epsilon`, then

```text
epsilon >= ||[U,d]||/8.                              (UCG3)
```

If either tensor-factor unitary is returned exactly, it lies in the
multiplicative domain of `Phi`; if, for example,
`Phi(1 tensor v)=d`, then the sharper estimate

```text
||[U,d]||<=2 epsilon_U                               (UCG4)
```

holds.

Consequently the coefficient seam in the weighted Fourier-row approach to
STW Problem LXXXIV cannot be crossed by replacing the scalar
star-homomorphism `C(T)->A` with an asymptotically unital c.p.c. evaluation
on the untwisted algebra `C(T) tensor D`.  For a coefficient unitary with a
fixed nonzero covariance commutator, every such evaluation has a fixed norm
gap.  The correct symbol must encode the action—by a finite-stage crossed
product as in
`stw84-invariant-coefficient-stages-restore-two-fourier-colours`—or abandon
simultaneous recovery of the Fourier and coefficient generators.

DERIVATION
[[stw84-stinespring-tensor-commutator-gap-proof]]
