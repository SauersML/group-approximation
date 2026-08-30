---
rg: 2
id: stw63-commuting-zigzag-proof
kind: route
title: Apply the approximately inner half-flip edge by edge
target: stw63-commuting-zigzag-forces-uniqueness
requires: []
---

Fix one edge, consisting of commuting unital maps
`alpha,beta:Z->B_infinity`.  Commutation gives a unital homomorphism

```text
Theta:Z tensor Z -> B_infinity,
Theta(a tensor b)=alpha(a)beta(b).
```

The approximately inner half-flip of `Z` supplies unitaries in `Z tensor Z`
which approximately conjugate `a tensor 1` to `1 tensor a`.  Their images
under `Theta` approximately conjugate `alpha` to `beta`.

Diagonalize this approximate conjugacy to one exact conjugacy in the sequence
algebra.  Explicitly, lift each image unitary to a sequence of unitaries in
`B`, choose a dense sequence in the unit ball of `Z`, and on successive
coordinate blocks use an approximate conjugator whose error is below `1/k`
on the first `k` elements.  The resulting unitary `V in B_infinity` satisfies

```text
V alpha(a)V*=beta(a)            for every a in Z.
```

Apply this construction to every adjacent pair and multiply the finitely many
resulting unitaries, in the appropriate order.  This gives a unitary
`W in B_infinity` with

```text
W phi(a)W*=psi(a)               for every a in Z.
```

A unitary of `B_infinity=ell_infinity(B)/c_0(B)` lifts, after polar correction
on a tail, to a sequence of unitaries in `B`.  The last equality therefore
becomes approximate unitary equivalence in `B`.
