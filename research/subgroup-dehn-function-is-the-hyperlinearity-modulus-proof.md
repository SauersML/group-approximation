---
rg: 2
id: subgroup-dehn-function-is-the-hyperlinearity-modulus-proof
kind: route
title: Telescope the van Kampen filling, using that conjugation is a 2-norm isometry
target: subgroup-dehn-function-is-the-hyperlinearity-modulus
requires: []
---

**`(SDM1)`.**  Let `w` be a word over `B u B^-1` of `B`-length at most `n` with
`w =_G 1`.  Rewriting each letter by its `A`-word makes `w` a word over
`A u A^-1` which is trivial in `H`, so by the definition of the Dehn function
of `G` in `H` it is freely equal to a product of at most
`k = delta_(G,H)(n)` conjugates of relators:

```text
w =_(F(A)) prod_(i=1)^k u_i r_i^(e_i) u_i^(-1),   r_i in R, e_i = +-1.
```

Apply `pi` and put `x_i = pi(u_i) pi(r_i)^(e_i) pi(u_i)^(-1)`, a unitary.
Because the normalized Hilbert--Schmidt norm is invariant under left and right
multiplication by unitaries,

```text
||x_i - 1||_2 = ||pi(r_i)^(e_i) - 1||_2 = ||pi(r_i) - 1||_2 <= delta,
```

the middle equality because `||v^(-1) - 1||_2 = ||1 - v||_2` for unitary `v`.
Telescoping a product of unitaries,

```text
prod_(i=1)^k x_i - 1 = sum_(i=1)^k (x_1 ... x_(i-1)) (x_i - 1),
```

and each prefix is unitary, so

```text
||pi_G(w) - 1||_2 = ||prod_i x_i - 1||_2 <= sum_i ||x_i - 1||_2 <= k delta.
```

Note `pi_G(w) = pi(w)` by construction of `pi_G`, since rewriting letters by
their `A`-words is exactly what `pi_G` does.

**`(SDM2)`.**  Fix `n`.  Hyperlinearity of `H` gives unitary `A`-tuples of any
prescribed relator defect `delta > 0`, so `(SDM1)` gives `B`-tuples whose
relations of length at most `n` have defect at most `delta_(G,H)(n) delta`,
which tends to `0` with `delta` since `n` is fixed.  Choosing
`delta_n = 1/(n delta_(G,H)(n))` and diagonalizing produces a sequence of
`B`-tuples that is an asymptotic representation of `G`; the marked element is
kept separated because the ambient tuples come from an injective ultraproduct
embedding of `H`.

**`(SDM3)`.**  Contrapositive of `(SDM1)`.  If `delta . delta_(G,H)(n) <
epsilon` then the induced `B`-tuple satisfies every `G`-relation of length at
most `n` to within `epsilon`, so the certificate applies and gives
`||pi_G(z) - 1||_2 < alpha`; and `pi_G(z) = pi(w_z)`.  That `w_z != 1` in `H`
is because `G` is a subgroup of `H` and `z != 1` in `G`.

All steps are elementary and dimension-free; no property of `G` or `H` beyond
finite presentability of `H` and finiteness of the relative Dehn function is
used.
