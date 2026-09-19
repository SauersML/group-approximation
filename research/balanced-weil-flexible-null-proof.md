---
rg: 2
id: balanced-weil-flexible-null-proof
kind: route
title: Sum the structural energy and restore every deleted even line
target: balanced-weil-blocks-are-flexibly-null
requires:
  - five-mod-eight-torsion-normalization-retains-a-padding-charge
  - exact-torsion-frame-has-rank-one-strict-counterpackets
  - regular-iwahori-strict-congruence-exactification-is-false
---

For one torsion-normalized compressed even block at a prime `p=5 mod 8`,
`five-mod-eight-torsion-normalization-retains-a-padding-charge` gives

```text
1 <= (23/2) (
  ||C_p(u)-1||_F^2 + ||C_p(v)-1||_F^2
).                                                        (1)
```

Both words are block diagonal under orthogonal sums, and Frobenius squares
add.  The exact odd-Weil block has zero structural energy.  Summing `(1)`
over the `K` positive blocks gives

```text
K <= (23/2) E(Phi).
```

Division by `N` is `(BWF3)`.  In particular a proposed positive-density
missing-line imbalance, `K/N>=eta>0`, has normalized root-sum-square defect
at least `sqrt(2 eta/23)`; it cannot be a microstate sequence.

By `exact-torsion-frame-has-rank-one-strict-counterpackets`, restoring the
deleted fixed line changes each compressed even block into its full exact
even-Weil representation.  For every fixed presentation generator the
unnormalized Frobenius square of that one-block change is bounded by one
universal constant.  The odd block is left unchanged.  Hence, after embedding
all old blocks into the completed space,

```text
sum_over_generators ||Phi-Pi||_F^2 <= C_0 K.
```

Normalize by `N+K` and use `K/N<=(23/2)epsilon(Phi)^2`.  This proves the
generalized-distance estimate in `(BWF4)`, after changing the constant for
the fixed finite generator set.  It also proves
`(N+K)/N-1=K/N=O(epsilon(Phi)^2)`.

On the central word, each input summand has signs `(+1,-1)` on two spaces
of the same dimension `d_j`, so its trace is zero.  The completion adds
one positive line per summand, giving trace `K/(N+K)`.  For a fixed
noncentral group element, the even and odd Weil character formulas are
`O(sqrt(p_j))`, while the block dimension is of order `p_j`.  Torsion
normalization changes each fixed word by bounded Frobenius norm, whose
aggregate normalized contribution is `O(sqrt(K/N))`.  Thus escape of the
least occupied prime, together with `(BWF3)`, gives the regular character
for both the input ultraproduct and its exact completion.
