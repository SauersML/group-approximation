---
rg: 2
id: diagonal-tensor-powers-do-not-amplify-regular-lamp-center
kind: claim
title: Diagonal tensor powers of a regular lamp packet do not amplify its center samples
distinct_from:
  a5-center-spectrum-has-constant-one-site-hamming-gap: that computes the one-packet Plancherel faithfulness and Hamming costs; this proves that tensoring the same group representation produces no independent center samples and leaves both costs unchanged.
  simple-lamp-gauge-rigidity-reduces-to-actor-classicalization: that absorbs a fixed actor representation into a regular actor packet; this is the finite-lamp version and rules out tensor-power repair of the center-fiber chart loss.
---

**ESTABLISHED.** Let `Q` be a finite group and let `lambda_Q` be its left
regular representation.  For every finite-dimensional representation `pi`
of `Q`, Fell absorption gives

```text
lambda_Q tensor pi  ~=  lambda_Q^(dim pi).                (DTP1)
```

Indeed, on `ell^2(Q) tensor H_pi` the unitary

```text
delta_h tensor xi  |->  delta_h tensor pi(h)^(-1) xi
```

conjugates `lambda_Q tensor pi` to `lambda_Q tensor 1`.  Iterating with
`pi=lambda_Q^(tensor(t-1))` gives

```text
lambda_Q^(tensor t) ~= lambda_Q^(|Q|^(t-1)).              (DTP2)
```

Consequently the normalized rank of every central isotypic projection is
unchanged by diagonal tensor powers.  It is always

```text
rank(p_rho)/dim = dim(rho)^2/|Q|.                         (DTP3)
```

In particular, take `Q=K^F` with `K` finite centerless nonabelian simple.
The center spectrum remains

```text
Irr(K)^F with the product Plancherel law p^F,
p_rho=dim(rho)^2/|K|,                                    (DTP4)
```

for every diagonal tensor power.  It does **not** become `t` independent
samples from that spectrum.  A center fiber is faithful on `K^Z` exactly
when every coordinate in `Z` has a nontrivial irrep label, so its good mass
remains

```text
(1-1/|K|)^|Z|.                                           (DTP5)
```

For `K=A5` this is `(59/60)^|Z|`, exactly the loss in
`a5-center-spectrum-has-constant-one-site-hamming-gap`.  Likewise the
weighted Hamming distance between two distinct one-site coordinate
permutations remains `71/100`; it is not amplified to
`1-(29/100)^t`.

Thus tensoring a putative hyperlinear microstate with itself cannot repair
the nonfaithful center states by producing repeated independent labels.
Normalized canonical trace forces the diagonal tensor packet straight back
to an amplification of the same regular packet.  Independent center samples
would require independent lamp-group copies, which are not present in the
generalized wreath product.

## Consequence

The two center defects are inseparable by tensor amplification:

1. individual center fibers fail chart injectivity on a fixed lamp window
   with the positive probability in `(DTP5)`;
2. the center of a complete invariant packet detects one wrong site with the
   same macroscopic `71/100` cost.

Any positive simple-lamp recovery theorem must therefore construct a
coherent near-total actor action before passing to centers.  Diagonal tensor
powers provide neither additional chart states nor a softer boundary.
