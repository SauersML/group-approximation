---
rg: 2
id: infinite-conjugacy-orbits-give-canonical-carrier-no-capture
kind: claim
title: Infinite conjugacy orbits give an amplification-proof canonical carrier gap
distinct_from:
  embedded-group-algebra-carriers-have-no-excess-fixed-component: that transfers whatever canonical fixed component exists; this computes it for Fourier carriers on one cyclic subgroup.
  finite-product-selected-type-mark-does-not-align-carriers: that shows scalar overlap need not yield a common reducing carrier; this obtains an exact no-capture value from infinite conjugacy-orbit geometry rather than pairwise packet overlap.
  marked-hs-separation-forces-spectral-density: that extracts a positive-density spectral projection from a separated word; this proves transversality of a fixed Fourier or spectral carrier to the entire subgroup commutant.
---

Let `H<=G`, let `w in G` have infinite order, and assume every nonzero power
`w^k` in the Fourier support below has an infinite `H`-conjugacy orbit. For

```text
x=sum_(k=-m)^m c_k lambda(w^k) in C[G],
```

one has

```text
E_(L(H)' cap L(G))(x)=c_0 I,                            (ICG1)
||x-E_H(x)||_2^2=sum_(k!=0)|c_k|^2.                    (ICG2)
```

The identical formula holds after every trace-preserving embedding of
`L(G)` into a finite tracial algebra, including every canonical matrix
ultraproduct embedding.

More generally, if `p=1_E(lambda(w))` for a Borel set `E subset T` of Haar
measure `beta`, and every nonzero power of `w` has infinite `H`-conjugacy
orbit, then

```text
E_H(p)=beta I,
||p-E_H(p)||_2^2=beta(1-beta).                          (ICG3)
```

If `H` has property `(T)`, a finite Kazhdan set `S` and `kappa>0` give,
in every such embedding,

```text
sum_(s in S)||[pi(s),pi(x)]||_2^2
 >=kappa sum_(k!=0)|c_k|^2,                            (ICG4)
```

and the analogous lower bound `kappa beta(1-beta)` for `p`. This is a
nonamenable error-spreading floor which survives arbitrary tensor
amplification and reducible canonical-profile models.
