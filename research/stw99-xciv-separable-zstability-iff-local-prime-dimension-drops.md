---
rg: 2
id: stw99-xciv-separable-zstability-iff-local-prime-dimension-drops
kind: claim
title: Separable Z-stability is exactly local norm-centralization of prime dimension-drop blocks
distinct_from:
  stw99-xciv-separable-zstability-iff-local-norm-central-z: that criterion asks for an actual approximately central copy of the whole infinite-dimensional algebra Z on every finite test; this exact weakening asks only for one finitely generated prime dimension-drop block at a time.
  stw99-xciv-norm-matrix-tower-has-zstable-hull: that gives a sufficient class through coherent finite-dimensional towers and growing Bratteli multiplicities; this is an equivalence for every unital ambient algebra and assumes no tower.
  stw99-xciv-finite-norm-spectral-gap-is-negative-certificate: that gives a sufficient scalar-commutant gap for failure; this gives the exact finite dimension-drop obstruction to separable Z-stability.
---

For `k>=2`, put

```text
I_k={f in C([0,1],M_k tensor M_(k+1)):
     f(0) in M_k tensor 1, f(1) in 1 tensor M_(k+1)}
```

and fix a finite selfadjoint contractive generating set `H_k` for `I_k`.
For every unital C\*-algebra `B`, with no separability assumption, the
following are equivalent.

1. Every norm-separable subset of `B` is contained in a separable unital
   `Z`-stable C\*-subalgebra of `B`.
2. For every finite `F subset B`, every `k>=2`, and every `epsilon>0`, there
   is a unital homomorphism `psi:I_k->B` such that

```text
||[a,psi(h)]||<epsilon       (a in F, h in H_k).
```

Equivalently, failure of separable `Z`-stability has an exact finite
operator-norm certificate: there are finite `F subset B`, `k>=2`, and
`delta>0` such that every unital homomorphism `psi:I_k->B` satisfies

```text
max_{a in F, h in H_k} ||[a,psi(h)]|| >= delta.
```

Thus Problem XCIV can be attacked one finitely generated prime
dimension-drop block at a time.  This does not replace operator norm by the
tracial `2`-norm and does not assert that `R` satisfies the condition.
