---
rg: 2
id: one-steinberg-loop-is-hnn-gram-neutral
kind: claim
title: One Steinberg loop is tautological on the free HNN orbit Gram matrix
invalidates:
  - sl3-hnn-exclusion-from-one-steinberg-loop
distinct_from:
  closed-a2-loop-still-leaves-swap-fold-free: that gives a finite matrix countermodel to two denominator-return identities; this is an exact calculation inside the full free HNN law showing why one literal lattice loop contributes no new scalar Gram inequality.
  free-hnn-outlier-has-dyadic-a2-pvm-tower: that retains the loop coherently at every spectral depth and every coset; this proves that at one depth the loop merely authenticates two names for the same endpoint.
---

In the notation `(DPT1)--(DPT5)`, the Steinberg relation

```text
[x_23(1),x_31(-1)]=x_21(-1)                            (SNG1)
```

does not change the Gram matrix of the coset atoms.  Both sides act by the
same permutation of `A/C`, so for every two atoms the trace after following
the commutator path is exactly the trace after following the single-root
path.  That common value is already determined by `(DPT4)`: it is the atom
mass on an identical endpoint and the product of masses on distinct
endpoints.

Consequently no scalar two-point or finite Gram inequality obtained by
substituting `(SNG1)` into the full free-lamp moments can exclude the HNN
enemy.  The relation authenticates path equality but creates neither a new
orthogonality nor a rank loss.  A viable use of `(SNG1)` must retain
matrix-coordinate data across unbounded spectral refinements, or combine it
with further noncommuting loops on the same carrier.

DERIVATION
one-steinberg-loop-hnn-gram-proof
