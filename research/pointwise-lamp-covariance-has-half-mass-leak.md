---
rg: 2
id: pointwise-lamp-covariance-has-half-mass-leak
kind: claim
title: Pointwise corona covariance permits a moving half-mass character leak at every coordinate
distinct_from:
  exact-lamp-lifts-admit-moving-pair-kernel-jumps: that fixes the even-lamp module and exhibits a moving two-point kernel jump; this works on the full regular lamp module, computes the joint-PVM transport leakage exactly, and proves that subsequences, amplification, and direct-sum reblocking do not reduce it.
  corona-defect-is-not-uniform: that distinguishes pointwise from uniform multiplicative defect abstractly; this gives an exact whole-lamp representation at every coordinate and locates the failure in one explicitly moving spectral character.
  sofic-actor-refutes-lamp-character-transport: that uses marked microstates and the Schreier gap to refute a dimension-free decoder for sofic actors; this is a direct two-dimensional lift countermodel, carries no marked Schreier mass, and isolates why an arbitrary corona lift cannot feed that gap.
---

**ESTABLISHED.**  Let a countably infinite group `A` act on itself by left
translation, let

```text
M = direct_sum_A C_2,
Gamma = M semidirect A,
```

and fix `1 != s in A`.  There are finite sets `E_n increasing to A`, exact
two-dimensional representations

```text
rho_n : M -> U(2),
```

and actor lifts `U_(g,n)=I_2` such that:

1. `rho_n` has one finite joint character PVM, with two rank-one atoms;
2. for every fixed `m in M` and `g in A`,

   ```text
   U_(g,n) rho_n(m) U_(g,n)^* = rho_n(g.m)                 (PCL1)
   ```

   for all sufficiently large `n`; hence the maps

   ```text
   sigma_n(m,g)=rho_n(m)
   ```

   are pointwise operator-norm asymptotic representations of `Gamma` and
   define a genuine norm-corona homomorphism;
3. nevertheless the character-transport leakage of `U_(s,n)` for the joint
   PVM of `rho_n` is

   ```text
   L_s(rho_n,U_(s,n)) = 1/2                               (PCL2)
   ```

   for every `n`.

The value `1/2` is unchanged by taking subsequences, by equal amplification,
or by direct-sum reblocking of these coordinates.  Thus pointwise
operator-norm covariance of every fixed lamp word -- even together with an
exact representation of the **entire** lamp group at every coordinate --
does not imply vanishing actor leakage for its finite character PVM.
In particular this applies to every infinite finitely generated `A`, with
`s` chosen as any nonidentity member of a fixed finite generating set.

The corona homomorphism in this example does admit a different zero-leakage
lift: replace the moving character by the invariant total-parity character.
At every coordinate that correction is operator-norm distance `2` on some
moving lamp word, although it agrees eventually on each fixed word.  Hence
the example refutes lift-independent extraction and reblocking, not the
existence of a specially selected lift.  For the atomic Schreier route this
is the exact remaining distinction: a positive theorem must select one
globally actor-compatible lift from the marked microstate with a **uniform
whole-module** modulus.  Pointwise corona data alone cannot do so.
