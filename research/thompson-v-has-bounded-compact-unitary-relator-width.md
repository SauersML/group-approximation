---
rg: 2
id: thompson-v-has-bounded-compact-unitary-relator-width
kind: claim
title: Some nontrivial element of Thompson's group V has bounded compact unitary relator width
refuted_by: [thompson-v-has-unbounded-compact-unitary-relator-width]
distinct_from:
  kl-violating-equation-over-thompson-v: that is one nonsingular equation killing a coefficient; this is the width inequality such an equation forces, stated with no equation and possibly true without one.
  thompson-v-not-hyperlinear: that excludes normalized Hilbert--Schmidt models; this is a uniform algebraic bound excluding those and every other invariant-length unitary model at once, and it is not known to follow from non-hyperlinearity.
  simple-group-relator-width-in-finite-simple-targets: that is uniform relator width in finite simple targets for nonsofic groups; this is width over the compact groups U(d) with U(d)-conjugators.
---

**OPEN.** Let `V = <S | R>` be a finite presentation. There are `1 != a in V` and `K >= 0` such that for every
`d >= 1` and every tuple `U in U(d)^S`,

```text
a(U) in Cons_K(R(U)),
```

the set of products of at most `K` `U(d)`-conjugates of `r(U)^(+-1)`, `r in R`.

Since `V` is simple, `Rad_cw(V)` is `1` or `V`. So this is equivalent to every element having bounded width, and it is exactly
the negation of `thompson-v-has-unbounded-compact-unitary-relator-width`.

## Where it sits

- **Forced by a violation.** See `thompson-v-bounded-unitary-width-from-kl-violation`.
- **Non-hyperlinearity.** See `thompson-v-not-hyperlinear-from-bounded-unitary-width`.
- **Everything else it excludes.** By part (C) of `kl-kernel-lies-in-the-compact-unitary-width-radical` it excludes, for `V`, every
  unitary model in any of these lengths, including unnormalized ratio models:
  - operator norm;
  - normalized Hilbert--Schmidt norm;
  - rank of `g - I`;
  - Schatten-`p` norm of `g - I`.
- **A decomposition of the V fork.**

  ```text
  violation over V  =>  bounded width  =>  V not hyperlinear
  ```

  This refines `thompson-v-not-hyperlinear-from-kl-violation`. The middle claim can fail on its own. One unitary ratio model for
  one nontrivial `a` refutes it, and that already proves `kl-holds-over-thompson-v`.

## Attempts

1. **From a violation.** Deferred. `thompson-v-bounded-unitary-width-from-kl-violation` is complete up to
   `kl-violating-equation-over-thompson-v`, and no violation is known.
2. **From non-hyperlinearity or non-MF.** Dead as stated. Non-hyperlinearity gives only a qualitative
   modulus: small normalized relator defect forces a small normalized defect of `a`. Bounded width asks
   for exact membership in `Cons_K(R(U))` for every tuple, with a linear constant in every invariant length at once, including
   unnormalized ones. No compactness argument turns the modulus into membership. `Cons_K(R(U))` is compact, but the
   quantifier over all `d` is not.
3. **From finite-target width.** Not applicable. `simple-group-relator-width-in-finite-simple-targets` and
   `simple-group-classical-width-finite-field-linear-soficity` bound width in finite groups under a nonsoficity or
   non-linear-soficity hypothesis. `U(d)` is not finite, and its conjugacy classes are continua, so those counting arguments
   do not transfer.
