---
rg: 2
id: thompson-v-has-unbounded-compact-unitary-relator-width
kind: claim
title: Thompson's group V has unbounded compact unitary relator width, so it embeds in a quotient of an algebraic ultraproduct of unitary groups
refuted_by: [thompson-v-has-bounded-compact-unitary-relator-width]
distinct_from:
  thompson-v-hyperlinear: that asks for approximations in normalized Hilbert--Schmidt distance; this asks only that no single constant bounds the relator width of one element in every dimension, which hyperlinearity implies, and which amounts to a homomorphism into an abstract quotient of an algebraic ultraproduct with no metric.
  kl-holds-over-thompson-v: that is injectivity of every nonsingular coefficient map over V; this is a sufficient condition for it that mentions no equation.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that excludes exact representations; this asks for approximate models that escape every bounded conjugacy-class cover of the relator images.
  simple-group-classical-width-finite-field-linear-soficity: that is relator width in finite classical groups; this is width in the compact groups U(d) with U(d)-conjugators.
---

**OPEN.** Let `V = <S | R>` be a finite presentation of Thompson's group `V`, and let `a in F(S)`
represent a nontrivial element. Then for every finite `R_0 <= R` and every `K >= 0` there are some `d` and some
`U in U(d)^S` such that `a(U)` is not a product of at most `K` `U(d)`-conjugates of the elements
`r(U)^(+-1)`, `r in R_0`.

Equivalently, `Rad_cw(V) = 1` in the notation of
`kl-kernel-lies-in-the-compact-unitary-width-radical`. By part (B) of that claim and simplicity of `V`
(`thompson-v-finitely-presented-infinite-simple`), this is also equivalent to each of the following:

- the displayed condition holds for **one** nontrivial `a`;
- `V` embeds in `(prod_i U(d_i))/N` for some normal `N` containing `N_omega`, for some ultrafilter `omega`.

The statement does not depend on the presentation or on `a`.

## Consequences

- **Kervaire--Laudenbach over V.** See `kl-holds-over-thompson-v-via-unbounded-unitary-width`.
- **Where it sits among known properties.** Part (C) of `kl-kernel-lies-in-the-compact-unitary-width-radical` gives the implications
  - hyperlinear => this (`thompson-v-unbounded-unitary-width-from-hyperlinearity`);
  - MF => this;
  - unitary rank or Schatten-`p` approximation => this.

  Radicals shrink on subgroups, so `Rad_cw = 1` for the binary Leavitt unit group, which contains `V`, would also give this.
- **A concrete witness format.** By (C) it suffices to find one conjugation-invariant, symmetric, subadditive length `l` on the
  groups `U(d)` and tuples `U_m` with

  ```text
  max_(r in R) l(r(U_m)) / l(a(U_m)) -> 0.
  ```

  Neither defect has to be bounded below or normalized, so any unnormalized ratio model is enough. Such a model is necessarily
  approximate, because `V` has no nontrivial finite-dimensional unitary representation.

## Attempts

1. **Abelian targets.** Dead as witnesses. `V` is perfect, so `a in [F, F] <<R>>` in `F(S)`. In `U(1)` every commutator
   evaluates to `1`, so `a(U)` is a fixed product of the `r(U)^(+-1)`, with the number of factors independent of `U`. A
   witness therefore needs noncommutative tuples.
2. **Cantor-action truncations and covariant compressions.** Not decided by the existing no-gos.
   - `thompson-v-hyperlinear-via-cantor-action-truncation` and `thompson-v-hyperlinear-via-covariant-compressions` are Dead for
     normalized Hilbert--Schmidt models, through `thompson-v-cantor-orbits-have-no-folner-sets` and
     `thompson-v-covariant-cantor-representations-are-not-amenable`.
   - Those arguments bound the boundary or repair mass below by a fixed fraction of the model size.
   - They do not address models in which the defect of `a` is itself a vanishing fraction but still dominates the relator defect,
     which is the unnormalized ratio format above.
   - No model of that type has been built or refuted.
3. **Permutation ratio models.** These reduce to soficity.
   - Take a permutation tuple on `X` with Hamming defect fraction `delta` for `a` and `epsilon delta` for every relator, where `epsilon -> 0`.
   - The `k`-fold diagonal tensor power acts on `X^k`. A point of `X^k` is fixed exactly when every coordinate is fixed, so `a` moves a
     fraction `1 - (1 - delta)^k`, while each relator moves at most `k epsilon delta`.
   - With `k ~ 1/delta`, `a` stays bounded below and the relators go to `0`. That gives a sofic model separating `a`, and by simplicity it
     makes `V` sofic.
   - So permutation witnesses are no easier than `thompson-v-is-sofic`.
   - The same amplification is not available for unitary rank or Hilbert--Schmidt ratio models, because eigenvalue products can cancel in
     tensor powers. Those formats are the ones not already reduced to an open approximation question.
