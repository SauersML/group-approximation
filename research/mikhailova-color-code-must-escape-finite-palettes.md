---
rg: 2
id: mikhailova-color-code-must-escape-finite-palettes
kind: claim
title: Every Mikhailova color-code witness escapes all finite palettes
distinct_from:
  mikhailova-left-right-soficity-is-one-color-code: that identifies the exact one-color-code criterion; this proves a quantitative structural necessity for every witness when the quotient is infinite.
  mikhailova-color-code-schreier-irs-firewall: that separates external colors from subgroup statistics; this shows why the colors cannot be replaced by a bounded standard observable or finite factor.
  mihailova-actor-liftable-ce-forces-q-hyperlinear: that assumes matrix liftability; this is an unconditional counting consequence inside the permutation-color model.
---

Assume `H` is infinite and the Mikhailova left-right action has a
color-code witness.  Represent its left free-factor homomorphism by exact
maps

```text
sigma_n:F->Sym(A_n)
```

and its color point by `c_n:A_n->N`.  Let

```text
mu_n(j)=|c_n^(-1)(j)|/|A_n|
```

be the color distribution.  Then for every fixed integer `K>=1`,

```text
max_{C subset N, |C|<=K} mu_n(C) -> 0.                 (MCE1)
```

(The convergence is along the ultrafilter defining the witness, or along
the chosen witnessing subsequence in a sequential formulation.)

More quantitatively, choose words `w_1,...,w_m in F` with pairwise
distinct images in `H`, and put

```text
epsilon_n=max_{i<j}
 Pr_a[c_n(sigma_n(w_i)^(-1)a)
      =c_n(sigma_n(w_j)^(-1)a)].
```

Then every set `C` of at most `K` colors satisfies

```text
mu_n(C) <= K/m + (m-1)epsilon_n/2.                     (MCE2)
```

The code criterion makes `epsilon_n->0`.  Since an infinite `H`
allows arbitrarily large `m`, equation `(MCE1)` follows.

Thus a witness cannot use a uniformly bounded alphabet, retain a positive
mass on finitely many standard colors, or yield a finite generating
observable by tightness.  The quotient equality is necessarily carried by
an increasingly diffuse external label space.  This is exactly why
collapsing colors to a finite quotient action or a standard finite
partition is not a valid descent to a sofic approximation of `H`.

DERIVATION
[[mikhailova-color-escape-proof]]
