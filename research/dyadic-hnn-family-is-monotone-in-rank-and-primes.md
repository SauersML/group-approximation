---
rg: 2
id: dyadic-hnn-family-is-monotone-in-rank-and-primes
kind: claim
title: The arithmetic centralizer HNN groups embed in one another as the rank grows and primes are inverted
distinct_from:
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that characterizes hyperlinearity of one HNN group by a free Haar unitary in some model of its base; this compares different arithmetic pairs by honest group embeddings and needs no model.
  arithmetic-hnn-nonhyperlinearity-equals-global-collapse: that proves six assertions equivalent for one fixed rank and prime; this relates the statements for different ranks and prime sets.
---

**ESTABLISHED** (proof in `dyadic-hnn-family-is-monotone-in-rank-and-primes-proof`).

For `n >= 2` and a nonempty finite set of primes `S`, put

```text
A_(n,S) = SL_n(Z[1/S]),     C_n = SL_n(Z),
G_(n,S) = < A_(n,S), t | [t, C_n] = 1 > = A_(n,S) *_(C_n) (C_n x Z).     (MON1)
```

So `G_(2,{2})` is the group `G_2` of `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`,
and `G_(3,{2})` is the group `G_3` of `sl3-hnn-admits-no-amalgamated-free-haar-unitary`.

1. **(HNN subgroup lemma.)** Let `A <= A'` be groups, `C' <= A'`, and `C = A cap C'`.
   Then `t -> t` and the inclusion `A -> A'` induce an injective homomorphism

   ```text
   < A, t | [t, C] = 1 >  ->  < A', t | [t, C'] = 1 >.                      (MON2)
   ```

2. **(Monotonicity.)** If `n <= n'` and `S subseteq S'`, the corner map
   `x -> diag(x, I_(n'-n))` gives `A_(n,S) cap C_(n') = C_n`, so by (MON2)

   ```text
   G_(n,S)  embeds in  G_(n',S').                                          (MON3)
   ```

3. **(Transfer of approximation properties.)** Hyperlinearity and soficity pass to
   subgroups. Hence, along the partial order `(n,S) <= (n',S')`:
   - non-hyperlinearity (resp. non-soficity) of `G_(n,S)` implies it for every larger index;
   - hyperlinearity (resp. soficity) of `G_(n',S')` implies it for every smaller index.

## What this says about family D

- Among the arithmetic centralizer HNN witnesses, `G_(2,{p})` is the **strongest** negative
  statement: `G_2` nonhyperlinear gives `G_(n,S)` nonhyperlinear for every `n >= 2` and every
  `S` containing `2`.
- A **positive** answer anywhere propagates downward. Hyperlinearity of `G_(3,{2})`, a group
  with a Kazhdan base and Kazhdan edge, would make `G_2` hyperlinear and kill family D at
  `n = 2` without any SL_2 construction. Hyperlinearity of `G_(2,{2,3})` would kill both
  `G_(2,{2})` and `G_(2,{3})`.
- Consequently the strategic fork recorded in `no-exact-quasi-regular-leak` ("fight the
  refutation at SL_3; treat SL_2 as two-sided") is forced by the group theory. The negative
  side is weakest at large rank, and the positive side is weakest at `n = 2`.
- Through `arithmetic-hnn-nonhyperlinearity-equals-global-collapse` the same monotonicity
  holds for every equivalent form at each index: global commutant collapse, non-relative-
  embeddability over scalars, plain-double and binary coset-wreath nonhyperlinearity. Those
  equivalences are proved for one fixed prime; for a set `S` only the group statements above are claimed.

## Scope

This relates open problems. It does not decide any of them, and it does not assert that
the implications are strict.
