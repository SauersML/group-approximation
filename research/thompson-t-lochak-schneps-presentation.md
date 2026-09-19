---
rg: 2
id: thompson-t-lochak-schneps-presentation
kind: claim
title: Thompson's T is the quotient of Z/4 * Z/3 by three long relators (Lochak--Schneps), realised by rotation by 1/4 and an order-3 dyadic map
distinct_from:
  thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3: that presents V as a quotient of an amalgam of non-cyclic finite groups; this presents T as a quotient of the free product of two finite cyclic groups, with no amalgamation.
  thompson-t-is-isomorphic-to-ppsl2z: that identifies T with the piecewise-PSL(2,Z) group; this is a finite presentation on an order-4 and an order-3 generator.
artifacts:
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/pl_circle.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/verify_ls.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/find_words.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_verify_ls.json
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_find_words.json
---

**ESTABLISHED** by `thompson-t-lochak-schneps-presentation-citation` (citation import plus an exact
computation of the relators in a concrete model).

## Statement

```text
T  =  < alpha, beta | alpha^4, beta^3, r_1, r_2, (beta alpha)^5 >,
r_1 = [beta alpha beta, alpha^2 beta alpha beta alpha^2],
r_2 = [beta alpha beta, alpha^2 beta^2 alpha^2 beta alpha beta alpha^2 beta alpha^2].
```

In words: `T` is the quotient of `Z/4 * Z/3 = <alpha> * <beta>` by the normal closure of `r_1`, `r_2` and
`r_P = (beta alpha)^5`.

**A concrete model (computed exactly).** Put `alpha = ` rotation by `1/4` and let `beta` be the dyadic PL
circle map sending `[0,1/2) -> [1/2,3/4)`, `[1/2,3/4) -> [3/4,1)` and `[3/4,1) -> [0,1/2)` affinely. Then:
- all five relators are the identity. This holds under both reading conventions for words, with exact
  rational arithmetic (`verify_ls.py`);
- reading the leftmost letter first, the Cannon--Floyd--Parry generators are `A = beta alpha alpha`,
  `B = beta alpha beta` and `C = beta beta` (`find_words.py`). So `alpha, beta` generate `T`.

Consequently the surjection `Z/4 * Z/3 -> T` onto this model kills `r_1, r_2, r_P`. That part is verified,
not imported. The only imported content is that no further relators are needed.

**Useful identities in the model and in every representation.**
- `J = alpha^2` is an involution.
- Put `X = beta alpha beta` (a palindrome) and `W = alpha^2 beta^2 alpha^2`, so `W^(-1) = alpha^2 beta alpha^2`.
  Then `r_1 = [X, J X J]` and `r_2 = [X, W X W^(-1)]`.
- In the model, `supp X = [1/2, 1]`, `supp(J X J) = [0, 1/2]` and `supp(W X W^(-1)) = [0, 1/4]`.

DERIVATION
thompson-t-lochak-schneps-presentation-citation
