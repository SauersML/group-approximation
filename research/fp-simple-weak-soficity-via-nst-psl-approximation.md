---
rg: 2
id: fp-simple-weak-soficity-via-nst-psl-approximation
kind: route
title: A simple weakly sofic group is PSL-approximable by Nikolov-Schneider-Thom, and PSL weak models are exactly linear soficity over finite fields
target: fp-simple-weak-soficity-is-finite-field-linear-soficity
requires: [nst-simple-weakly-sofic-groups-are-psl-approximable, simple-group-psl-width-is-finite-field-linear-soficity, simple-group-support-and-semisimple-rank-models-collapse]
---

`G = <X | R>` is an infinite finitely presented simple group. Items (i), (ii), (iii) are as on the target.

## 1. (i) => (iii)

Suppose `G` is weakly sofic, that is **Fin**-approximable (Example 1 of Nikolov--Schneider--Thom, quoted on
`nst-simple-weakly-sofic-groups-are-psl-approximable-citation`).
- **PSL-approximation.** By their Theorem 4, `G` is **PSL**-approximable. So there are finite `S ⊇ X ∪ {1}`
  containing the prefixes of the relators, `eps -> 0`, groups `PSL_n(q)` with invariant length functions, and maps `phi`
  that are `eps`-multiplicative on `S` and separate every `g in S \ {1}` by `delta_g > 0`.
- **Weak models.** These are weak models of `G` in the groups `PSL_n(q)` with bi-invariant lengths, in the sense of item
  1 (iii) of `simple-group-psl-width-is-finite-field-linear-soficity`. Put `a_x = phi(x)`. Relator values have length
  `O(eps)` and a nontrivial generator has length `>= delta_x`.
- **Conclusion.** By the equivalence (i) <=> (iii) there, `G` is linear sofic over finite fields.

Contrapositively, (i) gives (iii).

## 2. (iii) => (i)

The definition bullet of `simple-group-psl-width-is-finite-field-linear-soficity` records that linear soficity over
finite fields implies weak soficity: `GL_n(F_q)` is finite and the normalized rank length is bi-invariant.

## 3. (ii) <=> (iii)

- **(ii) => (iii).** Suppose `G` is weakly sofic. Take weak models `a` with relator lengths `<= C eps` and `l(a_x) >= delta`
  for a generator `x != 1`, as in section 2 of `fp-simple-weak-soficity-is-finite-field-linear-soficity-proof`.
  Bi-invariance and subadditivity give `l(a_x) <= w_Q(a) C eps`. So `w_Q(a) >= delta/(C eps)` is unbounded, contradicting (ii).
- **(iii) => (ii).** Suppose (ii) fails, so that for every `k` some `Q`, `a` and `x` have `a_x` not a product of `k` conjugates
  of relator values. Glebsky's capped conjugation length
  `l_k(g) = min(1, (least number of conjugates of r(a)^(+-1) with product g) / k)` is bi-invariant. It gives
  `l_k(r(a)) <= 1/k` and `l_k(a_x) = 1`. Section 0 of `simple-group-support-and-semisimple-rank-models-collapse-proof`
  turns such models of a simple group into weak soficity. So `G` is weakly sofic, contradicting (iii).

This route uses neither the finite-simple templates nor `relator-width-bounded-by-almost-simple-quotients`. It does
use the full PSL dichotomy, which is unreviewed.
