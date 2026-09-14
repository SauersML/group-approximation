---
rg: 2
id: random-exponential-pairing-families-are-unlearnable
kind: claim
title: Families of independent uniform pairings above (1+rho^2(m-1))^n members defeat every noisy-pullback list decoder
distinct_from:
  separated-small-pairing-families-defeat-the-noise-test: that is the decodable regime, where subexponential separated families are learned and the test fails; this is the opposite regime, where random exponential families defeat every list decoder, so member-level transparency cannot reach them.
  bkm-test-transparent-on-learnable-games: that shows the test adds no soundness when matchings are learnable; this proves that generic exponentially large families, including random smooth designs, are not learnable.
artifacts:
  - research/artifacts/unique-games-smooth-design-learnability-2026-09-11.md
---

**ESTABLISHED.** Let `Q = (P_1, ..., P_M)` be independent uniform perfect
matchings of `[2n]`. Plant `P_(i_0)` with `i_0` uniform, and observe one noisy
pullback `x`: a `P_(i_0)`-pair-constant uniform vector in `Z_m^(2n)`, with each
coordinate retained with probability `rho` and otherwise resampled. For every
list decoder `List_Q : Z_m^(2n) -> [M]^L`, which may depend on `Q`,

```text
E_Q Pr[ i_0 in List_Q(x) ] <= 2 sqrt( (2L+4) A^n / (M-1) ),   A = 1 + rho^2 (m-1) < m.
```

**Proof idea.** Two facts bound the posterior of any index:

- each pair's likelihood ratio is at most `A`;
- the partition function over the `M-1` unplanted matchings is an independent
  sum given `x`, with mean `mu(x) = m^(2n) nu(x)`.

Chebyshev's inequality controls that sum, and the `x` of low pullback density
have mass at most `tau`. Composing with a permutation design `D` does not change
the bound, because the planted conjugate of every other member is again
independent and uniform.

**Consequence.** The random smooth designs of size about `m^n poly(n)`, and
their `t`-wise uniform compositions `D o Q`, are member-unlearnable with success
decaying like `(A/m)^(n/2)`. Pullback smoothness forces at least about `m^n`
members, above both the separated-family decoding threshold and `A^n`. So
generic smooth designs escape member-level transparency. Transparency can still
act through decodable features (`noise-test-transparent-on-decodable-matching-features`).
No hardness or status of UGC is asserted.

DERIVATION random-exponential-pairing-unlearnability-proof
