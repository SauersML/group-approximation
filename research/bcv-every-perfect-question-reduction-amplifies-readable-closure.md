---
rg: 2
id: bcv-every-perfect-question-reduction-amplifies-readable-closure
kind: claim
title: Every attained-perfect BCV Question Reduction strategy contains all Pauli copies of a decoded source readable algebra
distinct_from:
  bcv-question-reduction-retains-readable-closure: that proves the inclusion only for BCV's chosen honest forward strategy; this extracts the source blocks and the full tensor inclusion from every attained-perfect target strategy.
  bcv-perfect-answer-reduction-decodes-double-cover: that inverts Answer Reduction by joint polynomial atoms; this uses the exact Pauli and controlled-answer normal form of Question Reduction.
  bcv-pauli-amplification-haarizes-only-the-packet: that determines the trace carried by the forced Pauli factor and proves that it does not canonize the source-fiber trace.
---

**ESTABLISHED (attained value one).** Let

```text
Q=QueRed_h(G,k,B)
```

be the BCV Question Reduced game, and let `S` be an attained-perfect
finite-dimensional signed-permutation ZPC strategy for `Q`. Restrict `G`
to the endpoints of the positive-weight edges of its question distribution.
Then there is a perfect signed-permutation ZPC strategy `T` for that
supported source and a monomial unitary

```text
W:H_S -> ell^2(F_2^k) tensor H_T
```

such that

```text
W D_infinity(S) W^*
  contains ell^infinity(F_2^k) tensor D_infinity(T).      (UQR1)
```

Questions outside the support may be assigned arbitrary trivial measurements.
In particular,

```text
dim H_S = 2^k dim H_T,
dim D_infinity(S) >= 2^k dim D_infinity(T).              (UQR2)
```

The unitary can be chosen monomial in the original Z-aligned coordinate
basis. Thus `(UQR1)` is an inclusion of ZPC readable-translate algebras,
not merely an abstract unitary equivalence of untyped strategies.

This is an exact zero-loss statement. A nonattained sequence of strategies
whose values tend to one gives the same normal form and inclusion only after
passing to a tracial ultraproduct; it need not produce an attained
finite-dimensional source strategy.

The proof is `bcv-perfect-question-reduction-readable-amplification-proof`.
