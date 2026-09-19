---
rg: 2
id: bcv-every-perfect-question-reduction-amplifies-readable-closure
kind: claim
title: Every attained-perfect BCV Question Reduction strategy contains all Pauli copies of a decoded source-double-cover readable algebra
distinct_from:
  bcv-question-reduction-retains-readable-closure: that proves the inclusion only for BCV's chosen honest forward strategy; this extracts side-specific source blocks and the full tensor inclusion from every attained-perfect target strategy.
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
Then there is a perfect signed-permutation ZPC strategy `T_pm` for
`DoubleCover(G)` on that support and a monomial unitary

```text
W:H_S -> ell^2(F_2^k) tensor H_(T_pm)
```

such that

```text
W D_infinity(S) W^*
  contains ell^infinity(F_2^k) tensor D_infinity(T_pm).  (UQR1)
```

Questions outside the support may be assigned arbitrary trivial measurements.
In particular,

```text
dim H_S = 2^k dim H_(T_pm),
dim D_infinity(S) >= 2^k dim D_infinity(T_pm).           (UQR2)
```

The double cover descends to a perfect source strategy `T`, with the same
tensor inclusion, under either exact hypothesis:

1. every supported source question has a positive-weight synchronization
   loop; or
2. the nontrivial supported question graph is bipartite, with any overlap
   of the two sides confined to zero-answer autoaccept anchors.

In the first case the Intro self-loop identifies the A- and B-fiber PVMs.
In the second, select the A fiber on one side and the B fiber on the other.

This boundary records exactly what the displayed equations in BCV Remark
4.22 prove. Item (6) makes the A blocks constant on `s_A` fibers and,
separately, the B blocks constant on `s_B` fibers. Its final prose calls
the restriction honest, but no displayed relation identifies the two blocks
when the same source vertex occurs on both sides. The theorem does not assume
that missing cross-side identity. It is automatic under either condition
above.

The unitary can be chosen monomial in the original Z-aligned coordinate
basis. Thus `(UQR1)` is an inclusion of ZPC readable-translate algebras,
not merely an abstract unitary equivalence of untyped strategies.

This is an exact zero-loss statement. A nonattained sequence of strategies
whose values tend to one gives the same normal form and inclusion only after
passing to a tracial ultraproduct; it need not produce an attained
finite-dimensional source strategy.

The proof is `bcv-perfect-question-reduction-readable-amplification-proof`.
