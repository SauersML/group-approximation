---
rg: 2
id: arbitrarily-complex-fp-simple-via-hard-self-similar-groups
kind: route
title: Embed hard finitely presented self-similar groups in finitely presented simple groups and transfer hardness upward
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires:
  - fp-self-similar-groups-with-arbitrarily-hard-word-problem
  - fp-self-similar-groups-embed-in-fp-simple-groups
---

Fix a recursive `T`, and put `T+(m) = m + max_(k<=m) T(k)`, which is
recursive, monotone and at least `T`.

1. **Choose a hard self-similar group.**
   `fp-self-similar-groups-with-arbitrarily-hard-word-problem` gives a
   finitely presented self-similar group `G` whose word problem has no
   algorithm in time `C*T+(C*l) + C*l + C` for any `C`.
2. **Embed it.** By Zaremsky, arXiv:2405.09722 Theorem 1.1
   (`fp-self-similar-groups-embed-in-fp-simple-groups`), `G <= S` for some
   finitely presented simple group `S`.
3. **Transfer upward.** Suppose `S` had a word-problem algorithm in time
   `C_S*T(C_S*l) + C_S*l + C_S`. Write the generators of `G` as words of length
   at most `L` over those of `S`. A word of length `l` over `G` becomes, in time
   `O(L*l)`, a word of length at most `L*l` over `S`, trivial iff the original
   is. That decides `WP(G)` in time at most `C'*T+(C'*l) + C'*l + C'`, using
   monotonicity of `T+` and `T <= T+`. This contradicts step 1.

So `S` beats `T`. This is the substitution of
`complexity-bounded-host-classes-are-not-universal-proof`, run in the other
direction; the embedding need not be effective. `∎`
