---
rg: 2
id: inner-realizers-are-at-least-half-the-sofic-radius
kind: claim
title: A blockwise inner-times-centralizer realizer of an element outside the kernel is a word at least half as long as the local sofic radius
distinct_from:
  bounded-blockwise-inner-realizers-fail-off-kernel: that shows realizers drawn from a fixed finite subset of the kernel occupy vanishing mass; this is a finite-stage inequality bounding the mass realized by words of length at most l by the mass where the edited sofic radius is below 2l + O(1), so realizers of any length are pinned to the scale of that radius.
  kun-expander-decomposition-formalized: that produces the expander blocks of the kernel; this bounds the length of kernel words that can realize an element outside the kernel on those blocks.
---

**ESTABLISHED.** Let `1 -> N -> G -> Q -> 1` be exact with `G` countable, `N`
Kazhdan with finite symmetric generating set `S`, and `C_G(N) = 1`. Let
`sigma_n : G -> Sym(X_n)` be a sofic approximation along `U`. Fix an edit
(`kun-expander-decomposition-formalized`): permutations `s~` of `X_n`
(`s in S`), each agreeing with `sigma_n(s)` off `o(|X_n|)` points, whose
`S`-graph is a disjoint union of blocks `B` with a uniform Cheeger constant.
Write `s_B` for the restriction of `s~` to `B`, `Pi_B = <s_B : s in S>`, and
`C_B` for the centralizer of `Pi_B` in `Sym(B)`.

- **Edited sofic radius.** `rho_n(x)` is the largest `r` such that for all words
  `u, u'` in `S` of length at most `r`: `u(s~) x = u'(s~) x` iff `u = u'` in `N`.
- **Realizers.** Fix `g in G \ N` and, for each `s in S`, a word `v_s` in `S`
  representing `g s g^-1`; put `L_g = max_s |v_s|`. A block `B` is
  `(w, eps)`-realized if `w` is a word in `S` and some `c in C_B` makes
  `sigma_n(g)` and `w(s_B) c` agree on at least `(1 - eps)|B|` points of `B`.
- **Error set.**
  `E_n = { y : v_s(s~) y != sigma_n(g) s~ sigma_n(g)^-1 y for some s in S }`,
  and `e_B = |E_n cap B|`.

Then `|E_n| = o(|X_n|)` along `U`, and for every `l >= 0` and `0 <= eps < 1/2`:

```text
sum over the blocks B that are (w_B, eps)-realized with |w_B| <= l  of  ((1 - 2 eps)|B| - e_B)
    <=  |{ x in those blocks : rho_n(x) < 2l + L_g + 1 }| .
```

Per block: if `B` is `(w, eps)`-realized and more than `2 eps |B| + e_B` points
of `B` have `rho_n >= r`, then `|w| >= (r - L_g - 1)/2`.

Derivation: `inner-realizer-length-radius-proof`.

**Consequences.**
- For each fixed `r`, `|{rho_n < r}| = o(|X_n|)` along `U`, so realizers of
  bounded length occupy `o(|X_n|)` mass. Words from a fixed finite `F ⊂ N` agree
  with `sigma_n` of their elements off `o(|X_n|)` points, so this recovers
  `bounded-blockwise-inner-realizers-fail-off-kernel`.
- Realizers of any length sit at the scale of the sofic radius: on blocks where
  most points have radius at least `r`, every realizer word has length at least
  about `r/2`. On a block that is the Cayley graph of `Pi_B`, every element of
  `Pi_B` is a word of length at most the diameter, which is `O(log |B|)` for
  bounded-degree expanders. There realizer words have length between about half
  the radius and `O(log |B|)`.

**Scope.** Elementary: trace zero, `C_G(N) = 1`, and the block partition. It
proves nothing about soficity. The unbounded case is analysed further in
`kernel-block-realizers-need-no-centralizer-factor` and
`leavitt-cover-regular-realizer-models-iff-residually-finite`.
