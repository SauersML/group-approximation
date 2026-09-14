---
rg: 2
id: stripped-infinite-order-free-factor-proof
kind: route
title: Conjugate the core into cyclically reduced form, then check that no junction of A-syllables and powers of the core reduces
target: stripped-infinite-order-elements-are-free-over-a-factor
requires: []
artifacts:
  - research/artifacts/hl-kl-two-level-words-2026-09-14.md
---

Notation of the target. All words are normal forms in the free product; a
syllable is a nontrivial element of one factor, and consecutive syllables lie
in different factors.

**2. Finite-order criterion.** Let `gamma = gamma_1 ... gamma_L` be reduced.
- If `L >= 2` and `gamma_1`, `gamma_L` lie in different factors, then `gamma` is
  cyclically reduced, so `gamma^e` is the `|e|`-fold concatenation of `gamma` or
  its inverse. It has length `|e| L != 0`, so `gamma` has infinite order.
- Suppose `gamma_1`, `gamma_L` lie in the same factor. Conjugating by `gamma_L`
  gives `gamma_L gamma gamma_L^(-1) = (gamma_L gamma_1) gamma_2 ... gamma_(L-1)`.
  - If `gamma_L gamma_1 != 1`, this word is reduced of length `L - 1`. Its first
    syllable lies in the factor of `gamma_1` and its last in the factor of
    `gamma_(L-1)`, which differs from that of `gamma_L`, hence from that of
    `gamma_1`. So it is cyclically reduced. `L = 2` cannot occur, since then
    `gamma_1`, `gamma_2` would be adjacent syllables in one factor. So
    `L - 1 >= 2`, and `gamma` has infinite order.
  - If `gamma_L gamma_1 = 1`, then `gamma` is conjugate to
    `gamma_2 ... gamma_(L-1)`, and we recurse.
- The recursion stops at a reduced word of length `0` (impossible, since `gamma`
  is nontrivial and each step removes exactly two syllables: for `L` even the
  last step would leave two adjacent syllables in one factor that are mutual
  inverses, contradicting reducedness), of length `1`, or of length `>= 2` with
  different end factors. It reaches length `1` exactly when `L` is odd and
  `gamma_(L+1-r) gamma_r = 1` for every `r <= (L-1)/2`. The length-one conjugate
  is the middle syllable, so `gamma` has the order of the middle syllable. Every
  other outcome gives infinite order.

**1. Free-factor criterion.** Write `u = x u' x'` as in the target.

- *The core's powers begin and end in `B`.* Write `u' = y v y^(-1)` with `v`
  cyclically reduced and the product reduced; this is standard in free
  products.
  - If `|v| >= 2`, then `u'^e = y v^e y^(-1)` is reduced of length at least 2 for
    `e != 0`, with the same first and last syllables as `u'`, which lie in `B`.
  - If `|v| = 1` and `v` has infinite order, then `u'^e = y v^e y^(-1)` is reduced
    with `v^e != 1`. Its first syllable is the first syllable of `u'` when
    `y != 1`. When `y = 1`, `u' = v in B`, and `v^e` is a nontrivial element of `B`.
    Either way it begins and ends in `B`.
  - By part 2, `u'` has infinite order exactly in these two cases.
- *Injectivity when the core has infinite order.* Let `theta : A * <z> -> A * B`
  be the identity on `A` with `z -> u'`. A nontrivial reduced word of
  `A * <z>` has the form
  `omega = a_0 z^(e_1) a_1 z^(e_2) ... z^(e_q) a_q`, with `e_i != 0`,
  `a_i in A \ {1}` for `0 < i < q`, and `a_0`, `a_q` possibly trivial.
  - If `q = 0`, then `theta(omega) = a_0 != 1`.
  - If `q >= 1`, each `u'^(e_i)` is a reduced word beginning and ending in `B`.
    At a junction `u'^(e_i) a_i u'^(e_(i+1))`, the syllable `a_i in A \ {1}` sits
    between two `B`-syllables, so nothing cancels or merges. The same holds at
    `a_0 u'^(e_1)` and `u'^(e_q) a_q`.
  - So `theta(omega)` has a reduced form of length at least
    `sum |u'^(e_i)| > 0` and is nontrivial. Hence `theta` is injective, and
    `gp(A, u') = A * <u'>_inf`.
  - Since `x, x' in A`, the substitution `z -> x z x'` is an automorphism of
    `A * <z>` fixing `A`. Composing it with `theta` sends `z -> u`, so the map
    `z -> u` is injective as well, and `gp(A, u) = gp(A, u') = A * <u>_inf`.
- *Failure when the core has finite order `k`.* Then
  `omega = (x^(-1) z x'^(-1))^k` is nontrivial in `A * <z>`. When
  `x'^(-1) x^(-1) = 1` it reduces to `x^(-1) z^k x'^(-1)`; otherwise it is
  already reduced. Its image is `(x^(-1) u x'^(-1))^k = u'^k = 1`. So the natural
  map is not injective, and `gp(A,u)` is not the free product `A * <u>_inf`
  along the natural map.
