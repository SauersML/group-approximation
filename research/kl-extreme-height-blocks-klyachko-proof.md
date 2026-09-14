---
rg: 2
id: kl-extreme-height-blocks-klyachko-proof
kind: route
title: Cut at the first maximum, split the product of conjugates at its extreme marks into Klyachko's form (1), and verify Lemma 2 with the stripped free-factor criterion
target: kl-holds-when-extreme-height-blocks-have-infinite-order
requires: [klyachko-lemma-2-solves-relatively-free-shift-systems, stripped-infinite-order-elements-are-free-over-a-factor]
artifacts:
  - research/artifacts/hl-kl-two-level-words-2026-09-14.md
---

Notation of the target. `P_m = gp(G^[i] : 0 <= i <= m)` and
`R_m = gp(G^[i] : 1 <= i <= m)` inside `G * <t>`, and `phi(p) = t^(-1) p t`
(Klyachko 1993, p. 2572). The subgroup `gp(G^[i] : i in Z)` of `G * <t>` is the
free product of the `G^[i]`: it is the kernel of `G * <t> -> Z`, and its
Bass--Serre tree has trivial edge groups. So `P_m = G^[0] * ... * G^[m]`,
`R_m = G^[1] * ... * G^[m]`, and `phi : P_(m-1) -> R_m` is an isomorphism
shifting indices by one.

**0. The canonical cut.** Let `M = max_(1 <= j <= n) h_j` and
`j_0 = min{ j : h_j = M }`.
- For `q in [j_0, n]`: `h_q <= M`.
- For `q = q' + n` with `q' in [1, j_0 - 1]`: `h_q = h_(q') + 1 <= (M - 1) + 1 = M`,
  since `h_(q') < M` is an integer.
- So `h_q <= h_(j_0)` on `[j_0, j_0 + n - 1]`.
- Uniqueness. Let `j in [1, n]` be another such position. If `j < j_0`, the
  window contains `j_0`, so `h_j >= M` and `h_j = M`, contradicting minimality
  of `j_0`. If `j > j_0`, the window contains `j_0 + n` with
  `h_(j_0+n) = M + 1 > h_j`.

After rotating, `h_j <= 0 = h_1` for all `j <= n`. `k_1 = h_2 <= 0` and
`k_1 != 0` give `s >= 1`.

**1. The product of conjugates.** `v = w t^(-1) = g_1 t^(k_1) ... g_n t^(k_n - 1)`.
Inserting `t^(h_j) t^(-h_j)` before each `g_j` gives

    v = prod_j t^(h_j) g_j t^(-h_j) · t^(h_(n+1) - 1) = prod_j g_j^[-h_j] = prod_j g_j^[i_j],

since `h_(n+1) = sum k_j = 1`. Consecutive indices differ by `k_j != 0`, so this is
a reduced word in `P_s`, with syllables the copies of the coefficients.

**2. Form (1).** Let the runs be `B_0, T_0, ..., B_k, T_k` and possibly `B_(k+1)`, as
in the target.
- `b_i` = the subword from just after the last mark of `T_(i-1)` (from position 1
  if `i = 0`) through the last mark of `B_i`.
- `h_i` = the subword from just after the last mark of `B_i` through the last mark
  of `T_i`.
- `c` = the rest, from just after the last mark of `T_k` to position `n`.

Then `v = b_0 h_0 b_1 h_1 ... b_k h_k c` as words. Moreover:
- `b_i` contains no top mark, so `b_i in P_(s-1)`. It contains a bottom mark, so
  `b_i` is not in `R_(s-1)`.
- `h_i` contains no bottom mark, so `h_i in R_s`. It contains a top mark, so `h_i`
  is not in `R_(s-1)`.
- `c` contains no top mark, so `c in P_(s-1)`.

Put `m = s - 1` and `a_i = phi^(-1)(h_i) = t h_i t^(-1) in P_m`. Then
`h_i = t^(-1) a_i t`, and

    w = v t = ( prod_(i=0)^k b_i t^(-1) a_i t ) c t,

with `a_i, b_i, c in P_m`, `a_i` not in `P_(m-1)` (it has an index-`m` syllable),
and `b_i` not in `R_m` (it has an index-`0` syllable). This is Klyachko's form
(1). It needs none of the minimality in his Lemma 3, and we never apply Lemma 3.

**3. Lemma 2's hypotheses.** Work in `H = P_m` with `P = P_(m-1)`, `P^phi = R_m`.
- *For `a_i`.* `H = P_(m-1) * G^[m]` and `a_i in H \ P_(m-1)`. Take
  `A = P_(m-1)` and `B = G^[m]`. The syllables of `a_i` in `A * B` are its
  index-`m` coefficient copies and the maximal runs of lower-index syllables
  between them. Stripping the `A`-syllables at both ends leaves
  `phi^(-1)(block of T_i)`. By item 1 of
  `stripped-infinite-order-elements-are-free-over-a-factor`,
  `gp(a_i, P_(m-1)) = <a_i>_inf * P_(m-1)` iff that core has infinite order.
  Since `phi^(-1)` is an isomorphism onto its image, this holds iff the block of
  `T_i` has infinite order.
- *For `b_i`.* `H = G^[0] * R_m` and `b_i in H \ R_m`. Take `A = R_m` and
  `B = G^[0]`. Stripping the `R_m`-syllables at both ends of `b_i` leaves the
  block of `B_i`. So `gp(b_i, R_m) = <b_i>_inf * R_m` iff that block has infinite
  order.
- The final run `B_(k+1)` lies in `c`, on which Lemma 2 imposes nothing.

So the hypothesis of the target gives exactly the hypotheses of
`klyachko-lemma-2-solves-relatively-free-shift-systems`.

**4. Solving and embedding.** By Lemma 2, some `H~ >= H` contains `t~` with
`(prod b_i t~^(-1) a_i t~) c t~ = 1` and `t~^(-1) p t~ = phi(p)` for all
`p in P_(m-1)`. Define `psi : G * <t> -> H~` by `g -> g in G^[0] <= H` and
`t -> t~`.
- For `g in G` and `0 <= i <= m`, induction on `i` using
  `t~^(-1) p t~ = phi(p)` for `p in G^[i-1] <= P_(m-1)` gives
  `psi(t^(-i) g t^i) = t~^(-i) g t~^i = g^[i]`. So `psi` is the identity on `P_m`,
  as a map into `H <= H~`.
- Hence `psi(w) = (prod b_i t~^(-1) a_i t~) c t~ = 1`, and `psi` factors through
  `K = (G * <t>)/<<w>>`.
- The composite `G -> K -> H~` is the inclusion `G = G^[0] <= H <= H~`, which is
  injective. So `G -> K` is injective.

**5. Item 2 and the corollary.** Item 2 of the target is item 2 of
`stripped-infinite-order-elements-are-free-over-a-factor`: each constrained
block is reduced, with first and last syllables at the same extreme index.

For the corollary, consider a constrained block.
- A block with one mark is a single extreme coefficient, which has infinite order
  by the first hypothesis.
- A block with at least two marks has first and last syllables that are marked
  coefficients at the same index. By the second hypothesis they are not mutual
  inverses, so the block is not an inverse palindrome, and it has infinite order
  by item 2.

**Degree `-1`.** `<<w>> = <<w^(-1)>>`, and `w^(-1)` has degree `1` with inverted
coefficients, whose orders are unchanged.
