---
rg: 2
id: kl-holds-when-extreme-height-blocks-have-infinite-order
kind: claim
title: A unimodular equation injects its coefficient group when the coefficient blocks at the extreme heights of its canonical cut have infinite order
distinct_from:
  klyachko-kl-holds-when-all-coefficients-have-infinite-order: that needs every coefficient to have infinite order; this needs infinite order only for the blocks at the minimal and maximal heights, and there only away from the middle of inverse palindromes, so finite-order coefficients may sit at every intermediate height.
  kl-sign-index-two-infinite-order-loops-inject: that handles exactly two sign changes, any nonzero degree, and needs infinite order at both sign-change coefficients; at degree one this theorem recovers it, since those two coefficients are exactly its constrained blocks, and it allows any number of sign changes.
  kl-four-same-sign-corner-words-inject: that fences by coincidences among same-sign corners via a weight test and allows torsion loops; this fences by the positions of finite-order coefficients along the height walk and imposes nothing on coincidences.
  kl-two-level-words-over-torsion-free-by-cyclic: that is the open two-level case over a torsion-free subgroup of finite cyclic index; this is a general theorem over every group, which settles the two-level words whose finite-order coefficients avoid its constrained blocks.
artifacts:
  - research/artifacts/hl-kl-two-level-words-2026-09-14.md
---

Let `G` be any group and `w in G * <t>` with `deg_t(w) = ±1`. If the degree is
`-1`, replace `w` by `w^(-1)`, which has the same normal closure and inverted
coefficients. So assume `deg_t(w) = 1`, and take a cyclically reduced conjugate
in normal form

    w = g_1 t^(k_1) g_2 t^(k_2) ... g_n t^(k_n),     g_j in G \ {1},  k_j != 0,  sum k_j = 1.

If `n <= 1`, then `w` is conjugate to `t` or `g t`, and `G` embeds trivially.
Assume `n >= 2`.

## The canonical cut and its blocks

- **Heights.** Put `h_1 = 0`, `h_(j+1) = h_j + k_j`, and extend periodically with
  drift, `h_(j+n) = h_j + 1`.
- **The canonical cut.** Let `j_0` be the first `j in {1, ..., n}` where `h_j` is
  maximal. It is the unique `j` (mod `n`) with `h_q <= h_j` for all
  `q in [j, j+n-1]`. Rotate `w` so that `j_0 = 1`. Then every `h_j <= 0`.
- **Indices.** Put `i_j = -h_j in [0, s]`, where `s = max_j i_j >= 1`, and
  `G^[i] = t^(-i) G t^i`. Then

      v = w t^(-1) = g_1^[i_1] g_2^[i_2] ... g_n^[i_n]

  is a reduced word in the free product `*_(0 <= i <= s) G^[i]`.
- **Marks.** A position `j` is a *bottom mark* if `i_j = 0` and a *top mark* if
  `i_j = s`. Scanning `j = 1, ..., n`, the marks form alternating maximal runs
  `B_0, T_0, B_1, T_1, ..., B_k, T_k`, possibly followed by a *final* bottom
  run `B_(k+1)`. The run `B_0` contains `j = 1`.
- **Blocks.** The *block* of a run is the subword `g_p^[i_p] ... g_q^[i_q]` of `v`
  from the first mark `p` of the run to its last mark `q`. The *constrained
  blocks* are those of `T_0, ..., T_k` and `B_0, ..., B_k`. The final run
  `B_(k+1)`, if present, is unconstrained.

## Theorem

1. **Main statement.** If every constrained block has infinite order in
   `*_i G^[i]`, then `G -> (G * <t>)/<<w>>` is injective.
2. **Checkable form.** A constrained block `gamma_1 ... gamma_L` has finite
   order iff `L` is odd, it is an inverse palindrome
   (`gamma_(L+1-r) = gamma_r^(-1)`, same index and inverse coefficient, for
   `r <= (L-1)/2`), and its middle coefficient has finite order in `G`
   (`stripped-infinite-order-elements-are-free-over-a-factor`, item 2). So `G`
   embeds unless some constrained block is an odd inverse palindrome around a
   finite-order coefficient.
3. **Corollary.** Suppose:
   - every coefficient at index `0` or index `s` of the canonical cut has
     infinite order, and
   - in every constrained block with at least two marks, the first and last
     marked coefficients are not mutual inverses.

   Then `G` embeds.

## What it changes

- **Recovers the known theorems.**
  - If all coefficients have infinite order, every block does, which is
    `klyachko-kl-holds-when-all-coefficients-have-infinite-order`.
  - At degree one with exactly two sign changes, the constrained blocks are
    exactly the two sign-change coefficients, which is the degree-one case of
    `kl-sign-index-two-infinite-order-loops-inject`. Model-tested in the
    artifact.
- **Torsion at intermediate heights is harmless.** A finite-order coefficient
  that is not the middle of an odd inverse-palindromic constrained block imposes
  nothing. That includes every coefficient strictly between index `0` and index
  `s`, and every coefficient in the final bottom run. In particular a
  sign-change coefficient at a local but not global extremum of the height walk
  may be an involution.
- **Where a violation must sit.** A Kervaire--Laudenbach violation of degree
  `±1` needs, at the canonical cut of `w` (or of `w^(-1)`), a constrained block
  that is an odd inverse palindrome around a finite-order coefficient. The
  simplest such blocks are single extreme-height coefficients of finite order.

**Example.** `w = g_1 t^(-1) g_2 t^(-1) g_3 t g_4 t^(-1) g_5 t g_6 t g_7 t`
has indices `(0,1,2,1,2,1,0)`, `s = 2`.
- The constrained blocks are `g_1` and `g_3^[2] g_4^[1] g_5^[2]`; the final
  bottom run `{g_7}` is exempt.
- `G` embeds whenever `g_1` has infinite order and either `g_5 != g_3^(-1)` or
  `g_4` has infinite order.
- So `g_2`, `g_4` (a sign-change coefficient at a local maximum), `g_6` and
  `g_7` may all be involutions, and so may `g_3`, `g_5` when `g_5 != g_3^(-1)`.

**ESTABLISHED** through `kl-extreme-height-blocks-klyachko-proof`. This is
Klyachko's proof of Theorem 4 with the canonical cut in place of Lemma 3 and the
sharpened free-factor fact in place of his simple fact. The car-crash lemma is
imported as published. Not independently reviewed. No novelty claimed; the
literature after Klyachko 1993 was not searched for this form.
