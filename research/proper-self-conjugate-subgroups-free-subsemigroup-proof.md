---
rg: 2
id: proper-self-conjugate-subgroups-free-subsemigroup-proof
kind: route
title: Push the stable letter to the right and compare at the first differing letter
target: proper-self-conjugate-subgroups-force-free-subsemigroups
requires: []
---

**0. Length criterion.** Suppose words `w != w'` with `|w| > |w'|` give the same element. Then the
words `w w'` and `w' w` have equal length and give the same element `w^2`. If they differ as
words we are done. Otherwise `w` and `w'` commute as words, so by Lyndon–Schützenberger both are
powers of one word `v`, say `w = v^p`, `w' = v^q`, `p > q`, and `v^{p-q} = 1` in `G`. Then
`v^{p-q} x` and `x v^{p-q}` give the same element `x`; as words they are equal only if `v` is a
power of `x`. Likewise with `y`. A nonempty word cannot be a power of both `x` and `y`, so some
pair of distinct same-length words gives equal elements, contrary to the hypothesis.

**1. Main claim.** Put `phi(g) = t g t^{-1}`, an automorphism of `G` with `phi(H) ⊊ H`, so
`phi^m(H) <= phi^k(H)` for `m >= k`. For `i = (i_1, ..., i_n) in {0,1}^n` put
`u_i = a^{i_1} t a^{i_2} t ... a^{i_n} t`. Since `t g = phi(g) t`, moving every `t` to the right
gives `u_i = g(i) t^n` with `g(i) = a^{i_1} phi(a^{i_2}) ... phi^{n-1}(a^{i_n})`, which lies in `H`.

Let `i != j` and let `k` be the first index with `i_k != j_k`. If `u_i = u_j` then `g(i) = g(j)`.
Cancel the common left factors with index below `k`:
`phi^{k-1}(a^{i_k}) X = phi^{k-1}(a^{j_k}) Y`, where `X, Y` are products of `phi^{m-1}(a^{...})`
with `m > k`, so `X, Y in phi^k(H)`. Apply `phi^{-(k-1)}`: `a^{i_k} X' = a^{j_k} Y'` with
`X', Y' in phi(H)`. Then `a^{-j_k} a^{i_k} = Y' X'^{-1} in phi(H)`. Since `{i_k, j_k} = {0,1}`,
this puts `a` or `a^{-1}` in `phi(H) = t H t^{-1}`, contradicting the choice of `a`. So distinct
words of equal length in `t, a t` give distinct elements, and part 0 gives freeness.

**2. Growth.** Fix a finite generating set and let `c` bound the word lengths of `t` and `a t`.
The ball of radius `c n` contains the `2^n` distinct elements `u_i`, so growth is at least
`2^{n/c}`. Subexponential growth therefore excludes such `(H, t)`.

**3. Ascending HNN extensions.** In `<H, t | t h t^{-1} = theta(h)>` the base `H` embeds (standard
normal form theory of HNN extensions, Lyndon–Schupp IV.2; not re-read) and
`t H t^{-1} = theta(H) ⊊ H`. Apply part 1, then part 2 when the group is finitely generated.

**Trust surface.** Lyndon–Schützenberger (commuting words are powers of a common word) and the
embedding of the base of an HNN extension are textbook facts, not re-read.
