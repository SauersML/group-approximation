---
rg: 2
id: non-automorphic-hnn-free-subsemigroup-proof
kind: route
title: Britton's lemma at the junction of a word and the inverse of another
target: non-automorphic-hnn-extensions-contain-free-subsemigroups
requires:
  - proper-self-conjugate-subgroups-force-free-subsemigroups
---

**1.** Let `a in H \ K`, `c_0 = a`, `c_1 = 1`, and for `i in {0,1}^n` put
`w_i = t c_{i_1} t c_{i_2} ... t c_{i_n}`, so the words in `t a, t` of length `n` are exactly the
`w_i`. Take `i != j` and let `k` be the last index with `i_k != j_k`. The factors after position
`k` agree and cancel, so

`w_i w_j^{-1} = t c_{i_1} ... t c_{i_{k-1}} · t (c_{i_k} c_{j_k}^{-1}) t^{-1} · c_{j_{k-1}}^{-1} t^{-1} ... c_{j_1}^{-1} t^{-1}`.

This word has `2k >= 2` letters `t^{±1}`: `k` positive, then `k` negative. A pinch is a subword
`t g t^{-1}` with `g in K` or `t^{-1} g t` with `g in L`. Same-sign neighbours are never pinches,
and the one sign change is `t (c_{i_k} c_{j_k}^{-1}) t^{-1}` with `c_{i_k} c_{j_k}^{-1} in {a, a^{-1}}`,
which is not in `K`. So the word is reduced, and by Britton's lemma it is not the identity. Hence
distinct same-length words give distinct elements, and the length criterion (part 0 of
`proper-self-conjugate-subgroups-force-free-subsemigroups`) gives freeness.

**2.** Presenting `G` with stable letter `s = t^{-1}` gives `s l s^{-1} = psi^{-1}(l)` for `l in L`,
i.e. `G = HNN(H, L, K, psi^{-1})`. Apply part 1 with `b in H \ L`.

**3.** Parts 1 and 2 leave only `K = L = H`. Then `t H t^{-1} = H`, so `H` is normal in
`G = <H, t>`, and `G/H` is infinite cyclic on `t` by the HNN presentation, so `G = H ⋊ <t>`.

**Trust surface.** Britton's lemma (Lyndon–Schupp IV.2.1) is a textbook fact, not re-read.
