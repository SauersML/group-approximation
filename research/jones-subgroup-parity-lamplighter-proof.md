---
rg: 2
id: jones-subgroup-parity-lamplighter-proof
kind: route
title: Leaf parities give the defect cocycle, and parity-word languages transport singleton defects by Jones' subgroup
target: jones-subgroup-cosets-form-a-parity-lamplighter
requires: [jones-subgroup-is-stabilizer-of-odd-digit-sum-dyadics]
artifacts:
  - research/artifacts/ideas-wildcards-2026-09-14.md
---

Full proof: `research/artifacts/ideas-wildcards-2026-09-14.md`, section "Execution of W2", Lemmas 1–7 and
Theorems A–B. Outline:

1. **Defect formula.** If `g` maps the leaf `u_i` to `v_i`, then `p(t) + p(gt) = p(u_i) + p(v_i)` on `I_(u_i)`.
   Comparing `[t − 2^(−n), t) = I_(w01^(n−m))` with its image `I_(w'01^(n−s−m'))` shows a jump at `t` iff
   `ℓ(gt) − ℓ(t) + s` is odd.
2. **Cocycle.** `p(t) + p(ght) = d_h(t) + d_g(ht)`, and jump sets of mod-2 sums add. The kernel `{g : p∘g = p on D}`
   is `Stab_F(S) = \vec F` by the cited theorem.
3. **Base elements.** `J(x_0) = {3/4}` and `J(x_0⁻¹) = {1/2}`. Copies into `[1 − 2^(−j), 1]` (`j = 1, 2`) give
   elements that are the identity on `[0, 1 − 2^(−j)]` with singleton defects of all four parity patterns
   `(p(left end), p(defect))`.
4. **Parity words.** Subdivisions of a standard interval of parity `q` realize exactly the words
   `{q} ∪ q(q+1){0,1}*`. Hence any two intervals `[a,b)`, `[a',b')` with `p(a) = p(a')` share a subdivision
   parity word.
5. **Transport.** `\vec F` maps any dyadic pair `c < t` to any pair `c' < t'` with the same parity pattern: glue
   common words on `[0,c)`, `[c,t)` and `[t,1)`. Conjugating a base element by such `k` gives an element that is
   the identity on `[0,c]` with defect set `{t}`.
6. **Induction.** For `E = {t_1 < … < t_k}`, compose an element realizing `E∖{t_k}` with one that is the identity
   on `[0,c]`, `t_(k−1) < c < t_k`, with defect `{t_k}`.

**Checks run (local, tiny; the proof does not depend on them).** Exact rational implementations of
`x_0^(±1)` and `x_1^(±1)` were used.
- The jump set of `p(g⁻¹t) + p(t)` on a `2^(−10)` grid agreed with the affine model on 150 random words
  (0 mismatches).
- The depth/derivative defect formula agreed with the model on 40 random words (0 mismatches).
- Within word length 9, the orbit of `∅` contains all subsets of `{k/4}`, all singletons `{k/16}`, and 113 of
  the 128 subsets of `{k/8}`.
