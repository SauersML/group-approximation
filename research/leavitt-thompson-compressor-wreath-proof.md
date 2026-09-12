---
rg: 2
id: leavitt-thompson-compressor-wreath-proof
kind: route
title: Follow the orbit of the cylinder 1000 under the prefix table of u
target: leavitt-thompson-copy-and-compressor-generate-v-wreath-z
requires: [openai-nine-leaf-leavitt-configuration, leavitt-cylinder-swaps-generate-thompson-in-el, compressor-subgroup-is-directed-union-by-cyclic]
---

The table of `u` is

* `alpha_i -> alpha_i 0`, `beta_i -> alpha_i 1`, `nu_i -> zeta_i`, with
* `alpha = (000, 001, 01)`, `beta = (1000, 1001, 101)`,
  `nu = (1100, 1101, 111)` and `zeta = (100, 101, 11)`.

A prefix replacement conjugates the small copy `V_(c)` supported on a cylinder
`c` inside one source leaf to `V_(u(c))`
(`leavitt-cylinder-swaps-generate-thompson-in-el`; the configuration records
`u J u^(-1) = V_(0001)`).

**Item 1.**

* *Forward orbit.*  `[1000] = [beta_1]` maps to `[alpha_1 1] = [0001]`.  Every
  cylinder `[000 w]` lies in `[alpha_1]` and maps to `[000 0 w]`, so by
  induction `u^k [1000] = [0^(k+2) 1]` for `k >= 1`.
* *Backward orbit.*  `[1000] = [zeta_1 0]` is the image of `[nu_1 0] = [11000]`.
  For `k >= 1`, the cylinder `[1^(k+1) 000]` lies in `[11] = [zeta_3]` and is
  the image of `[nu_3 1^(k-1) 000] = [1^(k+2) 000]`.  So
  `u^(-k) [1000] = [1^(k+1) 000]` for every `k >= 1`.
* *Disjointness.*  Any two of these words disagree at the first position where
  one of them changes letter.  So the cylinders are pairwise disjoint.
* *Commuting and independence.*  An element of `V_(c)` has the form
  `g = 1 + x` with `x in e_c R e_c`.  For disjoint `c`, `c'` the idempotents
  `e_c`, `e_(c')` are orthogonal, so the copies commute.  If
  `prod_k (1 + x_k) = 1` with the `x_k` on disjoint cylinders, the cross terms
  vanish, so `sum_k x_k = 0`; compressing by each `e_(c_k)` gives `x_k = 0`.
  Hence the copies generate their direct sum.

**Item 2.**

* *Semidirect product.*  Conjugation by `u` sends `V_k` to `V_(k+1)` and so
  normalizes `W = directSum_(k in Z) V_k`.  If `u^m in W` with `m != 0`, then
  `u^m` would preserve the cylinder `[1000]`, since every element of `W` does.
  But `u^m [1000]` is disjoint from `[1000]`.  So `<u> cap W = 1` and `u` has
  infinite order.
* *Identification.*  `<J, u> = W semidirect <u>`, which is the restricted wreath
  product `V wr Z` with `u` acting as the shift.

**Item 3.**

* `W_+ = directSum_(k >= 0) V_k` contains `J`, and
  `u W_+ u^(-1) = directSum_(k >= 1) V_k <= W_+`.  So `u` compresses `W_+` and
  `<W_+, u> = <J, u>`.
* By `compressor-subgroup-is-directed-union-by-cyclic`, `<J, u>` is hyperlinear
  if and only if `W_+` is.
* `W_+` is the directed union of the finite direct products `V^n`.
  Hyperlinearity passes to subgroups, finite direct products and directed
  unions, so `W_+` is hyperlinear if and only if `V` is.
