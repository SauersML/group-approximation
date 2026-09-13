---
rg: 2
id: thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words-proof
kind: route
title: Round the finite subgroups, keep the free part, glue along a, then amplify back
target: thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words
requires:
  - thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3
  - thompson-v-finitely-presented-infinite-simple
---

Numbering follows the claim. `d` is the normalized Hamming distance, `G0 = S4 *_<a> S3`. By
`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, `<a,b> = S4` and `<a,c> = S3` inside `V`,
and `V = G0 / <<r5, r6, r7, r8>>`.

**`2 <=> 3`.** A free gluing of size `L` has `24 | L`. Identify its `S4`-set with `(a_0, b_0)`. Its
`S3`-set is isomorphic to `(a_0, c_0)` by a bijection `nu`, and `nu` commutes with `a_0` because both
`S3`-structures give `a` the action `a_0`. Conversely every `nu in C(a_0)` gives a free gluing.

**Lemma (finite groups round linearly).** Let `H = <S | R_H>` be finite, with words `w_h` (`w_e`
empty). There is `C_H` such that if permutations `sigma(s)` of `X` make each `r in R_H` move at most
`delta|X|` points, then some `H`-action `rho` on `X` has `rho(s) = sigma(s)` off `C_H delta |X|` points.
*Proof.*
- Each `u_(h,s) = w_h s w_(hs)^-1` is trivial in `H`, so it is freely equal to a product of
  `N_(h,s)` conjugates `v r^(+-1) v^-1`. If `x . sigma(u_(h,s)) != x`, some factor moves the running
  point. For each factor, the running point is a bijective image of `x`, so at most `delta|X|`
  points `x` fail there.
- Call `x` good if `x . sigma(w_h s) = x . sigma(w_(hs))` for all `h, s`. At most
  `sum N_(h,s) delta |X|` points are bad.
- For good `x`, `O_x = {x . sigma(w_h)}` is `sigma(S)`-invariant. Each relator fixes it pointwise,
  since `x . sigma(w_h r) = x . sigma(w_(hr))`. So `O_x` is an `H`-set.
- Their union is invariant, so its complement is too. Let `rho = sigma` on the union and trivial
  on the complement. ∎

**`1 => 2`.** Take sofic approximations `sigma_n : V -> Sym(k_n)`: `sigma_n(e) = id`,
`d(sigma_n(gh), sigma_n(g) sigma_n(h)) -> 0`, and `d(sigma_n(g), id) -> 1` for `g != e`. Put
`A, B, C = sigma_n(a), sigma_n(b), sigma_n(c)`.
- **Relators.** A word trivial in `V` has defect at most the sum of the multiplicativity defects
  along its prefixes. So every word of `R_S4`, `R_S3` and `r5, ..., r8` has defect `delta_n -> 0`
  on `(A, B, C)`.
- **Rounding.** The Lemma gives actions `rho4` of `S4` and `rho3` of `S3` that agree with
  `(A, B)` and `(A, C)` off `O(delta_n k_n)` points.
- **Almost free.** For `h in S4 \ {e}`, `rho4(h)` agrees with `w_h(A, B)` off
  `|w_h| O(delta_n k_n)` points. `w_h(A, B)` is `o(1)`-close to `sigma_n(h)`, which fixes `o(k_n)`
  points because `h != e` in `V`. So the points with nontrivial `rho4`-stabilizer form a union of
  orbits of size `o(k_n)`. Its complement `X4` is a free `S4`-set. `X3` is defined the same way.
- **Glue.**
  - Let `T = {x in X4 ∩ X3 : x . rho4(a) = x . rho3(a)}`, so `|[k_n] \ T| = o(k_n)`. `T` is
    invariant under the common `a`: `X4` and `X3` are unions of orbits, and `a` is an involution.
  - Choose `L >= k_n` with `24 | L` and `L - k_n < 24`. Pad `X4` with `(L - |X4|)/24` free
    `S4`-orbits and `X3` with `(L - |X3|)/6` free `S3`-orbits.
  - The complements of `T` carry free `a`-actions of equal size. So there is an `a`-equivariant
    bijection `phi` of the padded sets that is the identity on `T`.
  - Transporting the `S3`-action along `phi` gives a free gluing `Y` of size `L`.
- **Defect.**
  - `a`, `b`, `c` on `Y` agree with `A`, `B`, `C` off a set `E` with `|E| = o(L)`: points outside
    `T`, padding, rounding errors, and their `c`-preimages.
  - For a word of length `l`, a point whose `Y`-trajectory avoids `E` is moved on `Y` exactly
    when it is moved by the word in `(A, B, C)`.
  - Trajectory positions are bijective images of the start, so at most `l|E|` starts meet `E`.
    Hence each `r_i` moves `o(L)` points of `Y`.

**`2 => 1`.** Let `Y_n` be free gluings whose long-word defects satisfy `epsilon_n -> 0`. Fix words
`w_g` with `w_e` empty, and put `sigma_n(g) = w_g(a, b, c)` on `Y_n`.
- **Multiplicative.** `w_g w_h w_(gh)^-1` is trivial in `V`. So it is freely equal to a product of
  `N_(g,h)` conjugates of relators of `G0` and of `r_i^(+-1)`. The first hold exactly on `Y_n`, and
  each of the others moves at most `epsilon_n |Y_n|` points. So
  `d(sigma_n(g) sigma_n(h), sigma_n(gh)) <= N_(g,h) epsilon_n`.
- **Separated.** Fix a nonprincipal ultrafilter `omega` and put
  `delta_g = lim_omega d(sigma_n(g), id)`.
  - `{g : delta_g = 0}` is a normal subgroup, because `d` is bi-invariant and `sigma_n` is
    asymptotically multiplicative.
  - It omits `a`, which moves every point.
  - `V` is simple (`thompson-v-finitely-presented-infinite-simple`). So `delta_g > 0` for every
    `g != e`.
- **Amplify.**
  - The diagonal action on `Y_n^m` satisfies
    `d(sigma_n^(m)(g), id) = 1 - (1 - d(sigma_n(g), id))^m`. Its multiplicativity defect is at most
    `m` times that of `sigma_n`.
  - Given finite `F` and `eta > 0`, let `delta = min_(F \ e) delta_g`, and choose `m` with
    `(1 - delta/2)^m < eta`.
  - Choose `n` in the `omega`-large set where `d(sigma_n(g), id) > delta/2` on `F \ {e}` and the
    defects on `F x F` are below `eta/m`.
  - Then `sigma_n^(m)` is an `(F, eta)`-approximation, so `V` is sofic. ∎
