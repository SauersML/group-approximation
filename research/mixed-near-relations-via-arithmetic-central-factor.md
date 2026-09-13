---
rg: 2
id: mixed-near-relations-via-arithmetic-central-factor
kind: route
title: Realize the central infinite cyclic factor by a free residue-affine permutation and read off the mixed relation
target: route-form-shell-inputs-have-computable-mixed-near-relations
requires:
  - arithmetic-near-shift-actions-have-mixed-relations
artifacts:
  - research/artifacts/shell-envelope-local-tests-2026-09-13.md
---

**Orbits of `lambda'`.** Write `lambda` for the unmodified formula,
which holds for every `n >= 4`. The four affine pieces map the residue
classes `0, 1, 2, 3 mod 4` bijectively onto `0 mod 8`, the odd numbers,
`4 mod 8` and `2 mod 4`. These images partition `N`, so `lambda` is a
bijection. Its only fixed points are `0` and `1`, and `lambda(3) = 2`.
Changing it to `lambda'(3) = 0`, `lambda'(0) = 1`, `lambda'(1) = 2`
permutes the three values `{0,1,2}` among the same three arguments, so
`lambda'` is again a bijection.

Inverse formulas for `lambda`:
- an odd `m` has preimage `2m-1`, which is `1 mod 4`;
- `e = 0 mod 8` has preimage `e/2`;
- `e = 4 mod 8` has preimage `e/2`;
- `e = 2 mod 4` has preimage `e+1`, which is `3 mod 4`.

Consider an element `q = 3 mod 4` with `q >= 7`. Forward, `q` goes to
`q-1 = 2 mod 4` and then doubles through even numbers forever.
Backward, the preimages `2m-1` of odd numbers stay `1 mod 4` and
increase strictly. So the orbit of `q` is bi-infinite and contains no
other element `3 mod 4`.

The orbit of `3` under `lambda'` is `..., 17, 9, 5, 3, 0, 1, 2, 4, 8, ...`,
which is also bi-infinite.

Every `n` lies on one of these orbits:
- an even `n > 2` halves backward until it is `2 mod 4`, then steps
  back to `n+1 = 3 mod 4`;
- an odd `n = 4k+1` with `k >= 1` moves forward by `n -> (n+1)/2`, a
  strictly decreasing sequence of odd numbers `>= 3`, until it reaches
  `3 mod 4`;
- `0, 1, 2` lie on the orbit of `3`.

Hence `<lambda'>` acts freely on `N`. Every orbit is bi-infinite, and
the orbits correspond bijectively to the residue class `3 + 4N`.

**The enumeration.** Choose a bijection `beta: P_0 -> 3 + 4N` and put
`nu(x, t^k) = lambda'^k(beta(x))`. Because the orbits partition `N` and
`k` indexes each orbit bijectively, `nu` is a bijection. Since `t` is
central and `t (x, t^k) = (x, t^(k+1))`, we get
`lambda_t(nu(x,t^k)) = nu(x,t^(k+1)) = lambda'(nu(x,t^k))`, that is,
`lambda_t = lambda'`.

**The relation.** For `n >= 4`, `lambda'` has the eventual formulas
`lambda'(4k+r) = a_r k + b_r` with `(a_r, b_r) = (8,0), (2,1), (8,4),
(4,2)`, all `a_r > 0`. Then `A = lcm(8,2,8,4) = 8`, and
`arithmetic-near-shift-actions-have-mixed-relations` gives
`[lambda_t s^4 lambda_t^-1, s^8] = 1` in `NearSym(N)`.

Directly: on the image piece `{a_r k + b_r}`, the germ of
`lambda' s^4 lambda'^-1` is the translation by `a_r`. Each piece is a
union of residue classes mod 8 that the translation preserves, so the
translation commutes with `s^8` near infinity.

Since `t != 1`, the word `t s^4 t^-1 s^8 t s^-4 t^-1 s^-8` is reduced
and nonidentity in `P*<s>`. The cited claim therefore makes
`R_nu != P*<s>`, and the free-near-shift obstruction, which requires
`R_nu = P*<s>`, does not apply.

**Computability.** Suppose `P_0` has decidable word problem.
- **`beta`.** List the words in its generators, and use the word
  problem to discard each word equal to an earlier one. This gives a
  computable listing of `P_0` without repetition, hence a computable
  bijection `beta` with computable inverse.
- **`nu`.** The piece formulas make `lambda'` and `lambda'^-1`
  computable, so `nu` is computable.
- **`nu^-1`.** Given `n`, iterate `lambda'^-1` from an even `n`, or
  `lambda'` from an odd `n = 1 mod 4`. This reaches the unique element
  `q = 3 mod 4` of the orbit after finitely many steps, by the orbit
  analysis above; `0, 1, 2` are handled directly. The step count gives
  `k`, and `beta^-1(q)` gives `x`.
