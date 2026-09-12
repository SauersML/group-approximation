---
rg: 2
id: jacobson-unit-group-symbol-and-index-proof
kind: route
title: Read the symbol of a unit, then kill its shift by a codimension count
target: jacobson-unit-group-is-locally-finite-and-mf
requires: []
artifacts:
  - research/artifacts/jacobson-unit-group-and-rank-four-recheck-2026-09-08.md
---

Section 2 of the artifact is a complete direct proof.

Represent `J` on `V = F_2^(N_0)` by `s v_i = v_(i+1)`,
`t v_0 = 0`, `t v_i = v_(i-1)`. This is faithful: cancelling `ts`
reduces every word to `s^i t^j`, distinct offsets `d = i - j` land in
distinct rows so they cannot cancel, and within one offset the
coefficient at column `k` is a partial sum of the `c_(j+d,j)`, whose
successive differences recover each coefficient.

`e = 1 - st` is the projection onto `v_0`, `f_(ij) = s^i e t^j` is
the matrix unit from `v_j` to `v_i`, and `I = JeJ` is exactly the
finitely supported matrices. Killing `e` makes `s` and `t` mutually
inverse, so `J/I` is `F_2[z,z^-1]` and `I != J`: the defect is
**not** full, which is why the archive's fullness theorems do not apply.

A unit has symbol a unit of `F_2[z,z^-1]`, hence `z^k`, because in a
product the lowest and highest exponents add, so a product equal to one
forces single monomials, with coefficient one over `F_2`. Since `I`
is finitely supported, `g v_i = v_(i+k)` for all large `i`, so
`g V_N = V_(N+k)` for the span `V_N` of `{v_i : i >= N}`. As `g`
is bijective it induces `V/V_N ~= V/V_(N+k)`, of dimensions `N` and
`N+k`, so `k = 0`. Every unit is then a finite invertible block
extended by the identity, and conversely.

MF-ness of a countable increasing union of finite groups is direct: at
stage `N` use the left regular representation of `F_N` and the
identity outside it. Each fixed relation holds exactly for large `N`,
and a nonidentity element eventually moves the identity basis vector to
an orthogonal one, so its distance to `I` is at least `sqrt 2`. No
amenable-approximation theorem is imported.

`ts = 1 != st` because `e != 0`, so `J` is not directly finite, and
the two halves together are the counterexample.
