---
rg: 2
id: dehn-function-bound-gives-word-problem-time-bound-proof
kind: route
title: Enumerate products of boundedly many relator conjugates with bounded conjugators
target: dehn-function-bound-gives-word-problem-time-bound
requires: []
---

Let `rho = max(1, max_(r in R) |r|)` and `K` the constant with
`delta_S(n) <= K f(Kn) + Kn`.

**Step 1: conjugator lengths.** Let `w` have length `l`, `w = 1` in `S`, and area
`A`. Then `w` is freely equal to a product `prod_(i=1..A) u_i r_i^(e_i) u_i^(-1)`
with `r_i in R`, `e_i = +-1` and `|u_i| <= l + rho A`. This is van Kampen's lemma
(Lyndon–Schupp, *Combinatorial Group Theory*, Ch. V §1; not re-read) with the
length count made explicit. Take a van Kampen diagram with `A` faces. If it has a
spur or a cut vertex, freely reduce `w` or split `w` at the cut vertex into
boundary words of subdiagrams; the conjugators produced are prefixes of `w`.
Otherwise some face `F` shares an arc with the boundary: `w = u x v`, where the
boundary label of `F` is `x y`, a cyclic permutation of some `r^(+-1)`, so
`x y = s r^(+-1) s^(-1)` with `|s| <= rho`. Removing `F` leaves a diagram with
`A - 1` faces and boundary word `u y^(-1) v`, of length at most `l + rho`, and
`w = (u s) r^(+-1) (u s)^(-1) · (u y^(-1) v)` freely. Inducting, the `j`-th
conjugator is a prefix of a boundary word of length at most `l + (j-1) rho`,
followed by some `s`, so `|u_j| <= l + j rho <= l + rho A`.

**Step 2: the algorithm.** On input `w` of length `l`, compute
`B = K f(Kl) + Kl`, in time at most `C_0 f(Kl)^2 + O(l log B)`. For
`A = 0, 1, ..., B` list every sequence `(u_i, r_i, e_i)_(i <= A)` with
`|u_i| <= l + rho B`. Freely reduce the product and compare it with the free
reduction of `w`. Answer "trivial" iff some sequence matches.

**Correctness.** A match exhibits `w` in the normal closure of `R`. Conversely, if
`w = 1` in `S` then `Area(w) <= delta_S(l) <= B`, and Step 1 supplies a matching
sequence of length `A <= B`.

**Time.** There are at most `(B + 1)(2|R| (2|X| + 1)^(l + rho B))^B <=
2^(c (l + B)^2)` sequences, for `c` depending on `|X|`, `|R|`, `rho`. Each product
has length at most `B (2(l + rho B) + rho)` and is freely reduced in linear time,
so the total is at most `2^(c' (l + B)^2)`. Since `f(n) >= n`,
`l + B <= (2K + 1) f(Kl)`, so the total is at most `2^(c'(2K+1)^2 f(Kl)^2)`. With
`C = max(K, c'(2K+1)^2, C_0 + c')` and `f` non-decreasing, this is at most
`2^(C (f(Cl) + l)^2) + C`. `∎`
