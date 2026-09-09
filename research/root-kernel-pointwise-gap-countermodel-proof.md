---
rg: 2
id: root-kernel-pointwise-gap-countermodel-proof
kind: route
title: Truncate the Jacobson normal form to a square window and shear one summand by left multiplication
target: root-kernel-invariance-is-not-pointwise-obtainable
requires: []
artifacts:
  - research/artifacts/root-kernel-uniformity-gap-2026-09-08.md
---

## 1. Normal form

Deleting an adjacent `ts` from a word in `s,t` shortens it; two available
deletions cannot overlap and disjoint deletions commute, so by induction on
length every deletion sequence ends at the same irreducible word, which has all
its `s`'s before all its `t`'s.  Hence the monomials `s^i t^j`, `i,j >= 0`, are
an `F_2`-basis of `J`, with

```text
(s^i t^j)(s^k t^l) = s^(i + max(k-j,0)) t^(l + max(j-k,0)).            (NF)
```

Associativity holds because both bracketings reduce the same concatenation.

## 2. The models

For `N >= 1` put

```text
W_N = span_(F_2) { s^i t^j : 0 <= i,j < N },
```

let `p_N : J -> W_N` keep those coordinates and discard the rest, and set
`B_N(b) v = p_N(bv)` for `v in W_N`, which is additive in `b` and linear in
`v`.  No multiplicativity of `B_N` is claimed.

On the finite set `Omega_N = W_N (+) W_N` define

```text
x_N(a)(v,w) = (v, w + p_N(a)),        y_N(a)(v,w) = (v + p_N(a), w),
u_N(b)(v,w) = (v + B_N(b) w, w),      c_N(v,w)    = (w, v),
```

all involutions because the characteristic is two, and let
`X_N(a), Y_N(a), U_N(b), C_N` be the permutation unitaries on
`H_N = l^2(Omega_N)`, with `U_f delta_omega = delta_(f(omega))` so that
products are compositions.  Then `dim H_N = 2^(2N^2)`.

## 3. Claims 1, 2, 4

Additivity in `a` of `x_N(a)` and `y_N(a)` and in `b` of `u_N(b)` is immediate
from additivity of `p_N` and `B_N`, giving claim 1.  Conjugating `x_N(a)` by
the coordinate swap `c_N` adds `p_N(a)` to the first coordinate instead of the
second, which is `y_N(a)`, giving claim 2 exactly.

For claim 4, `B_N(1) v = p_N(v) = v`, so on `W_N (+) W_N` the maps `c_N` and
`u_N(1)` are the scalar `2 x 2` matrices `[[0,1],[1,0]]` and `[[1,1],[0,1]]`
over `F_2`.  The first squares to the identity, and

```text
M = [[0,1],[1,0]] [[1,1],[0,1]] = [[0,1],[1,1]],
M^2 = [[1,1],[1,0]],      M^3 = [[1,0],[0,1]],
```

which is `(C_N U_N(1))^3 = 1`.

## 4. Claim 3: the commutator

Apply `x_N(a), u_N(b), x_N(a), u_N(b)` in turn to `(v,w)`:

```text
(v, w + p_N(a))
(v + B_N(b)(w + p_N(a)), w + p_N(a))
(v + B_N(b)(w + p_N(a)), w)
(v + B_N(b)(w + p_N(a)) + B_N(b) w, w) = (v + B_N(b) p_N(a), w),
```

using additivity of `B_N(b)` and characteristic two.  So

```text
[U_N(b), X_N(a)] = translation of the first coordinate by B_N(b) p_N(a).  (C)
```

`Y_N(ba)` is translation of the first coordinate by `p_N(ba)`.  If `a in W_N`
then `p_N(a) = a` and `B_N(b) a = p_N(ba)`, so the two agree for **every** `b`.
Every fixed `a` lies in `W_N` for all large `N`, which is claim 3 with a
threshold depending only on `a`.

## 5. Claim 5: separation

A nonidentity involution of a finite set has a `2`-cycle `{omega, omega'}`;
the vector `delta_omega - delta_(omega')` is an eigenvector of its permutation
unitary with eigenvalue `-1`, so the unitary is at distance exactly `2` from
`1`.  For `a != 0`, `p_N(a) != 0` for all large `N`, so `x_N(a)` and `y_N(a)`
are nonidentity involutions and `|| X_N(a) - 1 || = || Y_N(a) - 1 || = 2`.

For the mark, `q = 1 + st` and `(NF)` gives `st = s^1 t^1`, so
`q = s^0 t^0 + s^1 t^1`.  For `N = 1` the truncation keeps the `s^0 t^0` term,
and for `N >= 2` it keeps both, so `p_N(q) != 0` for every `N >= 1` and
`|| X_N(q) - 1 || = 2` throughout.

## 6. The failure, `(PG1)`

Take `a_N = s^N`.  Its exponent `i = N` is not `< N`, so

```text
p_N(a_N) = 0,        hence  X_N(a_N) = 1,
```

and by `(C)`, `[U_N(t), X_N(a_N)] = ` translation by `B_N(t) p_N(a_N) = 0`,
i.e. the identity.  Meanwhile `(NF)` gives

```text
t a_N = (s^0 t^1)(s^N t^0) = s^(max(N-1,0)) t^(max(1-N,0)) = s^(N-1)
```

for `N >= 1`, whose exponents `(N-1, 0)` are both `< N`, so
`p_N(t a_N) = s^(N-1) != 0` and `Y_N(t a_N)` is a nonidentity involution.  By
step 5 its distance from `1` is `2`, which is `(PG1)`.

So `a_N in ker X_N` while `t a_N not in ker Y_N`, and the two kernels are
identified by claim 2; the invariance step 4 of
`uniform-root-kernel-invariance-proof` fails, at distance `2`, for every `N`.

## 7. What is not claimed

`(C)` prescribes nothing at the root positions into a third coordinate, and no
Steinberg relation beyond those in claims 2, 3 and 4 is checked.  These are
models for the listed relations, not approximate representations of an
elementary group.
