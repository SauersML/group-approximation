---
rg: 2
id: jacobson-el3-is-not-lef-proof
kind: route
title: The Levi compressor g = diag(u,1) maps A = <x_13(1), x_13(s), x_31(1), x_31(t), c, d> into itself by relations C1-C6, a finite image makes that onto, and e = diag(1,1+sq,1), which centralizes A, then kills [e, g^{-1} x_13(1) g] = x_23(-sq)
target: jacobson-el3-is-not-lef
requires: []
artifacts:
  - experiments/jacobson-el3-bs-trap-2026-09-17/verify_trap.py
  - experiments/jacobson-el3-bs-trap-2026-09-17/verify_trap_signed.py
---

Notation is as in the target. Everything is proved here by hand; the two
artifacts re-check every matrix identity exactly and both exit 0.
* `verify_trap.py` checks the identities over `J = F_2<S,T|TS=1>` in the
  normal form `S^i T^j` (34 checks).
* `verify_trap_signed.py` checks the signed identities over
  `J_Z = Z<S,T|TS=1>` (30 checks).

The only external input is the definition of LEF. Steps 1-5 prove the
theorem; Step 6 proves the centralizer remark; Step 7 derives the
consequences, citing existing ESTABLISHED nodes.

## Step 0. The universal ring

`J_Z = Z<S,T | TS = 1>` has `Z`-basis `S^i T^j` (`i, j >= 0`), because
`TS -> 1` is a rewriting system with no overlaps. Put `Q = 1 - ST`. Then
`QS = S - STS = 0`, `TQ = T - TST = 0`, `Q^2 = Q`, and `SQ = S - S^2 T != 0`.

For a ring `R` with `ts = 1`, `S -> s`, `T -> t` defines a ring map
`J_Z -> R` sending `Q` to `q = 1 - st`, and hence a group map
`EL_3(J_Z) -> EL_3(R)` sending each elementary letter `x_ij(r)` to
`x_ij(image of r)`. So each identity between words in elementary matrices
that holds over `J_Z` holds over `R`. The only facts about `R` used below are
`qs = 0` and `tq = 0`, and, for nontriviality, `sq != 0`.

**Nontriviality.** If `st != 1` then `q != 0`, and `t (sq) = q`, so `sq != 0`.

## Step 1. The elements as elementary words

Write `[x,y] = x y x^{-1} y^{-1}`. For a 2-by-2 block on indices `(i,j)`,
`x(r) = x_ij(r)` and `y(r) = x_ji(r)`.

* **The compressor word.** Over any ring with `ts = 1`,
  `x(s) y(-t) x(s) = [[q, s],[-t, 0]]` and `x(-1) y(1) x(-1) = [[0,-1],[1,0]]`.
  Their product is `[[s, -q],[0, t]]`. On indices `(1,2)` this gives `g`, and
  on indices `(1,3)` it gives `U = a2 a4^{-1} a2 a1^{-1} a3 a1^{-1}`.
  The inverse is `[[t, 0],[-q, s]]`: the product of the two is
  `[[st + q, -qs],[-tq, ts]] = 1`, and in the other order it is
  `[[ts, -tq],[-qs, qq + st]] = 1`, using `q^2 = q`.
* **The correctors.** `x_12(s) x_21(q) = [[1+sq, s],[q, 1]]`. Multiplying on
  the right by `x_12(-s)` gives `[[1+sq, -sqs],[q, 1-qs]] = [[1+sq, 0],[q, 1]]`,
  and then by `x_21(-q)` gives `diag(1+sq, 1)`. So
  `c = [x_12(s), x_21(q)] = diag(1+sq,1,1)`. In the same way
  `[x_12(q), x_21(t)] = diag(1+qt, 1, 1)`, which is `d^{-1}`, and
  `[x_21(s), x_12(q)] = diag(1, 1+sq, 1) = e`.
* **Units.** `(1+sq)(1-sq) = 1 - s(qs)q = 1` and
  `(1-qt)(1+qt) = 1 - q(tq)t = 1`, on both sides.

All of these are also checked by the artifacts.

## Step 2. How g acts on the (1,3) block

Let `B13 <= GL_3(R)` be the group of matrices `M` with `M_{22} = 1` and
`M_{2j} = M_{j2} = 0` for `j != 2`. Identify `B13` with `GL_2(R)` on indices
`(1,3)`. The generators `a1, a2, a3, a4, c, d` and `U` all lie in `B13`,
so `A <= B13`.

Here `g` has rows `(s,-q,0), (0,t,0), (0,0,1)` and `g^{-1}` has rows
`(t,0,0), (-q,s,0), (0,0,1)`. For `M` in `B13`, a direct entry computation
using `qs = 0`, `tq = 0` and `q^2 = q` gives `g M g^{-1}` in `B13`, with block

`Psi(M) = D M D* + (1 - D D*)`, where `D = diag(s,1)` and `D* = diag(t,1)`.

For example:
* the `(1,1)` entry is `s m11 t + (-q)(1)(-q) = s m11 t + q`;
* the `(1,2)` entry is `(-q)(1)(s) = 0`;
* the `(2,1)` entry is `t(1)(-q) = 0`.

Since `D* D = 1`, `Psi` is an injective group homomorphism of `GL_2(R)`,
with left inverse `N -> D* N D`. It is not onto when `st != 1`. The
`(1,3)` entry of `Psi(M)` lies in `sR`, and `1` is not in `sR`: if
`1 = s r`, then `t = ts r = r`, so `st = 1`. On generators this gives:
* `Psi(x_13(r)) = x_13(s r)` and `Psi(x_31(r)) = x_31(r t)`;
* `Psi(diag(alpha, 1)) = diag(s alpha t + q, 1)`.

## Step 3. Relations C1-C6 and Z1-Z6

All computations are in the block `B13 = GL_2(R)`, indices `(1,3)`. For any
column `v` and row `w`, `U (1 + v w) U^{-1} = 1 + (Uv)(w U^{-1})`.
Here `U = [[s,-q],[0,t]]` and `U^{-1} = [[t,0],[-q,s]]`. The first column
of `U` is `(s,0)^T`, its second column is `(-q,t)^T`, the first row of
`U^{-1}` is `(t,0)` and its second row is `(-q,s)`.

* **(C1)** `Psi(x_13(1)) = x_13(s) = a2`.
* **(C3)** `Psi(x_31(1)) = x_31(t) = a4`.
* **(C2)** `Psi(a2) = x_13(s^2)`. On the other side,
  `U a1 U^{-1} = 1 + (s,0)^T (-q, s) = [[1 - sq, s^2],[0, 1]]`, and
  `c U a1 U^{-1} = [[(1+sq)(1-sq), (1+sq) s^2],[0,1]] = [[1, s^2],[0,1]]`,
  because `(1+sq)(1-sq) = 1` and `sq s^2 = s(qs)s = 0`.
* **(C4)** `Psi(a4) = x_31(t^2)`. On the other side,
  `U a3 U^{-1} = 1 + (-q,t)^T (t, 0) = [[1 - qt, 0],[t^2, 1]]`, and
  `U a3 U^{-1} d^{-1} = [[(1-qt)(1+qt), 0],[t^2 (1+qt), 1]] = [[1,0],[t^2,1]]`,
  because `t^2 qt = t(tq)t = 0`.
* **(C5)** `Psi(c) = diag(s(1+sq)t + q, 1) = diag(1 + s^2 q t, 1)`, using
  `st + q = 1`. On the other side,
  `U c U^{-1} = 1 + (s,0)^T (sq) (t,0) = diag(1 + s^2 q t, 1)`.
* **(C6)** `Psi(d) = diag(s(1-qt)t + q, 1) = diag(1 - sq t^2, 1)`, and
  `U d U^{-1} = 1 + (s,0)^T (-qt)(t,0) = diag(1 - sq t^2, 1)`.

Every right-hand side is a word in `a1, a2, a3, a4, c, d` and their inverses,
because `U` is (Step 1). So `g A g^{-1} <= A`.

* **(Z1-Z6)** `e = diag(1, 1+sq, 1)` commutes with every element of `B13`,
  because an element of `B13` fixes the second basis vector and preserves
  the span of the first and third, while `e` acts by a scalar on each of
  these two summands. So `e` centralizes `A`.

## Step 4. The witness

`g^{-1} a1 g = 1 + (g^{-1} e_1)(e_3^T g)`. The first column of `g^{-1}` is
`(t, -q, 0)^T` and the third row of `g` is `(0,0,1)`, so
`y := g^{-1} a1 g = 1 + t E_13 - q E_23 = x_13(t) x_23(-q)`.

Put `N = t E_13 - q E_23`, so `y = 1 + N`, `y^{-1} = 1 - N` and `N^2 = 0`.
Then `e N e^{-1} = t E_13 - (1+sq) q E_23 = t E_13 - (q + sq) E_23`, using
`sq q = s q^2 = sq`. So

`[e, y] = (1 + e N e^{-1})(1 - N) = 1 + (e N e^{-1} - N) = 1 - sq E_23 = x_23(-sq)`,

since every product of two matrices supported in column 3 and rows 1,2 is 0.
By Step 0, this is `!= 1` when `st != 1`.

## Step 5. Every finite image kills w; hence not LEF

Let `Gamma_3 = <g, e, a1, a2, a3, a4, c, d | C1-C6, Z1-Z6>`, where `U` in
(C2), (C4), (C5) and (C6) stands for the word `a2 a4^{-1} a2 a1^{-1} a3 a1^{-1}`,
and let `w = [e, g^{-1} a1 g]`. By Steps 1-4 the assignment of the
certificate defines a homomorphism `Phi : Gamma_3 -> EL_3(R)` with
`Phi(w) = x_23(-sq)`.

**(a) Finite images.** Let `phi : Gamma_3 -> K` be a homomorphism to a finite
group, and let `A_K = phi(<a1, a2, a3, a4, c, d>)`. By (C1)-(C6), conjugation
by `phi(g)` maps each generator of `A_K` into `A_K`, so
`phi(g) A_K phi(g)^{-1} <= A_K`. Conjugation is injective and `A_K` is
finite, so equality holds, and `phi(g)^{-1} A_K phi(g) = A_K`. In particular
`phi(g^{-1} a1 g)` is in `A_K`. By (Z1-Z6), `phi(e)` centralizes `A_K`.
So `phi(w) = 1`.

**(a') Linear images.** Let `phi : Gamma_3 -> GL_n(k)`, for a field `k`,
and let `H` be the Zariski closure of `phi(<a1,...,d>)`. Conjugation by
`phi(g)` is an automorphism of the variety `GL_n(k)`, so it maps `H` onto
the closed subgroup `phi(g) H phi(g)^{-1}`, which is contained in `H` by
(C1)-(C6). The two closed subgroups have the same dimension and the same
number of irreducible components, so they are equal. The centralizer of
`phi(e)` is closed and contains `phi(<a1,...,d>)`, so it contains `H`.
As in (a), `phi(w) = 1`.

**(b) Not LEF.** Recall that `G` is LEF if for every finite `F <= G` (as a
set) there are a finite group `K` and an injective map `iota : F -> K` with
`iota(xy) = iota(x) iota(y)` whenever `x, y, xy` are all in `F`.

Suppose `st != 1` and `EL_3(R)` is LEF. Let `F` be the set of
`Phi`-images of all prefixes of the 12 relators, of `w`, and of the words
`x x^{-1}`, for `x` a generator or an inverse of one. Take `iota` as in
the definition. Then `iota(1) = iota(1) iota(1)`, so `iota(1) = 1`, and
`iota(Phi(x^{-1})) = iota(Phi(x))^{-1}`.

Define `psi` on the free group by sending each generator `x` to
`iota(Phi(x))`. By induction on the length of a prefix `p`,
`psi(p) = iota(Phi(p))`. So each relator `r` has `psi(r) = iota(1) = 1`,
and `psi` factors through a homomorphism `Gamma_3 -> K`. It sends `w` to
`iota(Phi(w))`, which is not `iota(1) = 1`, because `iota` is injective and
`Phi(w) != 1`. This contradicts (a).

**(c) Not residually finite.** `w != 1` in `Gamma_3`, since `Phi(w) != 1`,
but every finite quotient kills `w`.

The inclusion `Phi(g A g^{-1}) < Phi(A)` is proper in `EL_3(R)`:
* `Phi(A) <= B13`;
* `Phi(g^{-1} a1 g)` has `(2,3)` entry `-q != 0`, so it is not in `B13`.

So the trap is a genuine contraction and not an automorphism.

## Step 6. The centralizer of g over J (the remark only)

Here `R = J = F_2<S,T|TS=1>`, acting on `V_+ = F_2^(N)` by
`S e_n = e_{n+1}`, `T e_n = e_{n-1}` and `T e_0 = 0`. This action is
faithful. Indeed `S^i T^j e_n = e_{n-j+i}` for `n >= j`, and `0` for `n < j`.
Given a nonzero combination, pick its least `j`, and evaluate at `e_j`: this
isolates the terms with that `j`, whose values `e_i` are distinct.

**Claim.** `C_{GL_3(J)}(g) = { diag(u^k, d') : k in Z, d' in J^x }`.

Write `X` in the centralizer in `(2+1)`-block form `[[X11, X12],[X21, x33]]`.
Then `u X11 = X11 u`, `u X12 = X12` and `X21 u = X21`.

**The off-diagonal blocks vanish.**
* Write `X12 = (x, y)^T`. Then `u X12 = (Sx + Qy, Ty)`.
  We argue with operators on `V_+`, using faithfulness.
  - `Ty = y` gives `y = T^n y` for all `n`. For each `v`, `yv` is finitely
    supported, so `T^n y v = 0` for large `n`. Hence `y v = 0`, and `y = 0`.
  - Then `Sx = x`, so `x v = S^n x v` for all `n`. If `xv != 0`, the least
    index in the support of `S^n x v` tends to infinity, which is impossible.
    So `x = 0`.
* Write `X21 = (a, b)`. Then `X21 u = (aS, aQ + bT)`.
  - `aS = a` gives `a e_m = a S^n e_m = a e_{m+n}` for all `n`. For
    `a = sum c_ij S^i T^j` and `k >= max j`, the vector `a e_k` is supported
    in indices `>= k - max j`. So `a e_m = 0` for every `m`, and `a = 0`.
  - Then `bT = b`, so `b e_m = b T^{m+1} e_m = 0` for every `m`, and `b = 0`.

**The diagonal block is a power of u.** Identify `V_+^2` with `F_2^(Z)`
by sending `(e_n, 0) -> f_{n+1}` and `(0, e_m) -> f_{-m}`. Using
`Q e_0 = e_0` and `Q e_m = 0` for `m >= 1`, the element `u` becomes the
bilateral shift `f_k -> f_{k+1}`. This makes `F_2^(Z)` a free module of
rank one over `F_2[z^(+-1)]`, with `z` acting as `u`.
* A linear map commuting with the shift is determined by its value `p` on
  `f_0`, so it is multiplication by `p`, a Laurent polynomial.
* `X11` is invertible, since `X` is block diagonal, and its inverse also
  commutes with `u`. So `p` is a unit of `F_2[z^(+-1)]`, hence `p = z^k`
  and `X11 = u^k`.

Conversely, every `diag(u^k, d')` commutes with `g`. This remark is not
used in Steps 1-5.

## Step 7. Consequences

1. **Not LEA (`R = J`).** `jacobson-elementary-groups-are-lea-only-if-lef`
   (ESTABLISHED) shows that `EL_3(J)` is LEA iff it is LEF. By Step 5 it
   is not LEF, so it is not LEA. The same holds over `F_3`, which that node
   also covers.
2. **No partial mirror lifts at rank three.**
   `jacobson-el3-lef-from-local-mirror-lifts` (L1) says that partial
   iota-lifts on every ball imply LEF. Contrapositively, some finite ball of
   `EL_3(J)` has none. The set `F` of Step 5(b) is such a ball.
3. **Rank threshold.** `binary-jacobson-el2-is-lef` (ESTABLISHED) gives
   `EL_2(J)` LEF. `cohn-elementary-group-is-not-lef` gives `n >= 4` not
   LEF, and so does Step 5 applied to `EL_3 <= EL_n` as the upper-left
   corner, since LEF passes to subgroups. So `EL_n(J)` is LEF iff `n <= 2`.
4. **Not in a proper parabolic.** By
   `jacobson-rank-three-parabolics-are-lef`, every proper parabolic of
   `EL_3(J)` is LEF. So `Phi(Gamma_3)` lies in no proper parabolic, which
   is consistent with its generators using all four roots `(1,2)`, `(2,1)`,
   `(1,3)` and `(3,1)`.
