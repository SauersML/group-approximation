---
rg: 2
id: kms-hc1-cartan-relator-is-tautological-mod-symmetry
kind: claim
title: The first-deviation kernel of Gamma^A2_p -> I_1 is fixed by the diagonal torus and is an S_3-module, so centralizer pairings vanish on the torus, the Cartan relator R_n has class exactly C_nA with no pairing terms, and V_n is one of four submodules of W_n; one generic relation per level suffices
distinct_from:
  kms-hc1-p-power-value-vanishes-on-affine-root-groups: that claim kills the p-power value Pi on torsion root elements and proposes the Cartan relator R_n with centralizer-pairing corrections as the next route. This claim proves that the pairings vanish on the torus, that R_n carries exactly C_nA and nothing else, and it cuts the unknown V_n down to four S_3-submodules.
  kms-hc1-root-p-powers-die-first-deviation-at-3np: that claim locates the first deviation in W_n = span(K_n, C_nA, C_nB). This claim adds the symmetry structure of W_n and of the kernel.
artifacts:
  - experiments/kms-hc1-cartan-relator-selection-2026-09-19/symmetry_check.py
  - experiments/kms-hc1-cartan-relator-selection-2026-09-19/symmetry_p5.out
  - experiments/kms-hc1-cartan-relator-selection-2026-09-19/symmetry_p7.out
  - experiments/kms-hc1-cartan-relator-selection-2026-09-19/symmetry_p11.out
  - experiments/kms-hc1-cartan-relator-selection-2026-09-19/symmetry_p13.out
  - experiments/kms-hc1-cartan-relator-selection-2026-09-19/pqchunk.sh
  - experiments/kms-hc1-cartan-relator-selection-2026-09-19/pq_p11_tower.out
---

Notation of `kms-hc1-p-power-value-vanishes-on-affine-root-groups` (below:
the root-group claim) and `kms-hc1-root-p-powers-die-first-deviation-at-3np`
(below: (FD)). Fix a prime `p >= 5`.

- `G = Gamma^` is the pro-p completion of `Gamma^A2_p`, and
  `K = ker(phi^ : G -> I_1)`.
- `D_d` is the Zassenhaus filtration. `d0 = 3np` is the first deviation
  degree, assumed finite.
- `Kd0 = W_n / V_n` is the kernel of `gr_(d0) G -> (L_p)_(d0)`, where
  `W_n = span(K_n, C_nA, C_nB)` lies in `U_(3np)`.
- `h(z) = diag(z, z^-1, 1)`, and `y_N = x21(t^N)`.

**Symmetries.** The group `H = (F_p^*)^3 x| S_3` acts on `Gamma^A2_p` by
the following automorphisms:
- the power maps `sigma_(al,be,ga)`: `a -> a^al`, `b -> b^be`,
  `c -> c^ga`;
- the rotation `rho`: `a -> c`, `b -> a`, `c -> b`;
- the flip `theta`: `a -> b`, `b -> a`, `c -> c^-1`.

Each of these is compatible with `phi` via an automorphism of `I_1`:
- `Ad(diag d)` composed with `t -> mu t`, where `mu = al be ga`;
- `Ad(pi)`, with `pi = [[0,1,0],[0,0,1],[t,0,0]]`;
- `X -> J X^-T J^-1`, with `J = antidiag(1,-1,1)`.

So `H` acts on `G`, `K`, `D_d`, `U`, `W_n`, `V_n` and `Kd0`, compatibly.

## Statement

> **(S) Selection rule.** The power map `sigma_(al,be,ga)` acts on `W_n`,
> and so on `Kd0`, as the scalar `(al be ga)^n`. So the subtorus
> `al be ga = 1` fixes `Kd0` pointwise. Let `v` be a power of one of the
> six vertex elements `a, b, c, [a,b], [b,c], [c,a]`. Let `c` be in the
> diagonal torus of `I_1` with `c` commuting with `phi(v)`. Then
> `delta_v(c) = [ct, v] mod D_(d0+1) = 0`. In particular `delta_a` vanishes
> on all of `diag(u, u, u^-2)`, `u` in `1 + tO`, at every level.

> **(T) The Cartan relator is tautological.** Let `g` be any lift of
> `h(1+t^n)`. Then `g^p mod D_(d0+1)` depends only on `h(1+t^n)`, not on
> the lift. So the lifts of the four root elements in the Bruhat word, and
> any centralizer corrections to them, drop out. The Bruhat word of
> `h(1+t^(np))` equals `[yt_(np), a^-1]` modulo `D_(d0+1)`, for any lift
> `yt_(np)` of `y_(np)`. Hence
> `class(R_n) = class(g^p) - [a, yt_(np)] = C_nA`,
> with `(h_A t^(np))~ = [E12, t^(np) E21]`. The centralizer pairings enter
> with coefficient zero. `C_nA` lies in `V_n` iff the single word `R_n`
> lies in `D_(3np+1)(G)`. No identity of `I_1` between root elements and
> torus elements says more than this. Deciding `R_n` needs `Gamma`'s
> relators at class `3np`, which is the tower computation.

> **(H) Four submodules.** As an `S_3`-module,
> `W_n = L_n (+) S_n`, where:
> - `L_n = W_n cap U^Lie` is the Kassel line. It is spanned by `K_n` and
>   carries a character `eps` of `S_3`.
> - `S_n` is isomorphic to the reflection representation of `S_3` on the
>   Cartan `h = {h_A, h_B, h_C}/(sum)`. This representation is irreducible,
>   since `p >= 5`.
>
> So `V_n` is one of `0`, `L_n`, `S_n`, `W_n`, and `Kd0` is one of `W_n`,
> `Std`, `eps`, `0`. Also, `V_n = W_n` iff `V_n` contains one vector with
> nonzero components in both `L_n` and `S_n`. The Cartan part is
> all-or-nothing: `C_nA` is in `V_n + L_n` iff `C_nB` is. At each level,
> the three unknowns `(kappa, alpha_A, alpha_B)` reduce to two bits.

## Proof idea

- **(S).** `phi^([ct, v]) = [c, phi v] = 1`, so `delta_v(c)` is in `Kd0`.
  It is bilinear, so `delta_(v^k) = k delta_v`.
  - `W_n` is multihomogeneous of degree `(np,np,np)`, and
    `(al be ga)^(np) = (al be ga)^n`.
  - Take `sigma` with `al be ga = 1` and character `chi(v) != 1` on `v`.
    This is possible for all six vertex elements; for example, `[a,b]` has
    character `al be = ga^-1`. Then `sigma` acts on `I_1` by conjugation by
    an `F_p`-diagonal matrix, which fixes `c`.
  - Equivariance gives `delta_v(c) = sigma(delta_v(c))`, and this equals
    `delta_(v^chi)(c) = chi delta_v(c)`. So `delta_v(c) = 0`.
- **(T).**
  - Two lifts of `h(1+t^n)` differ by `k` in `K`, which lies in `D_(d0)`.
    By Hall–Petrescu, `(gk)^p = g^p k^p` times commutators in
    `[D_(d0), D_(3n)]`, and all of this lies in `D_(d0+1)`.
  - In the Bruhat word, `x12(-1/(1+t^N)) = x12(-1) x12(t^N - ...)`, and
    `x21(-t^N/(1+t^N)) = y_N^-1 x21(t^(2N) - ...)`. The tails lie in
    `D_(3N+1)`. So the word is `yt^-1 a yt a^-1 = [yt, a^-1]` modulo
    `D_(d0+1)`.
  - `[a, yt]` mod `D_(d0+1)` is lift-independent, because `yt` has degree
    `3np - 1 < d0`.
- **(H).**
  - `h -> (t^n h)~^[p] mod U^Lie` is linear and `S_3`-equivariant. It is
    linear because the p-map is additive on commuting elements, and
    `[t^n h, t^n h']` has degree `6n < d0`.
  - Its image is `W_n / L_n`.
  - `dim L_n <= dim H_2(L_p)_(3np) = 1`. This holds because `U^Lie` is a
    quotient of the free Lie algebra modulo all Lie relations of degree
    `< d0`.
  - Irreducibility of `Std` and Maschke (`p` does not divide 6) give the
    decomposition. `Std` is not isomorphic to a character, so every
    submodule is a sum of isotypic pieces.

## Status

- **Proved, every p >= 5, every level n:** (S), (T), (H). They are
  conditional only on `d0 < infinity` and on (FD), which uses Open 1. The
  full proof is in `kms-hc1-cartan-relator-is-tautological-mod-symmetry-proof`.
- **Checked** (`symmetry_check.py p 12`, `ALL OK` for `p = 5, 7, 11, 13`):
  - the three `I_1` automorphisms and their action on `a, b, c`;
  - the permutation action on `h_A, h_B, h_C`;
  - the Bruhat identity for `N = 1, 2, 3`;
  - the nontrivial characters of the six vertex elements on
    `al be ga = 1`.
- **Obstruction (T):** the centralizer-pairing refinement of Route 2 is
  empty. It reproduces the definition of `C_nA` exactly.
- **Tower, p = 11** (`pqchunk.sh`, `pq_p11_tower.out`): the lower
  exponent-11 central quotients of `Gamma^A2_11` have the same order as
  those of `I_1` for every class `k <= 33` (increments `3,3,2`). The check
  covers the level-1 deviation degree `3p = 33`, so it independently
  confirms `V_1 = W_1` at `p = 11`. The level-2 degree `66` is out of
  reach: the time per class grows about 1.4x (`195` s at class 33, under
  load 25), so it would need far more than the 1200 s cap. The run was
  stopped after class 33.

## Next step

By (H), level `n` needs one relation class in general position, not three.
The level-1 proof found exactly this: the row `(0,0,6)` and its two
rotations. For `n = 2`, the question is whether a single
`(2p,2,2p)`-slice jump of the `b`-degree-2 lift computation (Next rank of
`kms-hc1-witt-carry-syzygy-lifts-by-right-freeness`) has nonzero components
in both `L_2` and `S_2`. The `S_3`-projection of such a jump is computed by
averaging it over the six elements of `S_3`.
