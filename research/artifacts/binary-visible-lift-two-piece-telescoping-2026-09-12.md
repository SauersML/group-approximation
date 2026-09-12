# Binary visible lifts: swap-group honest lifts and two-piece corner telescoping

Lane `w3-kap-visible`, 2026-09-12. Supports `binary-swap-group-lifts-leavitt-matrix-units-with-kernel-gap`,
`two-piece-s0-lifts-telescope-to-a-corner` and `two-piece-s0-lift-with-triangular-defect-exists`, all bearing on
`left-invertible-lift-of-s0-in-leavitt-group-algebra`.

**Setup.**
- `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, `pi : A ->> R` the evaluation map, `K = ker pi`.
- Monomials `S[alpha]T[beta]` replace the prefix `beta` by `alpha` (the checker convention).
- `P_alpha = S[alpha]T[alpha]` is the cylinder projection, so `P_0 = s0 t0` and `P_1 = s1 t1`.

## 1. Honest lifts in characteristic two

**1.0 Why the characteristic-three device has no binary analogue.** Over `F_3`, `P_p = 2(1 - [1+p])` lifts
an idempotent `p` because `1+p` is an involution. Over `F_2`, `(1+p)^2 = 1+p`, so `1+p` is a unit only when
`p = 0`. The binary device lifts nilpotents instead.

**Lemma 1.1 (nilpotent lifts).** Let `n` in `R` satisfy `n^(2^k) = 0`. Then `u = 1+n` is a unit with
`u^(2^k) = 1`, and `N(n) = [1] + [1+n]` satisfies `N(n)^(2^k) = 0` and `pi(N(n)) = n`.

*Proof.* In the commutative algebra `F_2[<u>]` the Frobenius gives
`([1]+[u])^(2^k) = [1] + [u^(2^k)] = 0`, and `pi([1]+[u]) = 1 + u = n`. QED

**1.2 The swap group.**
- Put `u = 1 + s0 t1` and `v = 1 + s1 t0`, the standard involutions.
- `uv = 1 + s0t1 + s1t0 + s0t0` is not `1` and has order three. So `F = <u, v>` is isomorphic to `S_3`; it is
  `GL_2(F_2)` on the depth-one matrix units `E_ij = s_i t_j`.
- Write `g = uv`, `g^2 = vu` and `w = uvu = vuv`.
- Put `x = [1] + [u]` and `y = [1] + [v]` in `A`.

**Proposition 1.2.**
1. `x^2 = y^2 = 0`.
2. `(xy)^2 = xy`, `(yx)^2 = yx`, and `(xy)(yx) = (yx)(xy) = 0`.
3. `pi(x) = s0 t1`, `pi(y) = s1 t0`, `pi(xy) = s0 t0`, `pi(yx) = s1 t1`.
4. `xy + yx = 1 + z`, where `z = [1] + [uv] + [vu]` is the kernel idempotent of
   `leavitt-evaluation-kernel-hits-augmentation-one`.
5. `P0^ = [u] + [v] + [vu]` and `P1^ = [1] + [u] + [v] + [vu]` are orthogonal idempotents with `P0^ + P1^ = 1`,
   `pi(P0^) = s0 t0` and `pi(P1^) = s1 t1`. Also `P0^ = xy + z` and `P1^ = yx`.

*Proof.*
- (1) is Lemma 1.1 with `k = 1`.
- (2): in `F_2[S_3]`, `xy = 1 + u + v + g`.
  - `xyx = (1+u+v+g)(1+u) = v + g + g^2 + w`, using `u^2 = 1`, `vu = g^2`, `uvu = w`.
  - `xyxy = (v+g+g^2+w)(1+v) = 1 + u + v + g`, using `v^2 = 1`, `gv = u`, `g^2 v = w`, `wv = g^2`.
  - So `(xy)^2 = xy`. The case `yx` is symmetric under `u <-> v`. `(xy)(yx) = x y^2 x = 0`.
- (3): `pi(x) = 1 + u = s0t1` and `pi(y) = s1t0`. Then `s0t1 s1t0 = s0t0` and `s1t0 s0t1 = s1t1`, since `t1 s1 = t0 s0 = 1`.
- (4): `xy + yx = (1+u+v+g) + (1+u+v+g^2) = g + g^2 = 1 + z`.
  - `z^2 = z` by the Frobenius in `F_2[<g>]`, since `3 = 1` in `F_2`.
  - `pi(z) = 0` by the cited node.
- (5):
  - From `xy = (xy)^2 + (xy)(yx) = xy(1+z)` we get `xy z = 0`; symmetrically `z xy = 0`, and the same for `yx`.
  - So `xy`, `yx` and `z` are pairwise orthogonal idempotents with sum `1`.
  - `xy + z = (1+u+v+g) + (1+g+g^2) = u + v + g^2`. A direct check also gives `(u+v+g^2)^2 = u+v+g^2`.
  - `pi(u + v + vu) = s0t0`: the three units contribute `1+s0t1`, `1+s1t0` and `1+s0t1+s1t0+s1t1`, which sum
    to `1 + s1t1`. QED

**Reading.**
- `x, y, xy, yx` are the matrix units of the `M_2(F_2)` block of `F_2[S_3]`, and `1+z` is its unit.
- `pi` kills the complementary block `F_2[S_3] z`.
- The exact lifted partition `P0^ + P1^ = 1` puts that missing kernel mass into `P0^`.
- Compare `anti-central-ternary-summand-contains-its-matrix-ring`: over `F_3` the depth-one matrix copy has
  unit `eps_-`. Over `F_2` it has unit `1 + z`.

**Remark 1.3 (depth `k`, not used below).** Put `n = 2^k`. The evaluation restricted to `F_2[GL_n(F_2)]` is the
natural representation onto `M_n(F_2)`, and it factors through `F_2[GL_n(F_2)]/rad`. Systems of matrix units lift
modulo nilpotent ideals, so every depth-`k` matrix-unit system lifts into `F_2[GL_n(F_2)]`. Depth one is special
only because its block splits off: the natural module is projective only for `n = 2`, since projective
`F_2[GL_n(F_2)]`-modules have dimension divisible by `2^(n(n-1)/2)`.

## 2. Two-piece lifts and corner telescoping

**Data 2.0.**
- `E^` is an idempotent of `A` with `pi(E^) = P_0`, and `E1^ = 1 - E^`. Example: `P0^` of Proposition 1.2.
- `g1, g2` in `G` satisfy `g1 s0 = s0 s0`, `g1 P_0 g1^(-1) = P_00`, `g2 s1 = s0 s1` and `g2 P_1 g2^(-1) = P_01`.
- `h = g1^(-1) g2`.
- `a = [g1] E^ + [g2] E1^` and `b = E^ [g1^(-1)] + E1^ [g2^(-1)]`.

**Lemma 2.1.** `pi(a) = s0` and `pi(b) = t0`. Also `b a = 1 + X + Y`, where `X = E^ [h] E1^` and
`Y = E1^ [h^(-1)] E^`, and both `X` and `Y` lie in `K`.

*Proof.*
- `pi(a) = g1 s0 t0 + g2 s1 t1 = s00 t0 + s01 t1 = s0`.
- `P_0 g1^(-1) = g1^(-1) P_00 = g1^(-1) s00 t00 = s0 t00`, since `g1^(-1) s00 = s0`. Likewise `P_1 g2^(-1) = s1 t01`,
  so `pi(b) = s0 t00 + s1 t01 = t0`.
- Expanding `b a` with `E^ E^ = E^`, `E1^ E1^ = E1^` and `g1^(-1) g1 = 1` gives `E^ + E1^ + X + Y`.
- `pi(X) = P_0 g1^(-1) g2 P_1 = g1^(-1) P_00 P_01 g2 = 0`. Similarly `pi(Y) = g2^(-1) P_01 P_00 g1 = 0`. QED

**Theorem 2.2 (corner telescoping).** Put `C = E1^ [h] E1^` and `C' = E1^ [h^(-1)] E1^`. Then
`YX = E1^ + C'C`, and the following are equivalent:
1. `b a` is a unit of `A`;
2. `C'C` is a unit of the corner ring `E1^ A E1^`.

When they hold, `c = (ba)^(-1) b` satisfies `c a = 1`, `pi(c) = t0` and `pi(a c) = s0 t0 != 1`. So `a` witnesses
`left-invertible-lift-of-s0-in-leavitt-group-algebra`.

*Proof.*
- **The identity.** `YX = E1^ [h^(-1)] (1 - E1^) [h] E1^ = E1^ - C'C`, which is `E1^ + C'C` in characteristic two.
- **Factorization.** `X^2 = Y^2 = 0` because `E^ E1^ = 0`. Then `(1 + Y)(1 + X + YX) = 1 + X + Y`, and `1 + Y`
  is its own inverse.
- **Peirce blocks.** `T = 1 + X + YX = E^ + X + d`, where `d = E1^ + YX = C'C`. In Peirce form,
  `T = [[E^, X], [0, d]]`.
- **(2) implies (1).** Let `w` be the inverse of `d` in `E1^ A E1^`. Then `S = E^ + Xw + w` satisfies
  `TS = ST = 1`. This uses `X p = d p = 0` for `p` in `E^ A E1^`, and `X w d = X`.
- **(1) implies (2).** Let `S = [[p, q], [r, s]]` be an inverse of `T`.
  - `ST = [[p, pX + qd], [r, rX + sd]] = 1` gives `r = 0` and `sd = E1^`.
  - `TS = [[p + Xr, q + Xs], [dr, ds]] = 1` gives `ds = E1^`.
  - So `s` inverts `d` in the corner.
- **The witness.** `pi(ba) = t0 s0 = 1`, so `pi(c) = t0` and `pi(ac) = s0 t0`. QED

**Corollary 2.3 (triangular defect).** If `X = 0` or `Y = 0`, then `b a = 1 + N` with `N^2 = 0`, so `b a` is a unit
and Theorem 2.2 produces a witness. Moreover:
- `X = 0` exactly when `[h] E1^ A` is contained in `E1^ A`, because `X = (1 - E1^)[h]E1^`;
- `Y = 0` exactly when `[h^(-1)] E^ A` is contained in `E^ A`.

**Proposition 2.4 (nilpotent defect).** `b a - 1 = X + Y` is nilpotent if and only if `YX` is nilpotent, that is,
if and only if `E1^ + C'C` is nilpotent in `E1^ A E1^`.

*Proof.*
- `(X + Y)^2 = XY + YX`. The two summands lie in the orthogonal corners `E^ A E^` and `E1^ A E1^`, so
  `(X + Y)^(2k) = (XY)^k + (YX)^k`.
- `(YX)^(k+1) = Y (XY)^k X` and `(XY)^(k+1) = X (YX)^k Y`, so either product is nilpotent exactly when the other is.
  QED

**Remark 2.5 (the ansatz telescopes visible to visible).**
- **The corner isometry.** Since `pi(X) = 0`, `pi(h) P_1 = P_1 pi(h) P_1`. So `pi(C) = pi(h) P_1` maps `P_1` onto
  `q = g1^(-1) P_01 g1`, and `pi(C') = P_1 pi(h^(-1))` is a left inverse of `pi(C)` in `P_1 R P_1`.
- **The range is proper.** `g1^(-1) P_00 g1 = P_0`, and `q` is orthogonal to it. So `g1^(-1) P_0 g1 = P_0 + q`, and
  `q = P_1 - g1^(-1) P_1 g1` is strictly smaller than `P_1`.
- **Same problem in a corner.** Transport along `R ~= P_1 R P_1`, `r |-> s1 r t1`:
  - `sigma = t1 pi(h) s1` satisfies `sigma' sigma = 1` for `sigma' = t1 pi(h^(-1)) s1`;
  - `sigma sigma' = t1 q s1 != 1`.
  - So `(C, C')` lifts a proper isometry and its left inverse into the corner ring `E1^ A E1^`. Theorem 2.2 asks
    for `C'C` to be a unit there, which is the visible problem again, one corner down.
- **Stopping the recursion.** This is the recursive-corner transport of
  `research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md` Section 6 made explicit. A finite witness
  of this shape must stop the recursion, and Corollary 2.3 is the one-step stop.
