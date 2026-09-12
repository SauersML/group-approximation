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

## 3. Obstructions

**Lemma 3.1 (double-coset tensor form).** Let `F <= G` be a subgroup, `h` in `G`, and `D = F ∩ h F h^(-1)`.
- **The map.** `mu : F_2[F] ⊗_(F_2[D]) F_2[F] -> A`, `x ⊗ y |-> x [h] y`, is well defined and injective.
- **The actions.** `D` acts on the first factor by right multiplication, and on the second factor by
  `d . y = [h^(-1) d h] y`.

*Proof.*
- **Well defined.** `(x[d])[h]y = x[h][h^(-1)dh]y`.
- **Basis.** `D` acts freely on `F x F` by `(f1, f2) . d = (f1 d, h^(-1) d^(-1) h f2)`, so the tensor product has basis
  the orbit set `F x_D F`.
- **Injectivity.** `mu` sends the orbit of `(f1, f2)` to `f1 h f2`. If `f1 h f2 = f1' h f2'`, then
  `d = f1^(-1) f1' = h f2 f2'^(-1) h^(-1)` lies in `D`, and `(f1', f2') = (f1, f2) . d`. So distinct basis vectors go
  to distinct group elements. QED

**Corollary 3.2.** Let `E^` lie in `F_2[F]` with `E^ != 0, 1`.
- `X = E^[h]E1^ = 0` exactly when `E^ ⊗ E1^ = 0` over `F_2[D]`.
- `Y = E1^[h^(-1)]E^ = 0` exactly when `E1^ ⊗ E^ = 0` over `F_2[h^(-1) D h]`.
- If `D = 1`, both tensors are tensors of nonzero vectors over `F_2`, so `X != 0` and `Y != 0`.

**Lemma 3.3 (rigidity).** In Data 2.0, if `b a` is a unit, then `F_2[H']` is not directly finite, where
`H' = <supp E^, h>`. In particular `H'` is not sofic, since group algebras of sofic groups are directly finite
(Elek–Szabó).

*Proof.*
- **Everything lives on `H'`.** `ba = 1 + X + Y` and `T = 1 + X + YX` lie in `F_2[H']`.
- **Inverses stay on `H'`.** If an element of `F_2[H']` is a unit of `A`, its inverse lies in `F_2[H']`, because the
  projection onto `H'`-supported coefficients is an `F_2[H']`-bimodule map.
- **The corner inverse.** `w = E1^ T^(-1) E1^` therefore lies in `F_2[H']` and inverts `C'C` in the corner. Put
  `C'' = w C'`; then `C'' C = E1^`.
- **Not two-sided.** `pi(w) = P_1`, so `pi(C C'') = pi(C) pi(C') = q != P_1` by Remark 2.5.
- **Conclusion.** `(C'' + E^)(C + E^) = 1`, while `(C + E^)(C'' + E^) = CC'' + E^ != 1`. QED

**Remark 3.4 (never both pieces).** Suppose `E^` is supported on a finite subgroup `F`, and `X = Y = 0`.
- `X = 0` gives `E1^ f = f`, and `Y = 0` gives `f E1^ = f`, where `f = [h]E1^[h^(-1)]`.
- `f != E1^`, since `pi(f) = q`, and `f` is supported on `h F h^(-1)`.
- `f` and `E1^` are conjugate, so they have equal normalized ranks. That contradicts
  `nested-two-finite-subgroup-idempotents-have-strict-rank`.

**Computation 3.5 (natural Thompson units, `D = 1`).**
- **The units.** `g1 = S[00]T[0] + S[01]T[10] + S[1]T[11]` and `g2 = S[01]T[1] + S[00]T[00] + S[1]T[01]`
  satisfy Data 2.0.
- **Their quotient.** `h = g1^(-1) g2 = S[10]T[1] + S[0]T[00] + S[11]T[01]`, that is `1w |-> 10w`, `00w |-> 0w`,
  `01w |-> 11w`.
- **The action of `F`.** `F = <u, v>` acts on each `V_x = span{delta_0x, delta_1x}` of the point module by one
  matrix `M_f` in `GL_2(F_2)`, and `f` is determined by `M_f`.
- **Step 1.** Suppose `h f = f' h` with `f, f'` in `F`, and let `y != 0^infinity`. On `delta_00y`,
  - `h f delta_00y = (M_f)_00 delta_0y + (M_f)_10 delta_100y`;
  - `f' h delta_00y = (M_f')_00 delta_0y + (M_f')_10 delta_1y`.

  The points `0y`, `100y` and `1y` are distinct, so both matrices are upper unitriangular.
- **Step 2.** On `delta_10x`, with `x != 0^infinity`,
  - `h f delta_10x = (M_f)_01 delta_0x + delta_100x`;
  - `f' h delta_10x = (M_f')_01 delta_000x + delta_100x`.

  So `M_f = M_f' = 1`, and `D = 1`. By Corollary 3.2, `X != 0` and `Y != 0` for every nontrivial idempotent
  `E^` of `F_2[F]`.

**Proposition 3.6 (swap-group lifts, every `h`).** Let `F = <u, v>`, and let `h` be as in Data 2.0.
1. The idempotents of `F_2[F]` over `P_0` are exactly `xy` and `P0^ = xy + z`.
2. For both of them, `X != 0` and `Y != 0`.

*Proof.*
- **(1).** `z` is central, so `F_2[F] = F_2[F](1+z) (+) F_2[F]z`.
  - The first block is `M_2(F_2)`, spanned by `x, y, xy, yx`, and `pi` is injective on it.
  - The second block is `F_2[C_2]`, which is local with idempotents `0` and `z`, and `pi` kills it.
- **Supports.** `xy = 1+u+v+g`, `1+xy = u+v+g`, `P0^ = u+v+g^2` and `1+P0^ = 1+u+v+g^2`. In each case one of
  `E^` and `E1^` has three elements in its support.
- **`D = 1`.** Corollary 3.2.
- **`D = <f>` of order two.** Let `f' = h^(-1) f h`, and put `S1 = supp E^`, `S2 = supp E1^`.
  - The orbit of `(f1, f2)` has coefficient `[f1 in S1][f2 in S2] + [f1 f in S1][f' f2 in S2]` in `E^ ⊗ E1^`.
  - If all of these vanish, then `S1 f = S1` and `f' S2 = S2`. So both supports have even size, which is a
    contradiction.
  - `Y` is handled the same way.
- **`D = <g>` of order three.** `D` is normal in `F`, so the twist fixes `z`, and the tensor product splits along the
  central idempotents `z` and `1+z` of `F_2[D]`.
  - The `1+z` component is a tensor over the field `F_2[D](1+z) ~= F_4`.
  - There `E^(1+z) ⊗ (1+z)E1^` equals `xy ⊗ yx != 0` for both choices of `E^`. The case of `Y` gives
    `yx ⊗ xy != 0`.
- **`D = F`.** Then `h` normalizes `F`, and `mu(x ⊗ y) = x (h y h^(-1)) [h]`.
  - **`X = 0`.** It gives `h E1^ h^(-1) F_2[F] ⊆ E1^ F_2[F]`. Conjugation preserves dimension, so the two are equal.
    Evaluating, `qR = P_1 R` with `q <= P_1`, so `q = P_1`, against Remark 2.5.
  - **`Y = 0`.** It gives `h^(-1) E^ h F_2[F] = E^ F_2[F]`. But `pi(h)^(-1) P_0 pi(h) = P_0 - pi(h)^(-1)(P_1 - q) pi(h)`
    is strictly below `P_0`. QED

**Remark 3.7 (where the ansatz stands).**
- **Non-sofic support group.** Any two-piece witness needs `<supp E^, h>` to be non-sofic (Lemma 3.3).
- **Swap group excluded.** A triangular witness needs `E^` supported off the swap-group algebra (Proposition 3.6).
  The next finite candidates are idempotent lifts of `P_0` on the depth-two constants `GL_4(F_2)` (Remark 1.3). There
  the parity case of Proposition 3.6 no longer applies automatically.
- **Nilpotent criterion untested.** The criterion of Proposition 2.4, `YX` nilpotent, has not been tested for any `h`.
