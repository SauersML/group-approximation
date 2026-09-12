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
