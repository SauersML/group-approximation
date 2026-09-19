---
rg: 2
id: fpbs-quasiconvex-null-lattice-odometer-class-dies-proof
kind: route
title: Proof that a semigroup Neumann lemma supplies F-transverse killing elements in every torsion-free hyperbolic group, and that the resulting symmetric odometer skeleton code is quasiconvex-null, forward injective and hence match-rigid, so its class dies
target: fpbs-quasiconvex-null-lattice-odometer-class-dies
requires:
  - fpbs-transverse-skeleton-ray-codes-are-match-rigid
  - fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups
  - fpbs-quasiconvex-null-small-classes-exist-on-free-boundary
---

# Proof

`Gamma` is torsion-free, nonelementary and `delta`-hyperbolic, with word length `|.|` and ball `B_R` of radius `R`.
For a quasiconvex `K`, `Lambda_K` is its limit set, and `g Lambda_K = Lambda_{g K g^{-1}}`. Inputs (Q1)--(Q4) are as in
`fpbs-transverse-skeleton-ray-codes-are-match-rigid-proof`.

## Step 1. The skeleton `F` and the element `c`

By Kapovich (*A non-quasiconvexity embedding theorem for hyperbolic groups*, Math. Proc. Cambridge Philos. Soc. 127
(1999)), `Gamma` contains a malnormal quasiconvex free subgroup `F_0 = <x, y>` of rank 2. Let `F = <y, yxxyx> <= F_0`.
The script `malnormal_search.py` builds the Stallings core graph of `F` in `F_0`: 4 vertices, 5 edges, rank 2, so
`y, yxxyx` is a free basis. It checks two things:
- `F` is malnormal in `F_0`. By Kapovich--Myasnikov (J. Algebra 248 (2002), Prop. 9.10), this holds because every
  component of the fibre product of the core graph with itself that avoids the diagonal is a tree.
- The `x`-edges of the core graph form no cycle. So no `x^n` with `n ≠ 0` is conjugate in `F_0` into `F`.

**Malnormal in `Gamma`.** Suppose `g ∈ Gamma` and `g F g^{-1} ∩ F ≠ 1`. Then `g F_0 g^{-1} ∩ F_0 ≠ 1`, so
`g ∈ F_0`. Malnormality in `F_0` then gives `g ∈ F`.

**Quasiconvex.** A finitely generated subgroup of a free group is quasiconvex in it. A quasiconvex subgroup of a
quasiconvex subgroup is quasiconvex.

**No power of `c = x` is conjugate into `F`.** Suppose `g x^n g^{-1} ∈ F ⊂ F_0` with `n ≠ 0`. Then
`g F_0 g^{-1} ∩ F_0 ∋ g x^n g^{-1} ≠ 1`, so `g ∈ F_0`. That contradicts the second check.

**Consequences.**
- `E(c) ∩ F = 1`, where `E(c)` is the maximal cyclic subgroup containing `c`. If `c_0^l ∈ F` with `c = c_0^k`, then
  `c^l ∈ F`, so `l = 0`.
- **(B)** For every `r` there is `B_c(r)` with `diam(N_r(h <c>) ∩ N_r(g F)) <= B_c(r)` for all `g, h`. This is the
  argument of (Q2) with `<c>` and `F`, both quasiconvex with `u <c> u^{-1} ∩ F = 1` for all `u`: a long coarse
  intersection gives, by pigeonhole on the bounded connectors, a nontrivial element of some `u <c> u^{-1} ∩ F`.

## Step 2. The semigroup `W`

Since `Gamma` is torsion-free, `E(c)` is infinite cyclic. Replace `c` by a generator of `E(c)`. If a power of the
generator were conjugate into `F`, so would be a power of the old `c`. So Step 1 still holds, and now `E(c) = <c>`.
Fix a finite `S ⊂ Gamma \ <c>` with `S ∪ {c}` generating `Gamma` (drop from a finite generating set its elements
in `<c>`). Put `A = A_m = {c^m, c^{m+1}} ∪ {c^m gamma c^m : gamma ∈ S}`, and let `W` be the semigroup it generates.

**Paths.** A word `a_1 ... a_n` in `A` defines the path that concatenates:
- the geodesic `c`-axis segments of the powers `c^m`, `c^{m+1}`, merging adjacent powers into one segment;
- geodesics of length `<= max_S |gamma|` for the letters `gamma`.

Since `gamma ∉ E(c)`, the axes of `c` and `gamma c gamma^{-1}` have distinct endpoints. So the Gromov products at the
junctions, `(c^{-p} · gamma c^q)_1` for `p, q >= m`, are bounded by `B_S`, independent of `m`. By (Q3), for
`m >= m_1` every such path is a `(lambda_W, eps_W)`-quasi-geodesic, with constants independent of `m`. Its Morse
constant is `M_W`. Every infinite word `omega ∈ A^N` defines a quasi-geodesic ray, with endpoint `e(omega) ∈ dGamma`.
The map `e` is continuous, and `e(p omega) = p e(omega)`.

**(i) Generation.** `c = c^{m+1} c^{-m}` and `gamma = c^{-m} (c^m gamma c^m) c^{-m}` lie in `<A>`. So `<A> = Gamma`.

**(ii) Transversality (I1).** Let `s ∈ W`. A geodesic `[1, s]` is within `M_W` of the path of `s`. A subsegment of
`[1, s]` of length `t` inside `N_r(g F)` gives a subpath of the path of `s` of length `>= t - 2 M_W` inside
`N_{r + M_W}(g F)`. Its `c`-axis parts are separated by `gamma`-parts of length `<= max_S |gamma|`, and each lies in
`N_{r'}(h <c>) ∩ N_{r'}(g F)` for `r' = r + M_W + |c|`. So each has length `<= B_c(r')` by (B). Consecutive `c`-parts
are at least `m |c|_{st} - O(1)` long, where `|c|_{st} > 0` is the stable length. So for `m` large a subpath meets at
most two of them. Hence

`D(r) = 2 B_c(r + M_W + |c|) + max_S |gamma| + 2 M_W + 1`

works for all `s ∈ W`. It works for `s^{-1}` too: `[1, s^{-1}] = s^{-1} [s, 1]`, and `s^{-1} g F` is a coset. `D`
does not depend on `m`.

**Junction bound and double-coset length.** By Step 1 of the skeleton proof, (ii) gives
`(f · s)_1 <= B := D(delta + kappa) + delta` for `f ∈ F`, `s ∈ W^±`. Let `f_1, f_2 ∈ F`, `s ∈ W^±`, with
`|s| > 2B + delta`.
- `|f_1 s| >= |f_1| + |s| - 2B`.
- `(s^{-1} · s^{-1} f_1^{-1})_1 >= |s| - B`.
- By the four-point condition, `B >= (s^{-1} · f_2)_1 >= min(|s| - B, (s^{-1} f_1^{-1} · f_2)_1) - delta`. So
  `(s^{-1} f_1^{-1} · f_2)_1 <= B + delta`.

Therefore

`|f_1 s f_2| >= |f_1| + |s| + |f_2| - 4B - 2 delta >= |s| - K_1`, with `K_1 := 4B + 2 delta`. (3)

**(iii) `F s F ≠ F s^{-1} F`.** Suppose `s^{-1} = f_1 s f_2`, with `s ∈ W` and `f_i ∈ F`.
- **`f_1` is short.** Let `u = f_1 s f_2`. By (3) and `|s f_2| <= |s| + |f_2|`,
  `(u · f_1)_1 = (|u| + |f_1| - |s f_2|) / 2 >= |f_1| - K_1 / 2`. Since `u = s^{-1}` and `(s^{-1} · u)_1 = |s|`, the
  four-point condition gives `B >= (s^{-1} · f_1)_1 >= min(|s|, |f_1| - K_1/2) - delta`. So `|f_1| <= 3B + 2 delta`,
  and `f_1` lies in the finite set `Phi = F ∩ B_{3B + 2 delta}`.
- **Both geodesics start along the `c`-axis.** The path of `s^{-1}` starts along `c^{-m}`, and the path of `u` starts
  along `f_1 c^m`. So `(c^{-m} · f_1 c^m)_1 >= m |c|_{st} - C'`, with `C'` independent of `m`.
- **This bound is impossible for large `m`.** For each `f_1 ∈ Phi`, `(c^{-m} · f_1 c^m)_1` stays bounded as
  `m -> ∞` unless `c^- = f_1 c^+`, where `c^±` are the fixed points of `c`.
  - If `c^- = f_1 c^+`, then `f_1 c f_1^{-1}` and `c` share a fixed point, so `f_1 c f_1^{-1} ∈ E(c)`. Then `f_1`
    preserves `{c^+, c^-}`, so `f_1 ∈ E(c) ∩ F = 1`.
  - But `f_1 = 1` would give `c^- = c^+`, which is false.

  As `Phi` is finite, there is `m_0 >= m_1` such that (iii) holds for all `m >= m_0` and all `s ∈ W` with
  `|s| > 2B + delta`. All `s ∈ W` have `|s| >= m |c|_{st} - O(1)`.

Fix `m >= m_0` with also `m |c|_{st} - O(1) > 2B + delta`.

## Step 3. The semigroup Neumann lemma

**Lemma A.** Let `K_1, ..., K_N` be infinite-index quasiconvex subgroups of `Gamma` (the trivial group allowed), and
`R >= 0`. Then `W ⊄ U := ∪_i B_R K_i B_R`.

*Proof.* `B_R K B_R = ∪_{b ∈ B_R} N_R(b K)`, since `K B_R = N_R(K)`. So `U` is a finite union of sets `N_R(g_l K_l)`.
Suppose `W ⊂ U`.

1. **Every endpoint lies in a translated limit set.** Let `omega ∈ A^N`. Its prefixes lie in `W ⊂ U`. By pigeonhole,
   infinitely many prefixes lie in one `N_R(g_l K_l)`, and they converge to `e(omega)`. Hence
   `e(omega) ∈ g_l Lambda_{K_l}`. This is impossible for `K_l = 1`, whose neighbourhoods are finite. So
   `A^N = ∪_l e^{-1}(g_l Lambda_{K_l})`, a finite union of closed sets.
2. **Baire.** By Baire, some `e^{-1}(g_l Lambda_{K_l})` contains a cylinder `[p]` with `p ∈ W`. Then
   `p e(A^N) ⊂ g_l Lambda_{K_l}`, so `e(A^N) ⊂ Lambda_{K''}` with `K'' = p^{-1} g_l K_l g_l^{-1} p`. This `K''` is
   quasiconvex of infinite index.
3. **`W` lies near `K''`.** Each `w ∈ W` is a vertex of the path of some `omega` (extend its word). That path is a
   `(lambda_W, eps_W)`-quasi-geodesic ray from `1 ∈ K''` to a point of `Lambda_{K''}`. So it lies in `N_rho(K'')`,
   with `rho` depending on the quasiconvexity constant of `K''`, `delta` and `M_W`. Hence `W ⊂ K'' B_rho`.
4. **Finite index.** The set `O = {K'' w : w ∈ W}` of right cosets is contained in `{K'' b : b ∈ B_rho}`, so it is
   finite. For `a ∈ A`, right multiplication `K'' w -> K'' w a` maps `O` into `O` (as `W a ⊂ W`) and is injective. So
   it is a bijection of `O`, and `O` is invariant under `a^{-1}` as well. So `O` is invariant under `<A> = Gamma`. Since
   `Gamma` acts transitively on `K'' \ Gamma`, we get `K'' \ Gamma = O`, so `K''` has finite index. Contradiction. ∎

## Step 4. The killing elements

Hyperbolic groups are countable. So their finitely generated subgroups, and among them the infinite-index quasiconvex
ones, form a countable set. Enumerate all pairs `(H, R)` of such a subgroup and an integer `R >= 0` as
`(H_1, R_1), (H_2, R_2), ...`. Inductively choose

`s_j ∈ W \ ( B_{ell_j} ∪ ∪_{i <= j} B_{R_i} H_i B_{R_i} )`, with `ell_j = max(|s_{j-1}| + K_1, L_0)`.

This is possible by Lemma A, with `B_{ell_j} = B_{ell_j} {1} B_0`. Here `L_0 = L_0(Gamma, F, D)` is the constant of
Theorem 2 of the skeleton claim, for the `D` of Step 2(ii).

**(I2) holds for `I = {s_j}`.** Let `i < j`. If `F s_j^{±1} F = F s_i^{±1} F`, then `s_i^{±1} ∈ F s_j^{±1} F`. By (3),
`|s_i| >= |s_j| - K_1 > |s_{j-1}| >= |s_i|`, a contradiction. For `i = j`, use Step 2(iii). Also `s_j ∉ F`, since
`1 ∉ F s_j F` by (3).

**(I1)** holds by Step 2(ii). **(I3)** holds with `L_I >= L_0`.

## Step 5. The code

Write `a, b` for the free basis `y, yxxyx` of `F`, and `A_F = a^{-1}`, `B_F = b^{-1}`.

**Base letters.** Take the labellings `F_n : Z/q_n -> {a, A_F, b, B_F, hole}` of Step 2 of
`fpbs-quasiconvex-null-small-classes-exist-on-free-boundary-proof`, built by the Toeplitz step only (no overwrites).
Here `q_n = 2^{n+2}`. They satisfy (T), (S) and (H) there:
- **(T)** alternating types by parity;
- **(S)** `F_n(-y) = F_n(y)^{-1}`;
- **(H)** holes exactly at `0` and `q_n/2`.

The set of `y ∈ Omega` that are stage-`n` holes for infinitely many `n` is null, by Borel--Cantelli. Off it, `F_n(y)` is
eventually constant; call the limit `F_pf(y)`.

**Windows.** Choose stages `n_1 < n_2 < ...` with `n_{j+1} >= n_j + 3`, and `r_j = q_{n_j}/8 + 1`. Call `y` a
**stage-`j` window** if `y ≡ ± r_j mod q_{n_j}`. Put

`G(y) = s_j` if `y ≡ r_j`, `G(y) = s_j^{-1}` if `y ≡ -r_j (mod q_{n_j})`, and `G(y) = F_pf(y)` otherwise.

- **Windows are unique.** `2 r_j = q_{n_j}/4 + 2 ≢ 0 mod q_{n_j}`, so `r_j ≢ -r_j`. For `i < j`, `q_{n_j}/8 ≡ 0 mod
  q_{n_i}`. So a stage-`j` window is `≡ ±1 mod q_{n_i}`, while `± r_i ≡ ±(q_{n_i}/8 + 1)`. These differ, as
  `q_{n_i}/8 ≠ 0` and `q_{n_i}/8 + 2 ≢ 0`. So each `y` is a window of at most one stage, with one sign.
- **Windows are separated.** Two windows of the same stage `j` differ by at least `min(2 r_j, q_{n_j} - 2 r_j) >=
  q_{n_j}/4 - 2`. A stage-`i` and a stage-`j` window (`i < j`) differ mod `q_{n_i}` by at least `q_{n_i}/8`. So any
  two windows are at distance `>= q_{n_1}/8`.
- **Every tail contains every stage.** Each stage-`j` residue class meets every forward half-orbit infinitely often.

Let `X_0` be the set of `x` such that `G(x + t)` is defined for all `t ∈ Z`. It is conull and `T`-invariant, and
`X_0 = -X_0` since holes and windows are symmetric. By (S) and the sign choice, `G(-y) = G(y)^{-1}`.

**Skeleton conditions.** Maximal `F`-runs lie between consecutive windows, so they have length `>= q_{n_1}/8 - 1`. They
consist of consecutive `F_pf` letters, which alternate type by (T), so they are reduced words in `a, b`. Insertions are
never adjacent. Choose `n_1` with `q_{n_1}/8 - 1 >= L_0`. With Step 4, the code is a symmetric skeleton code with
(I1)--(I3) and `L_I, L_F >= L_0`.

**Forward injectivity.** The letters `s_j^{±1}` are pairwise distinct: their double cosets are distinct, by Step 4. They
are also distinct from the `F`-letters, since `s_j ∉ F`. For `y ∈ X_0`,

`{t >= 1 : G(y + t) = s_j} = {t >= 1 : y + t ≡ r_j mod q_{n_j}}`.

This set is nonempty, and it determines `y mod q_{n_j}`. As `n_j -> ∞`, the forward coding determines `y ∈ Omega`.

## Step 6. Quasiconvex-null

By Theorem 2(1) of the skeleton claim, every `P_x` is a `(lambda', eps')`-quasi-geodesic ray. Let `H` be
infinite-index quasiconvex, and suppose `zeta(x) ∈ g Lambda_H` for some `g ∈ Gamma`. Geodesic rays from `g` to
points of `g Lambda_H` lie in `N_{kappa'}(g H)`, with `kappa'` depending on `H` and `delta`. By (Q3), a tail of `P_x`
lies in `N_{R(H)}(g H)`, with `R(H) = kappa' + C_0 + M`.

Pick `i` with `H_i = H` and `R_i >= R(H)`. Take a window `x + k + 1` of stage `j >= i` in that tail. The vertices
`p = c_k(x)^{-1}` and `p s_j^{±1}` both lie in `N_{R_i}(g H)`. So `p = g h_1 e_1` and `p s_j^{±1} = g h_2 e_2`, with
`h_1, h_2 ∈ H` and `|e_1|, |e_2| <= R_i`. Then

`s_j^{±1} = e_1^{-1} h_1^{-1} h_2 e_2 ∈ B_{R_i} H B_{R_i}`.

The double neighbourhood `B_R H B_R` is closed under inversion, so `s_j ∈ B_{R_i} H_i B_{R_i}` with `i <= j`. That
contradicts Step 4. Hence `zeta(x) ∉ Gamma Lambda_H` for every `x ∈ X_0`, and `nu(Gamma Lambda_H) = 0`.

## Step 7. Ergodicity, nonatomicity and death

- **Ergodicity.** `zeta(x + 1) = G(x + 1)^{-1} zeta(x)`. So a `Gamma`-invariant set pulls back under `zeta` to a
  `T`-invariant set, which is null or conull because the odometer is ergodic.
- **Nonatomicity.** By Theorem 2(3) of the skeleton claim and forward injectivity, (MR) holds. With `g = 1`, `zeta` is
  countable-to-one, so `zeta_* m_Omega` has no atoms, and neither does `nu`.
- **(MR±).** It holds by symmetry.
- **Death.** Theorem 1 of `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups` applies to `nu`, which is carried by
  `Gamma zeta(X_0)`. The diagonal action on `nu x nu`, on its Maharam extension, and on every imp action over `nu` is
  totally dissipative. So none of these is ergodic PDR, and `nu` is no BB boundary class.

**`Sp(n,1)`.** A cocompact lattice in `Sp(n,1)` is hyperbolic, and it has a torsion-free finite-index subgroup
(Selberg). Fixed price passes between a group and its finite-index subgroups (Gaboriau's induction formula). ∎
