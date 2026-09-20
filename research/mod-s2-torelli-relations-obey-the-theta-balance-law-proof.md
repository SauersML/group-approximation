---
rg: 2
id: mod-s2-torelli-relations-obey-the-theta-balance-law-proof
kind: route
title: Wind each relation around the modular unit theta_m/theta_m' on the Torelli complement at level (4,8), then transfer down from any Gamma' <= Gamma(2)
target: mod-s2-torelli-relations-obey-the-theta-balance-law
requires: []
artifacts:
  - research/artifacts/van-der-geer-chi10-baily-borel-verified.md
  - experiments/mod-s2-theta-balance-2026-09-17/theta_check.py
  - experiments/mod-s2-theta-balance-2026-09-17/theta-check.json
  - experiments/mod-s2-theta-balance-2026-09-17/balance.py
  - experiments/mod-s2-theta-balance-2026-09-17/balance-gamma4.json
  - experiments/mod-s2-theta-balance-2026-09-17/balance-U.json
  - experiments/mod-s2-theta-balance-2026-09-17/transversal.py
  - experiments/mod-s2-theta-balance-2026-09-17/transversal-gamma4.json
  - experiments/mod-s2-theta-balance-2026-09-17/transversal-U.json
---

Notation is that of the target. `H_2` is the Siegel upper half space. `Delta = {z = 0}` is the diagonal,
the period locus of the standard splitting `sigma_0`, and `D~ = union of g Delta` over
`g in Sp_4(Z)` is the reducible locus. The translate `g Delta` is the locus of the splitting
`g sigma_0`. The even theta constants are
`theta_m(tau) = sum_(n in Z^2) exp(pi i (n + a/2)^T tau (n + a/2) + pi i (n + a/2)^T b)`, for
`m = [a; b]` with `a, b in {0,1}^2` and `a . b` even. There are ten of them.

## Inputs

- **(Mess)** *Trust: Mess, as in the Remark of `mod-s2-holomorphic-torelli-certificates-have-unbounded-mass`.*
  The period map identifies Torelli space `Teich_2 / I` with `H_2 - D~`. Under this identification,
  a small loop around a smooth point of `g Delta` is the separating twist of the splitting
  `g sigma_0`, up to conjugacy in `I`.
- **(Q1)** (verbatim in the artifact) `chi_10` vanishes to order exactly 2 along `Delta`, and its zero
  divisor is `2 D~`.
- **(I1)** *Igusa, "On the graded ring of theta-constants" (1964); standard, not quoted in the repo.* For all
  even `m, n`, the product `theta_m theta_n` is a modular form of weight 1 for `Gamma(4,8)`, with the same
  (trivial) multiplier for all pairs. Hence each ratio `theta_m / theta_n` is a `Gamma(4,8)`-invariant
  meromorphic function on `H_2`.
  - Checked numerically in `theta_check.py`: invariance holds to `1e-15` under four generators of
    `Gamma(4,8)`, and fails, by a sign, for `[[I, 0], [diag(4,0), I]]`, which lies in `Gamma(4) - Gamma(4,8)`.
- **(I2)** *Igusa; standard.* `chi_10 = c prod_m theta_m^2` with `c != 0`.
- **(I3)** *Theta transformation formula; standard.* For `M in Sp_4(Z)`,
  `theta_(M.m)(M tau) = u(M, m, tau) theta_m(tau)`, where `u` is holomorphic and nowhere zero and
  `m -> M.m` is the affine action on characteristics. It factors through `Sp_4(F_2)` and is trivial on
  `Gamma(2)`.
- **(F)** On `Delta`, `theta_[a1 a2; b1 b2](diag(tau_1, tau_2)) = theta_[a1;b1](tau_1) theta_[a2;b2](tau_2)`,
  from the product form of the sum. A genus-one theta constant vanishes iff its characteristic is odd,
  i.e. `[1;1]`. So among the ten even `theta_m`, exactly `m_0 = [11; 11]` vanishes identically on `Delta`.
  Differentiating the sum termwise, `d theta_(m_0)/dz` at `z = 0` equals `2 pi i f(tau_1) f(tau_2)`,
  where `f(tau) = sum_(v in Z + 1/2) v exp(pi i tau v^2 + pi i v)`. Up to a nonzero constant, `f` is the
  derivative at 0 of the odd genus-one theta function. It is nonzero by Jacobi's formula
  `theta'_11 = -pi theta_00 theta_01 theta_10`. So `theta_(m_0)` has a simple zero along `Delta`.
  Numerically, `theta-check.json` gives `|d theta_(m_0)/dz| = 1.30` at a sample point, while the other
  nine `|theta_m|` there are at least `0.76`.

## Step 1: the zero set of theta_m is the Humbert fibre over one level-two splitting

**(1a) The labelling.** By (F), `m_0` is the only even characteristic whose theta vanishes on `Delta`.
By (I3), `theta_n` vanishes on `g Delta` iff `theta_(g^(-1).n)` vanishes on `Delta`, iff `n = g.m_0`.
So each translate `g Delta` carries a well-defined label `m(g Delta) = g.m_0`, the unique even `m` with
`theta_m = 0` on it.
- Let `Stab(sigma_0) <= Sp_4(Z)`, the conjugate of `(SL_2 x SL_2) x| Z/2`, be the stabilizer of the
  splitting. It preserves `Delta`, hence fixes `m_0`.
- Its image in `Sp_4(F_2) = S_6` is the full stabilizer of the level-two splitting
  `sigma_0 mod 2`, of order 72 and index 10. The stabilizer of `m_0` also has index 10, since the ten
  even characteristics form one orbit.
- So the two stabilizers are equal, and `g sigma_0 mod 2 -> g.m_0` is an `Sp_4(F_2)`-equivariant
  bijection from level-two splittings to even characteristics.
- Hence the label of `g Delta` depends only on the level-two splitting of `g sigma_0`. From now on each
  level-two splitting is identified with its characteristic `m`.

**(1b) Multiplicities.** Each `theta_m` vanishes only on `D~`, since by (I2) and (Q1)
`prod theta_m^2` has zero set `D~`. Along each translate `g Delta`, (I3) and (F) give the orders of
vanishing:
- `ord_(g Delta) theta_m = 1` for `m = m(g Delta)`;
- `ord_(g Delta) theta_m = 0` for the other nine `m`.

This is consistent with (Q1): the total order `2 * 1 = 2` of `prod theta_m^2 = chi_10 / c` is correct.

## Step 2: the law at Gamma' <= Gamma(4,8)

Let `Gamma' <= Gamma(4,8)` have finite index. Then:
- `Gamma' <= Gamma(4)` is torsion-free and misses `-1`.
- So `Lambda' = pi^(-1)(Gamma')` misses the hyperelliptic involution. It is torsion-free, since a torsion
  element maps to `1` in `Gamma'` and so lies in the torsion-free group `I`.
- `Lambda'` acts freely on the contractible `Teich_2`.
- By (Mess), `Y = Lambda' \ Teich_2 = Gamma' \ (H_2 - D~) = X - D`. Here `X = A_2(Gamma')` is a complex
  manifold and `D` is the image of `D~`.
- Hence `pi_1(Y) = Lambda'`.

The components of `D` are the images `D_o` of the translates in one `Gamma'`-orbit `o` of splittings.
Each is irreducible, being the image of one `g Delta`. By (Mess), the meridian `mu_o` of `D_o` at a smooth
point represents `[t_o]` in `H_1(Lambda') = H_1(Y)`.

Fix even `m != m'`. By (I1), `f = theta_m / theta_(m')` descends to a meromorphic function on `X`. By
(1b) it is holomorphic and nowhere zero on `Y`. So `f : Y -> C^*` induces `f_* : H_1(Y) -> H_1(C^*) = Z`.
The value `f_*(mu_o)` is the winding number of `f` around a small loop linking `D_o` once. That is the
order of `f` along `D_o`, computed on a translate upstairs:

    f_*(mu_o)  =  ord theta_m - ord theta_(m')  =  [m(o) = m] - [m(o) = m'].

Let `b in B(Gamma')`, so that `sum_o b_o mu_o = 0` in `H_1(Y)`. Applying `f_*` gives

    0  =  sum_o b_o ([m(o) = m] - [m(o) = m'])  =  s_m(b) - s_(m')(b).

So all ten fibre sums are equal. They add up to `aug(b)`, so each is `aug(b)/10`. Since `s_m(b)` is an
integer, `aug(b) in 10 Z`. This proves (TB1) at `Gamma' <= Gamma(4,8)`.

## Step 3: transfer to every Gamma' <= Gamma(2)

**Lemma (transfer).** Let `G` be a group and `N <= H <= G` with `N` normal in `G` and `[G : H] = d`
finite. Let `S` be a `G`-set of elements of `N`, closed under conjugation. Put `O_G = S/G` and
`O_H = S/H`, and let `B_G <= Z^(O_G)` and `B_H <= Z^(O_H)` be the kernels of `e_o -> [s]` into
`H_1(G)` and `H_1(H)`. Choose right coset representatives `g_1, ..., g_d` of `H` in `G`, and put
`T(e_(Gs)) = sum_i e_(H g_i s g_i^(-1))`. Then:
- `T` is well defined;
- `T(B_G) <= B_H`;
- each `e_o` goes to a sum of `d` unit vectors.

*Proof.* For `s in N`, `H g_i s = H (g_i s g_i^(-1)) g_i = H g_i`, since `g_i s g_i^(-1) in N <= H`. So
the transfer `tr : H_1(G) -> H_1(H)` gives `tr[s] = sum_i [g_i s g_i^(-1)]`.

Replacing `s` by `h s h^(-1)` with `h in G`, or changing the representatives, permutes the cosets `H g_i`.
It therefore replaces each `g_i s g_i^(-1)` by an `H`-conjugate of some `g_j s g_j^(-1)`, so `T` is well
defined. Moreover `tr o phi_G = phi_H o T`, so `T` maps `ker phi_G` into `ker phi_H`. QED.

Now let `Gamma' <= Gamma(2)` have finite index, and put `Gamma'' = Gamma' cap Gamma(4,8)`. Apply the
lemma as follows:
- `G = Lambda'`, or `Lambda'/<iota>` when `-1 in Gamma'` (the `Pbar` model);
- `H` is the image of `Lambda''`;
- `N` is the image of `I`, which maps isomorphically since `iota notin I`;
- `S` is the set of separating twists.

`I` acts transitively on the separating curves with a given homology splitting. Hence the
`Lambda'`-conjugacy classes of separating twists are the `Gamma'`-orbits of splittings, `S/G = O(Gamma')`,
and `B_G = B(Gamma')`. The same holds for `H`.

A conjugate `g_i t_s g_i^(-1) = t_(g_i s)` lies over the same level-two splitting as `s`, because `g_i`
maps into `Gamma(2)`, which acts trivially on level-two splittings. So `s_m(T b) = d s_m(b)` for every
`m`.

By Step 2 at `Gamma''`, for `b in B(Gamma')` we get `d s_m(b) = s_m(T b) = s_(m')(T b) = d s_(m')(b)`.
This proves (TB1) for `Gamma'`.

## Step 4: the corollaries

- **(TB2).** Let `b >= 0` be in `B` with `3 not| aug(b)`. Then `aug(b) != 0`. Put `s = s_m(b)`, the same
  for all `m`, so `aug(b) = 10 s`. Since `b >= 0` and `aug(b) != 0`, `s >= 1`, and `3 not| s`. Hence
  `A_+ in 10 Z` and `A_+ >= 10`. Also `aug(b) = 10` iff `s = 1`, iff `b` is nonnegative with fibre sums
  all equal to 1, iff `b` is a transversal.
- **(TB3).** *Pushforward lemma.* Let `Gamma'' <= Gamma'` have finite index, both in `Gamma(2)`. Every
  orbit `o''` of splittings under `Gamma''` lies in a single `Gamma'`-orbit `p(o'')`, over the same
  level-two splitting. The inclusion `Lambda'' -> Lambda'` sends `t_s` to `t_s`, hence `[t_(o'')]` to
  `[t_(p(o''))]` in `H_1(Lambda')`. So `p_* : Z^(O'') -> Z^(O')`, `(p_* b)_o = sum_(p(o'')=o) b_(o'')`,
  maps `B(Gamma'')` into `B(Gamma')`. It has the following properties:
  - it keeps `b >= 0`, `aug(b)` and every fibre sum `s_m(b)`;
  - it satisfies `||p_* b||_1 <= ||b||_1`.

  Hence `A_+(Gamma'') >= A_+(Gamma')`. The same holds for the least `l1` of a relation with
  `3 not| aug`.

  *At `Gamma_U`.* `transversal-U.json` shows that no transversal lies in `B(Gamma_U)`. So:
  - by (TB2), `A_+(Gamma_U) >= 20`;
  - the explicit mass-20 relation of `mod-s2-three-sylow-torelli-census` gives equality.

  *Least `l1`.* Let `w in B(Gamma_U)` with `3 not| aug(w)`. Then `aug(w) = 10 s`, `3 not| s`, and
  `||w||_1 >= sum_m |s_m(w)| = 10 |s|`. Suppose `|s| = 1`. Equality forces each fibre to carry exactly one
  nonzero entry, equal to `s`, so `s w` is a transversal, which is excluded. Since
  `||w||_1 = aug(w) mod 2` is even, `||w||_1 >= 12`. If `|s| >= 2`, then `||w||_1 >= 20`.

  By the pushforward lemma, both bounds hold at every finite-index `Gamma'' <= Gamma_U`. In any cofinal
  family, the members contained in `Gamma_U` form a cofinal subfamily. At those members:
  - (RF) gives at most `1/60`;
  - (TA3) gives at most `1/36`.

  Neither reaches the value `1/30`, which holds wherever it is computed.
- **(TB4).** If `s_m(b) = 0` for one `m`, then by (TB1) all fibre sums vanish and `aug(b) = 0`.
- **(TB5).** For `Gamma' <= Gamma(4,8)`, the characters `f_*` of Step 2, for the nine pairs `(m_1, m)`,
  restrict on `Z^O` to `x_o = [m(o) = m_1] - [m(o) = m]`. They span the fibre-constant vectors `x` with
  `sum_m x_m = 0`, which is `Bal^perp`.
  - `H^1(Gamma'; R) = 0` (congruence subgroups of `Sp_4(Z)` have finite abelianization), so
    `H_1(Lambda'; Q)` is spanned by meridians and `Hom(H_1(Lambda'), R) = Hom(Z^O / B, R)`.
  - At `Gamma(4)`, where only the squares are invariant, the same holds with `f^2`. The census count is
    `160 - 106 = 54 = 9 + 45`.

## Exact check

`balance.py gamma4` verifies (TB1) exactly on a `Z`-basis of `W(Gamma(4))`, with 0 violations
(`balance-gamma4.json`). This is independent of the theta inputs. It uses the `Pbar` Reidemeister-Schreier
model and its fibre labels, the ten standard twists keyed by triples of `{1..5}`, i.e. by 3|3 partitions of
the six branch points.

`balance.py U` does the same at `Gamma_U`, with 0 violations among 34 basis rows (`balance-U.json`).
`Gamma_U` is not in `Gamma(4,8)`, and `[Gamma(2) : Gamma_U] = 640` is even, so this run tests Step 3.

`transversal.py` computes the invariant map `Z^O -> Z^O / B` exactly, from a Smith decomposition. It then
counts transversals `x` with `x in B` by meet in the middle over the two halves of the fibres. The
counts are:
- 1024 at `Gamma(4)`, which matches (G4) of `mod-s2-gamma4-torelli-census-is-one-thirtieth`;
- 0 of `5^10` at `Gamma_U`.

Before searching, it checks that every basis row of `B` has invariant 0.
