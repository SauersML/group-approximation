# Strong Atiyah for Kazhdan groups: what is already known, and the SL_3(Z) question

Lane `strong-atiyah-kazhdan-group`, 2026-09-12. The task was to prove the Strong
Atiyah Conjecture (SAC) for some infinite torsion-free property (T) group, since
`atiyah-coproduct-inner-rank` recorded that none was known. That record is wrong,
and this note says so from source. It then pivots to the named open case
`SL_3(Z)`, reduces it to a finite 2-adic question, and settles half of that
question.

## 1. Status from source (arXiv LaTeX sources fetched and read on MSI)

- **Farkas--Linnell**, *Congruence subgroups and the Atiyah conjecture*,
  arXiv:math/0511747v2 (Contemp. Math. 420, 2006). Define
  `CS(i,d,p) = {A in Mat_d(Z_p) : A = I_d mod p^i}`, with `i >= 2` whenever
  `p = 2`.
  - Theorem 1.1: "let `G` be a torsion-free group which contains a normal
    subgroup of finite index isomorphic to `CS(u,d,p)`. Then there is a division
    ring `D(G)` such that `Qbar[G] <= D(G) <= U(G)`."
  - Theorem 1.2: "If `k` is a field of characteristic `p` then `k[Gamma]` is a
    domain", for `Gamma = CS(u,d,p)`.
  - Theorem 1.3: "If `K` is a field of characteristic `0` then `K[Gamma]` is a
    domain."
- **Fisher--Ng**, arXiv:2606.19606v1.
  - Section 1: "while it is not known whether `GL_m(Z)` satisfies [SAC], it has
    a finite-index subgroup that does by results of Farkas--Linnell and
    Jaikin-Zapirain"; the same holds for any finitely generated group linear in
    characteristic 0.
  - Section 1: "`Out(F_n)` has property (T) for `n >= 4`", citing
    Kaluba--Kielak--Nowak and Nitsche. For `n >= 5` the KKN abstract was checked
    from source: `Aut(F_n)` has (T) for `n >= 5`.
  - Section 2, Theorem `thm:p-adic-atiyah`: "If `G` is a torsion-free compact
    `p`-adic analytic group, then `G` satisfies the Strong Atiyah Conjecture over
    `C`" (Farkas--Linnell plus Jaikin-Zapirain base change). Also: SAC "is the
    case for subgroups of torsion-free groups".

**Consequence.** `Gamma(3) <= SL_3(Z)` lies in `CS(1,3,3)`, so it and all its
subgroups satisfy SAC over `C` and have domain group rings in characteristics
`0` and `3`. They are infinite, torsion-free and Kazhdan. So Kazhdan groups
satisfying SAC have been known since 2006. Torsion-free finite-index subgroups
of `Out(F_n)`, `n >= 4`, are known too (Fisher--Ng 2026). Landed as
`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah` and
`congruence-kazhdan-groups-satisfy-strong-atiyah`.

**Corrections forward** (edited in place, each with a dated note):
- `research/artifacts/atiyah-coproduct-inner-rank-2026-09-12.md` Section 3;
- `kazhdan-edge-coproduct-rank-is-inner-rank` scope bullet;
- `e33-no-unique-product-pairs-of-small-radius` host status: `E_3(3)` is a
  zero-divisor host only in characteristics other than `0` and `3`;
- `kaplansky-zero-divisor-conjecture`: known cases and the `E_3(3)` bullet;
- `zero-divisor-host-is-not-virtually-compact-special`: the "for every field"
  sentence.

Remark. The `p`-adic analytic case can also be proved directly, as Fisher--Ng
note (Harris, Lemma 1.10.1). For nonzero `f` in `Z_p[[U]]`, `U` uniform of
dimension `d`, the kernel of `f` on `Q_p[U/U^(p^k)]` has dimension at most
`e p^(k(d-1))`. Reduce mod `p` through the saturated kernel lattice, and bound the
kernel by that of the leading form in `gr F_p[[U]] = F_p[X_1..X_d]` acting on
`F_p[X]/(X_i^(p^k))`. Ore clearing of denominators in `Z_p[[U]]` extends this to
matrices, and Lück approximation along `Gamma cap U^(p^k)` finishes. This
lane re-derived that argument but did not land it, because the import already
covers it.

## 2. The pivot: SAC for SL_3(Z)

For a group with bounded torsion, SAC predicts `rk_{N(G)}(A) in (1/lcm) Z`, where
`lcm` is the least common multiple of the orders of finite subgroups.

**lcm(SL_3(Z)) = 24.** `SL_3(Z)` contains `S_4`, the rotation group of the cube.
If `F <= SL_3(Z)` is finite then `F x {+-I} <= GL_3(Z)` is finite of order
`2|F|`, and finite subgroups of `GL_3(Z)` have order at most 48. So `|F| <= 24`.
Orders are products of 2 and 3 only, since `Phi_q` has degree `> 3` for `q >= 5`,
and 9 does not divide `|F|`. So `lcm = 24`.

**Weak bound (landed): denominators divide 48.** For any finite-index subgroup
`H <= G`, `rk_G(A) = rk_H(res A) / [G:H]`. `Gamma(3)` has index `5616 = 2^4 3^3 13`
and `Gamma(4) <= CS(2,3,2)` has index `|SL_3(Z/4)| = 2^8 * 168 = 2^11 3 7`. Both
satisfy SAC, so `rk_G(A) in (1/5616)Z cap (1/43008)Z = (1/48)Z`.

**Odd primes cannot reach 24.** For `p` odd, a Sylow 2-subgroup of `SL_3(F_p)`
has order divisible by 16. It lifts to `SL_3(Z_p)`, since the kernel is pro-`p`.
It meets a torsion-free open subgroup trivially, so 16 divides every such index.

**Reduction (landed as a route).** Suppose `W <= SL_3(Z_2)` is open and
torsion-free with `v_2([SL_3(Z_2):W]) = 3`. Then:
- **2-part.** `H = W cap SL_3(Z)` has the same index, by density, and satisfies
  SAC over `C`, since `W` is torsion-free 2-adic analytic.
- **3-part.** `W`'s image in `SL_3(F_2)` has no element of order 3 or 7. The
  closure of a cyclic group contains its prime-to-2 torsion part. So the image
  is a 2-group and `W` is conjugate into the pro-2 Iwahori `I`, the preimage of
  the unitriangular `U`, of index 21. Then `[SL_3(Z_2):W] = 21 [I:W] = 168`.
- **Combine.** `gcd(168, 5616) = 24`, so `rk_G(A) in (1/24)Z`: SAC for `SL_3(Z)`,
  and then for `GL_3(Z) = SL_3(Z) x {+-I}`, lcm 48.

So **SAC for SL_3(Z) follows if the pro-2 Iwahori `I <= SL_3(Z_2)` has a
torsion-free subgroup of index 8.** The index is at least 8, because `I`
contains a conjugate of the dihedral group of order 8 in `SL_3(Z)`.

## 3. The level-4 census (landed)

Write `K_j = ker(SL_3(Z_2) -> SL_3(Z/2^j))`. Torsion in `K_1` consists of the
involutions `I - 2e`, `e` a rank-2 idempotent. `K_1` has no elements of order 4,
since `(i-1)/2` is not integral. `K_2` is torsion-free. Let `W <= I` have index
8, `K = W cap K_1`, and let `W-bar` be the image in `U`. Then
`[U : W-bar][K_1 : K] = 8`, so `|W-bar| = 2^c` and `[K_1:K] = 2^c`.

**If `W >= K_2`**, then `S = K/K_2` is a subspace of
`V = K_1/K_2 = sl_3(F_2)`, dimension 8. It has codimension `c`, contains none of
the 28 rank-2 idempotents `ebar`, and is normalized by `W-bar`. Every coset
`I + 2 ebar + K_2` contains the involution `I - 2e` for a Hensel lift `e`.
Exhaustive check (`experiments/strong-atiyah-sl3z/iwahori_level4_census.py`,
seconds):
- no codimension-2 subspace avoids the 28, hence no hyperplane does;
- 1500 codimension-3 subspaces avoid them, and none is normalized by any of the
  21 subgroups of order 8.

So **no torsion-free index-8 subgroup of `I` contains `K_2`.** An example
avoiding subspace, with no normalizer of order 8, is `T cap V` for
`T = F_8 + F_8 sigma` inside `End_{F_2}(F_8)`. Every rank-1 map has a nonzero
`sigma^2` component, but the normalizer of `T` is the Frobenius group of order
21.

## 4. What remains (open claim)

Every index-8 subgroup `W` of `I` contains `K_4`. For a 2-group,
`Phi(A) = A^2 [A,A]` is monotone. `Phi(K_1) = K_2`, since `sl_3(F_2)` is perfect,
and `K_2^2 = K_3`, `K_3^2 = K_4`, since `K_2` is uniform. A chain of index-2 steps
`K <= K'' <= K' <= K_1` then forces `K' >= K_2`, `K'' >= K_3` and `K >= K_4`. So
the question is finite: does `I/K_4`, a 2-group of order `2^27`, have an index-8
subgroup containing no image of an involution of `SL_3(Z_2)`? Involutions form
two classes over `Z_2` (Diederichsen--Reiner: `diag(1,-1,-1)` and
`swap + (-1)`), so the forbidden set is the intersection of two
`SL_3(Z/16)`-conjugacy classes with `I/K_4`. A quick global refutation fails:
`Phi^3(I) <= K_2` contains no involution. The next step is a GAP pc-group search
on MSI through the three index-2 steps, testing the last step by linear algebra
over `M''/Phi(M'')`.
