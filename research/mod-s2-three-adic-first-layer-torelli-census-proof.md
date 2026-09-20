---
rg: 2
id: mod-s2-three-adic-first-layer-torelli-census-proof
kind: route
title: Classify the index-three subgroups between Gamma(9) and Gamma(3) by adjoint orbits, bound their new real Torelli characters by the count of off-diagonal splittings via the Hochschild-Serre sequence and property (T), and run the iota-quotient census on each orbit
target: mod-s2-three-adic-first-layer-torelli-census
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
  - genus-two-torelli-freely-generated-by-separating-twists
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
artifacts:
  - experiments/mod-s2-three-adic-census-2026-09-17/orbits.py
  - experiments/mod-s2-three-adic-census-2026-09-17/orbits.json
  - experiments/mod-s2-three-adic-census-2026-09-17/threeadic.py
  - experiments/mod-s2-three-adic-census-2026-09-17/test_quotient.py
  - experiments/mod-s2-three-adic-census-2026-09-17/equivariant.py
  - experiments/mod-s2-three-adic-census-2026-09-17/local.py
  - experiments/mod-s2-three-adic-census-2026-09-17/lelim.c
  - experiments/mod-s2-three-adic-census-2026-09-17/test_lelim.py
  - experiments/mod-s2-three-adic-census-2026-09-17/compare.py
  - experiments/mod-s2-three-adic-census-2026-09-17/summarize.py
  - experiments/mod-s2-three-adic-census-2026-09-17/first-layer-results.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-0.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-1.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-2.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-3.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-4.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-5.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-6.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-7.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-8.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-9.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-10.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-11.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-12.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-13.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-14.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-15.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-flat0.json
---

Notation as in the target.

**Inputs.**
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`: `pi : M -> Sp_4(Z)` is onto
  with kernel the Torelli group `K`. So `M_3 / M_Y = Gamma(3) / G_Y = Z/3`, and every separating twist
  lies in every `M_Y`.
- **[FREE]** `genus-two-torelli-freely-generated-by-separating-twists`: `K` is free on separating twists,
  one per symplectic splitting of `H_1(S_2; Z)`. So `H_1(K; Z) = Z[Sigma]` is the permutation module on
  the set `Sigma` of integral splittings, and `M` acts through `Sp_4(Z)`.
- **[TA]** `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`: the definitions of `v_c`,
  `W`, `d`, (TA2) monotonicity and (TA3) certificates.
- **[T]** Kazhdan: `Sp_4(Z)` has property (T), so every finite-index subgroup has finite abelianization.
- **[CONG]** The standard facts `Gamma(3)/Gamma(9) = sp_4(F_3)` via `I + 3X -> X mod 3`, equivariant for
  conjugation by `Sp_4(Z)` acting through `Sp_4(F_3)`, and `Gamma_SL2(3)/Gamma_SL2(9) = sl_2(F_3)`.

## Step 1. The index-three layer

- The trace form `(X, Y) -> tr(XY)` on `sp_4(F_3)` is nondegenerate and `Sp_4`-invariant. So every
  homomorphism `Gamma(3)/Gamma(9) -> F_3` is `chi_Y(I + 3X) = tr(YX)` for a unique `Y`.
- The index-three subgroups `Gamma(9) < G < Gamma(3)` are the kernels `G_Y`, `Y != 0`, with
  `G_Y = G_(-Y)`. There are `(3^10 - 1)/2 = 29524` of them.
- Conjugation by `g in Sp_4(Z)` carries `G_Y` to `G_(gbar Y gbar^-1)`. So `G_Y` and `G_Y'` are conjugate
  iff `Y'` is `Sp_4(F_3)`-conjugate to `+-Y`. Conjugation by a lift in `M` carries twists to twists, so
  `d(G_Y)` depends only on that class.
- `orbits.py` finds the classes by union-find over the five generator transvections (which generate
  `Sp_4(F_3)`) and `Y -> -Y`. There are 16 classes, of sizes `80, 240, 480, 540, 540, 1080, 1080, 4320,
  4320, 5184, 5184, 5760, 6480, 6480, 8640, 8640` (counted with sign; sum `3^10 - 1`).

## Step 2. Lemma A: new real characters are bounded by off-diagonal splittings

For a level-three splitting `s = P + P^perp` of `F_3^4`, put
`off(s) = {Y in sp_4(F_3) : Y P <= P^perp, Y P^perp <= P}`, and let `n_Y` be the number of `s` with
`Y in off(s)`.

**Lemma A.** Let `Y != 0` and `chi = chi_Y`. Let `C_chi` be `C` with `M_3` acting through `chi o pi`
followed by a primitive cube root of unity.
1. `b_1(M_Y) = 24 + 2 a_Y`, where `a_Y = dim H_1(M_3; C_chi) <= n_Y`.
2. The twist classes of `M_Y` are the images of the basis of `H_1(K)_(G_Y) = Z[G_Y \ Sigma]`, and
   `|G_Y \ Sigma| = 45 + 2 n_Y`. Over a level-3 splitting `s` with `Y in off(s)` there are 3 orbits;
   over every other `s` there is one.
3. If `n_Y = 0`, then `b_1(M_Y) = 24` and `G_Y \ Sigma` is the set of the 45 level-3 splittings. With
   that indexing, `3 W(Gamma(3)) <= W(G_Y) <= W(Gamma(3))`.

*Proof of 1.*
- Shapiro's lemma gives `H_1(M_Y; C) = H_1(M_3; C) + H_1(M_3; C_chi) + H_1(M_3; C_chibar)`. Complex
  conjugation exchanges the last two summands, and `b_1(M_3) = 24` (frame-3 census in [TA]).
- `K` acts trivially on `C_chi`. The low-degree Hochschild-Serre sequence of
  `1 -> K -> M_3 -> Gamma(3) -> 1` with coefficients `C_chi` is exact:
  `H_0(Gamma(3); H_1(K; C) (x) C_chi) -> H_1(M_3; C_chi) -> H_1(Gamma(3); C_chi) -> 0`.
- By Shapiro, `H_1(Gamma(3); C_chi)` is a summand of `H_1(G_Y; C)`, which is `0` by [T].
- By [FREE], `H_1(K; C) (x) C_chi` is the sum over `Gamma(3)`-orbits `O` on `Sigma` of
  `Ind_(Stab(s_O))^(Gamma(3)) C_chi`. So its coinvariants are the sum of `H_0(Stab_(Gamma(3))(s_O); C_chi)`.
  Each such term is `C` if `chi` is trivial on the stabilizer, and `0` otherwise.
- *Orbits.* `Sp_4(Z)` is transitive on `Sigma`, with stabilizer `H = (SL_2 Z x SL_2 Z) x| Z/2`. Since
  `Gamma(3)` is normal, the `Gamma(3)`-orbits are `Sp_4(F_3) / Hbar`. `SL_2(Z) -> SL_2(F_3)` is onto, so
  `Hbar` is the full stabilizer of the reduced splitting. The orbits are therefore the 45 level-3 splittings.
- *Stabilizers.* `Stab_(Gamma(3))(s) = Gamma_SL2(3) x Gamma_SL2(3)` in block form. The swap coset is
  excluded because it moves `P mod 3`. By [CONG], its image in `sp_4(F_3)` is `d(s) = sp(P) + sp(P^perp)`.
- *Triviality.* `chi` kills `d(s)` iff `tr(Y_PP X_1) + tr(Y_QQ X_2) = 0` for all `X_1, X_2` in `sl_2(F_3)`.
  The diagonal blocks `Y_PP`, `Y_QQ` lie in `sl_2(F_3)`, and the trace form of `sl_2(F_3)` is nondegenerate.
  So the condition is `Y_PP = Y_QQ = 0`, i.e. `Y in off(s)`.
- Hence `a_Y <= n_Y`.

*Proof of 2.*
- Two separating twists over the same integral splitting are conjugate in `K <= M_Y`. So by [FREE], the
  `M_Y`-conjugacy classes of basis twists are `G_Y \ Sigma`. The census classes `v_c` are their images in
  `H_1(M_Y)`.
- Inside the `Gamma(3)`-orbit `Gamma(3)/Stab` over `s`, the `G_Y`-orbits are
  `G_Y \ Gamma(3) / Stab = F_3 / chi(Stab)`. This set has 3 elements iff `Y in off(s)`, and 1 otherwise.

*Proof of 3.*
- If `n_Y = 0`, part 1 gives `a_Y = 0`, and part 2 gives one orbit over each level-3 splitting.
- Their images in `H_1(M_3)` are the 45 distinct frame-3 classes, so their images in `H_1(M_Y)` are
  distinct too.
- The inclusion `M_Y -> M_3` sends the class over `s` to the class over `s`. So `W(G_Y) <= W(Gamma(3))`.
- `M_Y` is normal of index 3 in `M_3`. The transfer `H_1(M_3) -> H_1(M_Y)` sends `[t]` to
  `sum_(g in M_3 / M_Y) [g t g^-1] = 3[t]`, because the three conjugates lie in one `M_Y`-orbit.
- Applying the transfer to `sum_s w_s [t_s] = 0` gives `3w in W(G_Y)`. QED.

**Values of `n_Y`** (`orbits.py`, checked by `sum_Y n_Y = 45 * (|off(s)| - 1) = 45 * 80`).
`n_Y = 3, 2, 1` on the classes of sizes `480, 540, 1080` with characteristic polynomials `x^4`,
`x^4 + 2x^2 + 1` and `x^4 + x^2 + 1`. These are indices 2, 4 and 6 in `orbits.json`. On the other 13
classes `n_Y = 0`.

**Corollary A'.** `b_1(M_9) = 24 + sum_(Y != 0) a_Y <= 24 + 480*3 + 540*2 + 1080*1 = 3624`. Only
`G_Y` from the three classes 2, 4 and 6 can carry a real Torelli character of `M_9` that is not
restricted from `M_3`. On the 13 classes with `n_Y = 0`, the real characters are frozen. Any drop of
`d(G_Y)` below `1/15` there comes from torsion characters, and `W(Gamma(3))/W(G_Y)` is an
`F_3`-vector space.

## Step 3. Exactness from a single 3-adic modulus

Write `H = H_1(M_Y; Z)`, `phi : Z^classes -> H`, `w -> sum_c w_c v_c`, so `W(G_Y) = ker phi`. For
`q = 3^m` put `L_m = phi^(-1)(q H)`. Then `L_m >= W(G_Y) + q Z^classes`. Let `c_m` be the number of
invariant factors equal to `q` in `H (x) Z/q + (Z/q)^2` (the extra `(Z/q)^2` is `d_1(C_1)`, see Step 4).
- *Facts used.* `cor : H -> H_1(M_3)` is the map induced by inclusion, and `res` is the transfer. Then
  `res o cor = N = 1 + t + t^2`, where `t` is conjugation by a lift `iota` of a generator of `M_3/M_Y`.
- `H_1(M_3)` is torsion-free (frame-3 census), so `W(Gamma(3))` is saturated.
- `b_1(M_Y) >= 24`, because `cor` is rationally onto (`cor o res = 3`).
- So `c_m = b_1 + 2 + #(summands of the 3-torsion of H of order >= q)`. Hence `c_m = 26` gives
  `b_1(M_Y) = 24` (`a_Y = 0`), and the 3-torsion of `H` has exponent `<= 3^(m-1)`.

**Lemma B (`n_Y = 0`, exact).** If `n_Y = 0` and `c_m = 26`, then `W(G_Y) = W(Gamma(3)) cap L_m`, with the
classes indexed by level-3 splittings as in Lemma A.3.

*Proof.*
- `<=`: this is Lemma A.3 together with `W <= L_m`.
- `>=`: take `w` in both, and put `x = phi(w)`, so `x` lies in `qH` and `cor(x) = 0`.
- Each `v_c` is `t`-invariant: `iota t_c iota^-1` is a twist over the same level-3 splitting, and for
  `n_Y = 0` there is only one `M_Y`-class over it. So `3x = N x = res(cor x) = 0`.
- Write `x = q y`. Then `3 q y = 0`, so `y` is 3-power torsion, and `x = q y = 0` because the exponent
  is `<= q/3`. QED.

**Lemma C (`n_Y > 0`, exact at 3).** Let `W_(3) = {w : k w in W(G_Y) for some k prime to 3}`. Let
`push : Z^classes -> Z^45` sum the classes above each level-3 splitting. If `c_m = 26`, then
`W_(3) = push^(-1)(W(Gamma(3))) cap L_m`.

*Proof.*
- `<=`: if `k w in W`, then `k push(w) in W(Gamma(3))`, which is saturated. Also `k phi(w) = 0`, so
  `phi(w)` is prime-to-3 torsion and lies in `qH`.
- `>=`: `x = phi(w)` lies in `qH` and `ker cor`. Since `a_Y = 0`, `cor (x) Q` is an isomorphism, so `x` is
  torsion. Write `x = q y` with `y` torsion. The 3-primary part of `x` is `q` times that of `y`, which is
  `0`. So `x` has order prime to 3. QED.
- *Consequences.* `d(G_Y) <= d(W_(3))`. The 3-adic valuation of `gcd aug` is the same for `W` and `W_(3)`.
  An `l1`-optimal certificate of `W_(3)` is a certificate for `G_Y` after multiplication by an unknown
  `k` prime to 3. Only prime-to-3 torsion in the `chi`-part of `H` can separate `W` from `W_(3)`.

**Lemma C' (collapse).** Assume `c_m = 26`. Let `c, c'` be classes over the same level-3 splitting with
`v_c - v_c' in qH`. Then `e_c - e_c' in W_(3)`.

*Proof.* `x = v_c - v_c'` lies in `ker cor`, so it is torsion because `a_Y = 0`. It also lies in `qH`, so,
as in Lemma C, it has order prime to 3. QED.

So if every class above each split splitting has the same image in `H (x) Z/q`, then `W_(3)` is the
pull-back of the lattice on the 45 merged classes. `d(W_(3))` is then the value on the merged classes:
`Ann(W_(3))` forces equal coordinates on merged classes.

## Step 4. The computation (`equivariant.py`, `local.py`, `lelim.c`)

- *Cover.* `M` has a finite presentation, the one used by the frame-3 census. The 77760 cosets of
  `M_Y<iota>` in `M/<iota>` form a free `Z/3`-cover of the 25920 cosets of `M_3<iota>/<iota>`, which
  are indexed by `PSp_4(F_3)`. The sheet labels come from `chi_Y` (`threeadic.py`, `equivariant.py`).
  `test_quotient.py` checks the coset tables.
- *Chains.* The cellular chains of the presentation complex of `M_Y` are free over `R = Z[t]/(t^3 - 1)`:
  103681 generators and 311040 relators (Fox calculus). Put `Q = C_1 / d_2 C_2`. Then
  `Q = H + d_1(C_1)`, and `d_1(C_1)` is the augmentation ideal of the free module on cosets, which is free
  of rank 2 for `Y != 0`. So `Q (x) Z/q = H (x) Z/q + (Z/q)^2`, with no Tor term.
- *Twist loops.* One loop per orbit of the stabilizer `<a_1, a_2, a_4, a_5>` on cosets, pushed to `C_1`
  along a spanning tree. For `n_Y = 0` the loops are grouped into classes by the level-3 splitting of the
  lifted coset representative; this is the frame-3 grouping (`compare.split_key`). For `n_Y > 0` they are
  grouped by splitting and by the image in `Q (x) Z/q`. The check that the group count is `45 + 2 n_Y`
  (Lemma A.2) guards against merges.
- *Local elimination.* `Lam = (Z/3^m)[t]/(t^3 - 1)` is a local ring whose units are the elements with
  augmentation prime to 3. `lelim.c` eliminates through unit entries. Each step takes a shortest row with
  a unit, and the unit whose column is shortest. Every step is an isomorphism of `Q (x) Z/q` that carries
  the twist vectors along. The reduced system is expanded over `Z` (3 columns per `Lam`-column) together
  with `q I`, and put in HNF. Then `c_m`, `L_m`, and the intersections of Lemmas B and C are HNF
  computations (`local.intersect_rowspaces`). `d` and the `l1`-optimal certificate come from the MILPs
  of the frame-3 census (`census.distance_milp`, `census.best_certificate`).
- *Tests.* `lelim.c` was checked against the Python elimination and against no elimination on 30 random
  systems over `Lam`, with `q = 27`: invariants and relation lattices agree. `local.py flat0` sets all sheet labels to 0, so the
  cover is 3 copies of the base. It returns `c_m = 72 = 3 * 24` with no smaller invariants, as the
  frame-3 value `H_1(M_3) = Z^24` predicts (`local-orbit-flat0.json`).
- *Built-in checks.* The transfer images `3 W(Gamma(3))` (for `n_Y = 0`) and `tr W(Gamma(3))` (for
  `n_Y > 0`) must lie in `L_m`. They do in every run below.

## Step 5. Results (`q = 81`, `summarize.py`, `first-layer-results.json`)

In each of the 16 runs, the 103681 `Lam`-generators reduce to 24, and the checks below hold.

| orbit (`n_Y`) | size | `c_m` | smaller inv. | groups | `rank W` | `gcd aug` | cert `l1` | `d` |
|---|---|---|---|---|---|---|---|---|
| 13 classes (`n_Y = 0`) | 80 ... 8640 | 26 | none | 45 | 21 | 5 | 5 | 1/15 |
| 6 (`n_Y = 1`) | 1080 | 26 | none | 45 of 47 | 21 | 5 | 5 | 1/15 (3-local) |
| 4 (`n_Y = 2`) | 540 | 26 | none | 45 of 49 | 21 | 5 | 5 | 1/15 (3-local) |
| 2 (`n_Y = 3`) | 480 | 26 | none | 45 of 51 | 21 | 5 | 5 | 1/15 (3-local) |

- *All `Y`.* `c_m = 26`, so `a_Y = 0` and `b_1(M_Y) = 24` (Step 3). By Shapiro,
  `b_1(M_9) = 24 + sum_(Y != 0) a_Y = 24`.
- *`n_Y = 0`.* The following hold on all 13 classes:
  - the loop groups are the 45 splittings, and the loops in each group have equal vectors;
  - `3 W(Gamma(3)) <= L_m` (the transfer check);
  - `W(Gamma(3)) <= L_m`.
  So Lemma B gives `W(G_Y) = W(Gamma(3))`, with elementary divisors of the index empty.
- *`n_Y > 0`.* All loops over one level-3 splitting have the same vector in `Q (x) Z/81`. The 102, 98 and
  94 stabilizer orbits fall into 45 groups, although Lemma A.2 gives `45 + 2 n_Y` true classes. So
  Lemma C' collapses the classes, and Lemma C gives `W_(3)` as the pull-back of
  `W(Gamma(3)) cap L_m = W(Gamma(3))`.
- *Sanity.* `local.py flat0` gives `c_m = 72`.

**Conclusion.**
- Parts 1 and 2 of the target hold exactly.
- Part 3 holds at the prime 3.
- `d(G_Y) = 1/15` on the 13 classes with `n_Y = 0`, and `d(G_Y) <= 1/15` with `3 not | gcd aug` on the
  other 3.
