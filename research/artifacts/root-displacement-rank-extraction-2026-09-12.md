# Rank extraction from root displacement, and where it stops

Lane `gk-rk-free` (family R), 2026-09-12. Supports the claims
`leavitt-rank-models-have-uniform-root-displacement` (Section 1) and
`dyadic-root-displacement-data-admit-trivial-plus-free-models` (Section 2), and the Attempts
entry on `leavitt-el3-rank-models-over-finite-fields-are-trivial` (Section 3).

## 0. The approach

The family's other lanes study the restriction of a rank model to `SL_3(F_2)` (ranges and
kernels, extensions and flags, composition factors), or free-like content and level-changing
units (the lead lane). This lane asks a different question: what do the **displacement ranks
of root elements** alone force? The hope was to extract a ring-theoretic rank function on
`R = L_(F_2)(1,2)` from a model, and to contradict the absence of Sylvester rank functions on
`R` (`R` is not directly finite).

Setting. `M = prod_omega M_(n_i)(k) / d_omega` is a rank ultraproduct over a field `k` of
characteristic two, with faithful Sylvester rank function `rk`. `sigma : EL_3(R) -> M^x` is a
homomorphism. `R^3` is the right `R`-module of column vectors, matrices act on the left, and
`x_ij(a) = 1 + a E_ij`. The Steinberg commutator is `[x_ij(a), x_jk(b)] = x_ik(ab)` for
distinct `i, j, k`, with `[g,h] = g h g^-1 h^-1`. Put

```text
rho_ij(a) = rk( sigma(x_ij(a)) - 1 ),     rho(a) = rho_12(a),     rho = rho(1).
```

## 1. Exact properties of the displacement function

**Theorem 1.** For every homomorphism `sigma : EL_3(R) -> M^x` as above:

1. **Weyl invariance.** `rho_ij(a) = rho(a)` for all `i != j` and all `a` in `R`.
2. **Unit invariance.** `rho(u a v) = rho(a)` for all units `u, v` of `R`.
3. **Square-zero bound.** `rho(a) <= 1/2`.
4. **Subadditivity and products.** `rho(a + b) <= rho(a) + rho(b)` and
   `rho(ab) <= 2 min(rho(a), rho(b))`.
5. **Uniformity.** `rho/4 <= rho(a) <= 2 rho` for every nonzero `a` in `R`.
6. **Simultaneous conjugacy of orthogonal root tuples.** Let `(e_1, ..., e_n)` and
   `(f_1, ..., f_n)` be two tuples of pairwise orthogonal nonzero idempotents of `R`, with
   arbitrary sums. Then some `g` in `EL_3(R)` satisfies `g x_12(e_i) g^-1 = x_12(f_i)` for every
   `i`. In particular `rho(e) = rho` for every nonzero idempotent `e`, and the restrictions of
   `sigma` to `<x_12(e_i)>` and `<x_12(f_i)>`, both elementary abelian of rank `n`, are
   conjugate in `M` generator by generator. So the restriction of `sigma` to the dyadic root
   group is exchangeable and invariant under merging disjoint generators.

Consequently `sigma` is nontrivial exactly when `rho > 0` (artifact
`el3-rank-ring-rigidity-2026-09-12.md`, Corollary 4, since root elements generate), and then
every nontrivial root element `x_ij(a)`, `a != 0`, is displaced by at least `rho/4`.

*Proof.*

1. The permutation matrices lie in `SL_3(F_2) = <x_ij(1)> <= EL_3(R)`. Conjugating `x_12(a)`
   by a permutation matrix gives `x_(pi 1, pi 2)(+-a) = x_(pi 1, pi 2)(a)`, since the
   characteristic is two. Conjugation is exact in `M` and preserves `rk`.
2. `diag(u, v, 1)` lies in `GL_3(R) = EL_3(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`),
   and `diag(u, v, 1) x_12(a) diag(u, v, 1)^-1 = x_12(u a v^-1)`.
3. `x_12(a)^2 = x_12(2a) = 1`, so `N = sigma(x_12(a)) - 1` satisfies `N^2 = 0` in `M`. At finite
   stages `rank(N_i) <= n_i - rank(N_i) + rank(N_i^2)` with `rank(N_i^2) = o(n_i)`, so
   `rk(N) <= 1/2`.
4. `x_12(a + b) = x_12(a) x_12(b)` gives `sigma(x_12(a+b)) - 1 = N_a + N_b + N_a N_b`, whose
   rank is at most `rk N_a + rk N_b`. For products, `[g,h] - 1 = (gh - hg) g^-1 h^-1` and
   `gh - hg = (g-1)(h-1) - (h-1)(g-1)`, so `rk([g,h] - 1) <= 2 min(rk(g-1), rk(h-1))`. With
   `x_13(ab) = [x_12(a), x_23(b)]` and part 1 this gives `rho(ab) <= 2 min(rho(a), rho(b))`.
5. Upper bound: `rho(a) = rho_13(a·1) <= 2 rho_23(1) = 2 rho`. Lower bound: by
   `binary-leavitt-algebra-is-purely-infinite-by-monomials`, every nonzero `a` has monomials
   `x, y` with `x a y = 1`. Then `x_13(1) = x_13(x·ay) = [x_12(x), x_23(ay)]` and
   `x_23(ay) = [x_21(a), x_13(y)]`, so `rho = rho_13(1) <= 2 rho_23(ay) <= 4 rho_21(a) = 4 rho(a)`.
6. Put `e = sum e_i` and `f = sum f_i`. Decompose

   ```text
   e_1 R = (+)_i e_1 e_i R  (+)  e_1 (1-e) R,     e_2 R = (+)_i e_2 e_i R  (+)  e_2 (1-e) R,
   B = e_1 (1-e) R  (+)  e_2 (1-e) R  (+)  e_3 R,
   ```

   so `R^3 = (+)_i (e_1 e_i R (+) e_2 e_i R) (+) B`, and similarly with `f` and `B'`. The operator
   `N_i = x_12(e_i) - 1` sends `e_2 e_i r` to `e_1 e_i r` and kills every other summand. The same
   holds for `N'_i = x_12(f_i) - 1`.
   * Every nonzero finitely generated projective right `R`-module is isomorphic to `R`
     (`binary-leavitt-nonzero-projectives-are-free`). So there are isomorphisms
     `phi_i : e_i R -> f_i R`, and `psi : B -> B'`; `B` and `B'` are nonzero since they contain
     `e_3 R`.
   * Define `g` by `e_1 e_i r -> e_1 phi_i(e_i r)`, `e_2 e_i r -> e_2 phi_i(e_i r)`, and `psi` on
     `B`. It is an automorphism of `R^3`, hence an element of `GL_3(R) = EL_3(R)`.
   * On `e_2 e_i r`: `g N_i (e_2 e_i r) = e_1 phi_i(e_i r)` and
     `N'_i g (e_2 e_i r) = e_1 f_i phi_i(e_i r) = e_1 phi_i(e_i r)`. On every other summand both
     sides vanish. So `g N_i g^-1 = N'_i` for all `i`.

   With `n = 1` and `f_1 = 1`, `x_12(e) ~ x_12(1)` for every nonzero idempotent `e`. QED

Relation to the corona row. `binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale` uses
the same sandwich `u a v = 1` in operator norm, through normal-generation counting. Theorem 1 is
the characteristic-two rank-ultraproduct version, with exact rank bounds on commutators and
simultaneous conjugacy of tuples.

Relation to the family's artifact. `el3-rank-ring-rigidity-2026-09-12.md` (lane
`gk-l-gate-neg`) has two related results. Proposition 12: `rho(a) = rho` for every nonzero `a`
in the locally matricial subalgebra `A_inf = union M_(2^k)(F_2)`, by Smith normal form and
Proposition 5. Section 4b: `x_12(1)` is a product of `2^k` commuting conjugates of itself. For
constancy on `A_inf`, cite those. What is new here:
* the bounds of part 5 for every nonzero `a` in `R`, off `A_inf`;
* unit invariance by arbitrary units;
* simultaneous conjugacy of arbitrary orthogonal idempotent tuples (part 6);
* the calibration of Section 2.

## 2. Calibration: displacement data admit trivial-plus-free models

Let `D_k <= EL_3(R)` be generated by `x_12(s_w t_w)`, `|w| = k`. Since
`s_w t_w = s_(w0) t_(w0) + s_(w1) t_(w1)`, `D_k <= D_(k+1)`, and `D = union D_k` is an increasing
union of elementary abelian groups `D_k ~= (Z/2)^(2^k)`. Its elements are the `x_12(e_S)` with
`e_S` a finite sum of level idempotents.

**Theorem 2.** For every `epsilon` in `[0,1]` there is a homomorphism
`tau_epsilon : D -> M^x`, into a rank ultraproduct over `F_2`, with these properties:

* every nontrivial element of `D` has displacement `rk(tau_epsilon(g) - 1) = epsilon/2`;
* for any two tuples of pairwise orthogonal nonzero dyadic idempotents of equal length, the
  restrictions of `tau_epsilon` to the generated subgroups are conjugate in `M`, generator by
  generator;
* `tau_epsilon` is injective when `epsilon > 0`.

Moreover the Boolean function `rho_B(a) = (epsilon/2)[a != 0]` on `R` satisfies parts 2 to 5
of Theorem 1.

*Proof.* Choose levels `k_i -> infinity` and put `V_i = F_2^(m_i) (+) F_2[D_(k_i)]^(r_i)` with
`m_i / dim V_i -> 1 - epsilon`. `D_(k_i)` acts trivially on the first summand and regularly on
the second. Extend by the identity off `D_(k_i)`.
* Every `g` in `D` lies in `D_(k_i)` for large `i`, so `tau_epsilon` is an exact homomorphism in
  the ultraproduct.
* A nontrivial `g` of order two acts freely on the regular module, so `rank(g - 1)` is half its
  dimension there and zero on the trivial summand. This gives displacement `epsilon/2`, and
  injectivity when `epsilon > 0`.
* For two tuples of `n` orthogonal nonzero dyadic idempotents at levels at most `k_i`, the
  generated subgroups `Q, Q'` are elementary abelian of rank `n`. The regular module of
  `D_(k_i)` restricts to free modules of the same dimension over `Q` and `Q'`. An isomorphism
  `Q -> Q'` matching generators is realized by a linear isomorphism between these free modules,
  and by the identity on the trivial part.
* The Boolean function is constant on nonzero elements, so subadditivity, the product bound
  `c <= 2c`, unit invariance and the bounds `c/4 <= c <= 2c` hold. QED

**Consequence.** Parts 3, 5 and 6 of Theorem 1, together with constant displacement on the
dyadic root group, are realized at every displacement value `rho` in `[0, 1/2]`. So no
argument that uses only displacement ranks of root elements, their exact inequalities, and the
restriction of `sigma` to `D` up to conjugacy can prove that `sigma` is trivial. None can
produce a Sylvester rank function on `R` either: the extracted function is Boolean, not
additive on orthogonal idempotents.

## 3. Where the extraction stops

* **The extracted function is Boolean.** Theorem 1 part 6 makes `rho` constant on nonzero
  idempotents. A Sylvester rank function would need
  `rho(e + f) = rho(e) + rho(f)` for orthogonal `e, f`. This fails whenever `rho > 0`, and it
  fails in the calibration models for the right reason: the images of `N_e` and `N_f` overlap.
* **Joint displacement does not help.** The rank of `Im N_(e_1) + ... + Im N_(e_n)` is a
  function of `n` alone by part 6. In the free calibration it equals `epsilon (1 - 2^-n)`,
  which is realized.
* **The displacement data do not see the gate identity.** By
  `el3-unit-root-matrix-units-iff-two-root-identities` (lane `gk-rk-unipotent`), in characteristic
  two the unit root elements act by matrix units exactly when `N_23 N_12 = 0`, with
  `N_ij = sigma(x_ij(1)) - 1`. After that the matrix-unit theorems kill the model. Theorem 1
  neither forces nor forbids that identity: the ranks it controls are those of `N_ij(a)` and of
  commutator displacements.
  * Over the locally matricial algebra `A_inf`, the natural block models have `N_23 N_12 = 0`.
  * The free models of `free-rank-models-on-sl3-admit-no-block-support` have
    `rk(N_23 N_12) > 0`.
  * Both have constant displacement on nonzero coefficients.

  So `rho` matters for the gate only through an argument that turns uniform displacement into a
  bound on `rk(N_23 N_12)`, and no such argument appears here.
* **What a proof must add.** Exact module data beyond ranks of root displacements: the product
  `N_23 N_12` itself, the interaction of root subgroups in different positions on the same
  corner (where the calibration group `D` is not defined), or Leavitt-specific units that change
  level (the lead lane's territory).

## 4. Heuristic note, not a claim: fixed points of corner copies

The lead lane suggested Hom and fixed-point constructions that turn free content into natural
content. The natural candidate is `Fix sigma(G_(1-e))` for the corner copy
`G_(1-e) = EL_3((1-e) R (1-e))`, which is a module for the commuting copy `G_e`. By compressor
conjugacy and fixed-ideal conservation
(`rank-ultraproduct-compressors-conserve-fixed-right-ideals`,
`leavitt-rank-models-kazhdan-fixed-ideals-are-global`), corner copies containing a Kazhdan
subgroup of the nine-leaf configuration fix only the global fixed ideal. After the global
fixed part is removed this module is zero, so the construction yields no new model. This
depends on which block identification contains the Kazhdan subgroup, and I have not checked
that. It is recorded as heuristic only.
