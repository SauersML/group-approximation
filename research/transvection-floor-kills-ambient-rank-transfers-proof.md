---
rg: 2
id: transvection-floor-kills-ambient-rank-transfers-proof
kind: route
title: Count root-subgroup isotypic multiplicities through the two opposite maximal unipotent radicals, then feed a transvection defect to the infinite cyclic group
target: transvection-floor-kills-ambient-rank-transfers
requires: [root-splits-into-large-and-fixed-characteristic-witnesses]
artifacts: [experiments/transvection-floor-2026-09-17/transvection_floor_check.py, experiments/transvection-floor-2026-09-17/transvection_floor_check.out]
---

Ranks do not change under field extension, so we may assume `K` algebraically closed of characteristic `!= p`.
Every representation of a finite `p`-group over `K` is then semisimple and splits into characters. Fix a nontrivial
additive character `eps : (F_q, +) -> K^*`; its kernel is an additive subgroup `ker eps` of index `p`. Characters of
`F_q^k` are `chi_b(a) = eps(a . b)` for `b` in `F_q^k`. Let `G = SL_n(F_q)`, `n >= 3`, and
`psi : G -> GL(V)`, `N = dim V`, `N_0 = dim V^G`. `E_ij` are matrix units.

## 1. Two opposite radicals

- `A = {1 + sum_(j >= 2) a_j E_1j}` and `B = {1 + sum_(j >= 2) a_j E_j1}`, both isomorphic to `F_q^(n-1)`.
- **They generate `G`.** `A` contains every root subgroup `U_1j`, `B` every `U_j1`. For distinct `i, j >= 2`,
  `[1 + a E_i1, 1 + b E_1j] = 1 + ab E_ij`. So `<A, B>` contains all root subgroups, which generate `SL_n(F_q)`.
  Hence `V^A ∩ V^B = V^G`, and `dim V^A + dim V^B <= N + N_0`.
- **Transitivity.** `L = {diag(det(h)^(-1), h) : h in GL_(n-1)(F_q)}` lies in `G` and normalizes `A`, acting on the
  row vector `a` by `a -> det(h)^(-1) a h^(-1)`. Already `SL_(n-1)(F_q)` (here `n - 1 >= 2`) is transitive on nonzero
  rows. So `L` permutes the nontrivial characters of `A` transitively, and all of them occur in `V|_A` with one
  common multiplicity `M_A`. With `M_0^A = dim V^A`:
  `N = M_0^A + (q^(n-1) - 1) M_A`.
  The same `L` acts on the column vectors of `B` by `a -> det(h) h a`, again transitively, giving `M_0^B`, `M_B`.

## 2. The root subgroup `U = U_12`

- A character `chi_b` of `A` restricts trivially to `U_12 = {1 + a E_12}` iff `b_2 = 0`. That leaves `q^(n-2) - 1`
  nontrivial characters of `A`. So
  `dim V^(U_12) = M_0^A + (q^(n-2) - 1) M_A = M_0^A + s (N - M_0^A)`, with `s = (q^(n-2) - 1)/(q^(n-1) - 1) <= 1/q`.
- Likewise `dim V^(U_21) = M_0^B + s (N - M_0^B)`.
- `U_12` and `U_21` are conjugate in `G` by `w = [[0, 1], [-1, 0]] (+) 1_(n-2)`, so the two dimensions agree. The map
  `x -> x + s(N - x)` is strictly increasing (`s < 1`). Hence `M_0^A = M_0^B =: M_0`, and
  `2 M_0 <= N + N_0`.
- Therefore `N - dim V^U = (1 - s)(N - M_0) >= (1 - 1/q)(N - N_0)/2`.

## 3. One transvection

- `T = {diag(c, 1, c^(-1), 1, ..., 1)}` lies in `G` (here `n >= 3`) and conjugates `1 + a E_12` to `1 + ca E_12`. So
  the nontrivial characters of `U` occur in `V|_U` with a common multiplicity `m`, and
  `(q - 1) m = N - dim V^U`.
- The characters of `U` are `chi_beta(1 + a E_12) = eps(a beta)`, `beta` in `F_q`. For `a != 0`, `t_a = 1 + a E_12`
  acts on the `chi_beta`-isotypic part by the scalar `eps(a beta)`. This is `1` iff `a beta` lies in `ker eps`, which
  happens for exactly `q/p - 1` nonzero `beta`. So
  `dim V^(t_a) = dim V^U + (q/p - 1) m`, and
  `N - dim V^(t_a) = (N - dim V^U) (q - q/p)/(q - 1) >= (1 - 1/p)(N - dim V^U)`,
  because `(q - q/p) - (1 - 1/p)(q - 1) = 1 - 1/p >= 0`.
- `rank(psi(t) - 1) = N - dim V^t`. Combining with §2:
  `rank(psi(t_a) - 1) >= (1 - 1/p)(1 - 1/q)(N - N_0)/2`.
- Every transvection `t = 1 + v f` (`v != 0`, `f != 0`, `f(v) = 0`) is conjugate in `G` to `t_1`.
  - `GL_n(F_q)` is transitive on such pairs `(v, f)`, so some `g` has `g e_1 = v` and `f o g = e_2^*`. Then
    `g^(-1) t g = 1 + e_1 e_2^* = t_1`.
  - Replace `g` by `g diag(1, 1, det(g)^(-1), 1, ..., 1)` (here `n >= 3`). This keeps `g e_1 = v` and `f o g = e_2^*`
    and makes `det g = 1`.
- Finally, `V^G` is fixed by every `psi(y)`, so `rank(psi(y) - 1) <= N - N_0`. This proves Theorem 1.
- *Subgroups.* For `S <= Q` with `S ≅ SL_m(F_q)`, `m >= 3`, restrict `psi` to `S`; `V^Q <= V^S` changes nothing in
  the argument. ∎

**Constant.** `(1 - 1/p)(1 - 1/q)/2` is smallest at `p = q = 2`, where it equals `1/8`.

## 4. Corollary 2

1. **The model.** Choose `y` in `SL_n(F_q)` with no eigenvalue `1`: the companion matrix of
   `x^n + a x + (-1)^n` with `a != -1 - (-1)^n` has determinant `1` and `f(1) != 0`. So `rank(y - 1) = n`. Let `t`
   be any transvection. On `W = {1, g, g^(-1)}` in `Z` put `phi(1) = 1`, `phi(g) = y`, `phi(g^(-1)) = y^(-1) t`.
   - The only products inside `W` with nontrivial factors are `g g^(-1)` and `g^(-1) g`. Their defects are
     `rank(t - 1) = 1` and `rank(y^(-1) t y - 1) = 1`.
   - Separation: `rank(y - 1) = n`, and `rank(y^(-1) t - 1) >= rank(y^(-1) - 1) - rank(t - 1) = n - 1`.
   - So `phi` is a `(W, 1/n)`-model with separation at least `1 - 1/n >= 1/4`.
2. **Transport.** For a representation `psi` of `GL_n(F_q)` (restrict to `SL_n`) or of `SL_n(F_q)`, in characteristic
   `!= p`, `psi o phi` has defect `mu_psi(t)` at `(g, g^(-1))` and separation `mu_psi(y)` at `g`. By Theorem 1,
   `mu_psi(t) >= mu_psi(y)/8`.
3. **Consequence.** A family `psi_n` that turned `(W, eps)`-models into models with defect `omega(eps)` and separation
   `>= c` would give `omega(1/n) >= c/8` for all `n >= 3` in the family, so it cannot have `omega(eps) -> 0`. ∎

## 5. Corollary 3

- Well-definedness means: `rank(x_i - 1)/n_i -> 0` along `omega` implies `mu_(psi_i)(x_i) -> 0` along `omega`.
- Since `n_i -> infinity`, any transvections `t_i` satisfy `rank(t_i - 1)/n_i = 1/n_i -> 0`. So
  `mu_(psi_i)(t_i) -> 0`.
- By Theorem 1, `sup_y mu_(psi_i)(y) <= 8 mu_(psi_i)(t_i) -> 0` for `omega`-most `i`. So every element of `Pi` maps to
  the identity. ∎

## 6. Where the approach class dies, and what survives

- **Killed.** Every transfer `phi -> psi o phi` in which `psi` is a representation, in characteristic `!= p`, of a
  group containing an `SL_3(F_q)` block `S` that contains a defect element of `phi` which is a transvection, together
  with a separated element of `S`. The ambient groups `GL_n(F_q)`, `SL_n(F_q)` are the extreme case (Corollary 2).
  The exact failing step is §3: the torus `T` spreads the defect transvection's isotypic mass over all `q - 1`
  nontrivial root characters, and §2 ties that mass to the whole nontrivial part of `V`.
- **Consistent with tame lifting.** A generated group of order prime to `p` contains no transvection.
- **Survives.**
  - Lifts that depend on the model and are not homomorphisms of any group containing such a block.
  - Rank-approximate representations. Theorem 1 uses exact isotypic decompositions of `A`, `B`, `U`, `T`. A
    rank-metric uniform stability theorem for `SL_n(F_q)` in characteristic `0`, with constants independent of `n`
    and `q`, would carry the floor over with an additive loss.

## 7. Verification

`experiments/transvection-floor-2026-09-17/transvection_floor_check.py` enumerates `SL_3(F_2)`, `SL_3(F_3)`,
`SL_4(F_2)`, `SL_3(F_4)`. For permutation modules `C[X]` (vectors, points, lines, flags, pairs) it computes
`rank(t - 1) = |X| - #cycles(t)`, `N_0 = #G-orbits`, `dim V^U = #U-orbits`, and `max_y rank(y - 1)`. It checks
`rank(t - 1) >= c(p, q)(N - N_0)`, `N - dim V^U >= (1 - 1/q)(N - N_0)/2`, and `max_y rank(y - 1) <= N - N_0`. Output is
in `transvection_floor_check.out`. These modules test the counting of §§2--3 on reducible representations with
invariant vectors. They are a sanity check, not a substitute for the proof.
