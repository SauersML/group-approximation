# The binary cyclic corner and Sylvester rank functions on simple group algebras

Lane `w4-binary-cyclic`, 2026-09-12. Supports `simple-group-rank-functions-are-augmentation-or-detecting`
and `binary-leavitt-units-carry-nonaugmentation-rank-function`, and records where the lift attempts on
`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` stop.

## 0. Setup and the permutation-module form

- `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, `pi : A -> R` the evaluation.
- The ternary family: `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`, with `t_1, t_2, t_3` dual.
- `g = s_2 t_1 + s_3 t_2 + s_1 t_3`, of order three, and `e = 1 + [g] + [g²]`.
- The target (open): `c e b = 1` for some `b, c` in `A`.

**Proposition 0.1 (permutation-module form).** Let `K` be a field, `Γ` a group, `H <= Γ` finite with
`|H|` invertible in `K`, and `e_H = |H|^(-1) Σ_(h in H) [h]`. The following are equivalent.
1. `c e_H b = 1` for some `b, c` in `K[Γ]`.
2. The free module `K[Γ]` is a direct summand of the right permutation module `K[H\Γ]`.
3. `K[H\Γ]` has a unimodular element: some `m` and a module map `φ : K[H\Γ] -> K[Γ]` with `φ(m) = 1`.

*Proof.* `e_H [x]` depends only on the coset `Hx`, and over a set of coset representatives these
elements have disjoint supports. So `Hx -> e_H [x]` is an isomorphism of right modules
`K[H\Γ] ≅ e_H K[Γ]`. A module map `e_H K[Γ] -> K[Γ]` is left multiplication by its value at `e_H`,
which lies in `K[Γ] e_H`. So (3) reads `c e_H b = 1` with `m = e_H b` and `φ = c e_H ·`, which is (1).
From (1), `1 -> e_H b` is a split injection with retraction `c e_H ·`, which is (2), and (2) gives (3).
QED

A single coset is never unimodular: `c e_H [x] = 1` would give `c e_H = [x^(-1)]`, which is not
invariant under right multiplication by `H`.

**Proposition 0.2 (monotonicity).** If `H <= H'` are finite of invertible order, then
`e_(H') = e_(H') e_H`, so `c e_(H') b = 1` gives `(c e_(H')) e_H b = 1`. Conjugate subgroups give
conjugate idempotents. Every nontrivial `H` contains an element `h` of prime order, and fullness of
`e_H` gives fullness of `e_(⟨h⟩)`. So among averaging corners of finite subgroups containing `g`, the
order-three target is the weakest.

## 1. Sylvester rank functions on group algebras

A *Sylvester matrix rank function* on a ring `S` assigns to every rectangular matrix a number
`rk >= 0` with `rk(0) = 0`, `rk(1) = 1`, `rk(XY) <= min(rk X, rk Y)`, `rk(diag(X, Y)) = rk X + rk Y`
and `rk([[X, Z], [0, Y]]) >= rk X + rk Y`. Standard consequences used below:
- `rk(X + Y) <= rk X + rk Y`, since `X + Y = [1 1] diag(X, Y) [1 1]^T`;
- `rk(uXv) = rk X` for invertible `u, v`;
- an `n x m` matrix has rank at most `min(n, m)`, since `X = I_n X = X I_m`;
- a matrix all of whose entries have rank `0` has rank `0` (it is a sum of single-entry matrices);
- for an idempotent `f`, `rk(f) + rk(1 - f) = 1`: `>=` by subadditivity, and `<=` because
  `diag(f, 1 - f) = [f; 1 - f] [f, 1 - f]` factors through a `1 x 2` matrix.

On `K[Γ]` the *augmentation rank* is `rk_ε(X) = rank_K(ε(X))`, with `ε` the augmentation.

**Theorem 1.1.** Let `K` be a field, `Γ` a group, and `rk` a Sylvester matrix rank function on `K[Γ]`.
1. `N_rk = {x in Γ : rk(1 - [x]) = 0}` is a normal subgroup of `Γ`.
2. Matrices with the same image over `K[Γ/N_rk]` have the same rank, so `rk` descends to a Sylvester
   matrix rank function on `K[Γ/N_rk]`.
3. If `N_rk = Γ`, then `rk = rk_ε`.
4. If `Γ` is simple, then either `rk = rk_ε`, or `rk(1 - [x]) > 0` for every `x != 1`.

*Proof.*
1. `1 - [xy] = (1 - [x]) + [x](1 - [y])`, so `rk(1 - [xy]) <= rk(1 - [x]) + rk(1 - [y])`. Also
   `1 - [x^(-1)] = -[x^(-1)](1 - [x])` and `1 - [y x y^(-1)] = [y](1 - [x])[y^(-1)]` have rank at most,
   respectively exactly, `rk(1 - [x])`.
2. The kernel of `K[Γ] -> K[Γ/N_rk]` is spanned by the elements `[y](1 - [n])` with `y in Γ` and
   `n in N_rk`. Each has rank at most `rk(1 - [n]) = 0`, so every kernel element and every matrix with
   kernel entries has rank `0`. Then `|rk X - rk X'| <= rk(X - X') = 0` for two lifts. The axioms pass to
   the quotient, because products, block sums and triangular blocks of lifts are lifts.
3. Then `K[Γ/N_rk] = K` and the quotient map is `ε`. Every matrix over a field is equivalent to
   `diag(I_r, 0)`, so the only Sylvester matrix rank function on `K` is the normalized rank.
4. `N_rk` is `1` or `Γ`. QED

**Remark 1.2 (every rank function is a rank model).** `I_rk = {x : rk(x) = 0}` is a two-sided ideal,
and `rk` descends to `K[Γ]/I_rk` with `rk(x) > 0` for `x != 0`. So `Γ -> (K[Γ]/I_rk)^x` is a rank model
as in `full-averaging-idempotent-kills-its-element-in-rank-models`, and that theorem covers every
Sylvester rank function. Directly: `c e_H b = 1` gives `rk(e_H) >= 1`, so `rk(1 - e_H) = 0`, and
`1 - [h] = (1 - [h])(1 - e_H)` has rank `0` for each `h in H`.

**Corollary 1.3 (the binary targets force a unique rank function).** `R^x` is simple
(`binary-leavitt-unit-group-is-simple`). If `c e_H b = 1` in `F_2[R^x]` for one nontrivial finite
subgroup `H` of odd order, then `rk_ε` is the only Sylvester matrix rank function on `F_2[R^x]`.
Equivalently, a single Sylvester matrix rank function on `F_2[R^x]` other than `rk_ε` refutes every
averaging corner in `F_2[R^x]` at once. This includes `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`
and `thompson-v-order-three-averaging-idempotent-is-full`, because a witness in `F_2[V]` is a witness
in `F_2[R^x]`.

*Proof.* Remark 1.2 gives `rk(1 - [h]) = 0` for `h in H \ {1}`, and Theorem 1.1(4) gives `rk = rk_ε`. QED

**Corollary 1.4 (support filter).** If `c e_H b = 1` with `b, c` supported in a subgroup `Γ` containing
`H`, of any ambient group, then `H` lies in the normal subgroup `⋂_rk N_rk` of `Γ`. So `H` maps
trivially to every quotient `Q` of `Γ` whose group algebra has a rank function detecting the image of
`H`. Examples:
- finite `Q`, with normalized rank on the regular representation (`rk(1 - [q]) = 1 - 1/ord(q)`);
- sofic `Q`, through permutation matrices (a permutation moving a fraction `d` of the points has
  `rk(P - 1) >= d/2`, and Hamming defects bound rank defects);
- `K`-linear sofic `Q`.

On a simple group such as `R^x` the only proper quotient is trivial, so Corollary 1.3 is the whole
content there. On proper supports the filter is live.
