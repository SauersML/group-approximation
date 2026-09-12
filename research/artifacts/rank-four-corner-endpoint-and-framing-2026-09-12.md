# Rank-four Plan 1: the corner endpoint, check (iii), and the framing inputs

Lane `w4-r4-corner` (family R4), 2026-09-12. This note checks the endpoint and the framing of Plan 1 in
`research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md`. Plan 1 is the claim
`rank-four-isometry-relations-give-corner-cuntz-family` with route
`leavitt-el3-triviality-via-rank-four-cuntz-family`. My scope is open check (iii), the Khanh--Thanh
input, the passage from approximate models to exact relations, and what the no-rank-model endpoint
quantifies over. Checks (i) and (ii) belong to `w4-r4-orth` and `w4-r4-complete`.

## 0. Summary

1. **Three relations reach the contradiction, not five** (Theorem 1). In a corner `eMe` of a rank
   ultraproduct, `T_0 S_0 = e` forces `S_0 T_0 = e`. So any `S_1` in `eM` with `T_0 S_1 = 0` is zero, and
   `T_1 S_1 = e` then gives `e = 0`. The rest of Plan 1's family is never used:
   - the completeness relation `S_0 T_0 + S_1 T_1 = e` (check (ii));
   - the second off-diagonal relation `T_1 S_0 = 0`;
   - the equality `rk(e) = rk(D)`.
2. **Plan 1's conclusion cannot hold in `M` at all.** No nonzero corner of a rank ultraproduct holds
   such a triple. So, model by model, `rank-four-isometry-relations-give-corner-cuntz-family` is
   equivalent to `D = 0`. It restates the gate as a proof by contradiction; it does not split the gate
   into easier pieces. Proving checks (i)--(iii) *is* proving the gate.
3. **Check (iii) asks only for `e != 0`, and positivity is free** (Lemma 3, Corollary 4).
   - A model with `D != 0` is nontrivial.
   - A nontrivial model of `EL_4(R)` moves every unit root element, and for simple `R` every
     `x_IJ(r)` with `r != 0`.
   - So any idempotent that absorbs `D`, or a nonzero root operator, on one side has positive rank.
4. **The literal equality `rk(e) = rk(D)` is neither needed nor generally true** (Proposition 2). A
   corner containing `D` on both sides has rank at least `2 rk(D) - rk(D^2)`, and that bound is
   attained. Equality with `rk(D)` is possible only when `rk(D^2) = rk(D)`.
5. **Framing (Section 3).**
   - `R^x ~= GL_4(R) = EL_4(R)` is on main as an internal Lean theorem (`glAll_eq_elementary`,
     binary case, every field), together with the prefix-code ring isomorphism. Khanh--Thanh,
     arXiv:2607.10351v1, states the same identification, unrefereed, and nothing depends on it.
   - A given `EL_3` model is **not** the `EL_3` block of its `EL_4` transport. The route survives
     anyway, because the gate quantifies over all models and Lemma 3 carries triviality from the
     block to all of `EL_4(R)`.

## 1. The corner endpoint

**Setting.**
- `k` is any field and `M = prod_omega M_(n_i)(k) / d_omega` is a rank ultraproduct.
- `rk([x_i]) = lim_omega rank(x_i)/n_i`.
- `d_omega` is the ideal of rank-null sequences, so `rk` is faithful on `M`: `rk(x) = 0` iff `x = 0`.

**Theorem 1.** Let `e` be an idempotent of `M`, and let `S_0, T_0` lie in `eMe` with `T_0 S_0 = e`.
1. `S_0 T_0 = e`.
2. Every `S` in `eM` (so `eS = S`) with `T_0 S = 0` is zero.
3. If `S_1` in `eM` and `T_1` in `M` satisfy `T_0 S_1 = 0` and `T_1 S_1 = e`, then `e = 0`.

*Proof.* For square matrices, `rank(1 - AB) = rank(1 - BA)`, since `v -> Bv` maps `ker(1 - AB)`
bijectively onto `ker(1 - BA)`. The identity holds at every level `i`, so `rk(1 - ab) = rk(1 - ba)` in
`M`. This is Arzhantseva--Paunescu, arXiv:1212.6780, Proposition 2.8, as used in
`leavitt-algebra-has-no-unital-rank-model-proof`.

Put `a = S_0 + (1 - e)` and `b = T_0 + (1 - e)`. Since `S_0 = eS_0 = S_0 e` and `T_0 = eT_0 = T_0 e`,
the cross terms `T_0 (1 - e)` and `(1 - e) S_0` vanish, and so do `S_0 (1 - e)` and `(1 - e) T_0`.
Hence

```text
b a = T_0 S_0 + (1 - e) = 1,        a b = S_0 T_0 + (1 - e).
```

So `rk(e - S_0 T_0) = rk(1 - ab) = rk(1 - ba) = 0`, and `S_0 T_0 = e` by faithfulness.

If `S` is in `eM` with `T_0 S = 0`, then `S = eS = S_0 T_0 S = 0`. With `S = S_1` this gives
`e = T_1 S_1 = 0`. ∎

**Remarks.**
- The proof works over any field, in any characteristic. It needs no algebra homomorphism, no
  simplicity of `R`, and no renormalization of `eMe` as a rank ultraproduct. (The plan cites
  "Fitting decomposition and idempotent lifting" for the last; it is not needed.)
- **Endpoint of Plan 1.** For `e != 0` there is no order-two Leavitt family in `eMe`. There is not even
  the triple `T_0 S_0 = e`, `T_0 S_1 = 0`, `T_1 S_1 = e` with `S_0, T_0` in `eMe` and `S_1` in `eM`.
  Indeed a nonzero `S_1` in `eM` killed by `T_0` is already impossible.
- **The route's `D = 0` branch, for every finite `K`.** A unital ring homomorphism
  `C : L_K(1,2) -> p_1 M p_1` gives the triple `(C(s_0), C(t_0), C(s_1), C(t_1))` with `e = p_1`, so
  `p_1 = 0`. The endpoint `leavitt-algebra-has-no-unital-rank-model` is stated only for
  `L_(F_2)(1,2)`; its proof is characteristic-free, and Theorem 1 covers every `K` directly.
- **What checks (i) and (ii) must deliver.** From `D != 0`: an idempotent `e != 0`, elements `S_0, T_0`
  in `eMe` with `T_0 S_0 = e`, and a nonzero `S_1` in `eM` with `T_0 S_1 = 0`. For instance `T_1 S_1 = e`
  certifies `S_1 != 0`. Check (ii), completeness, is never used.
- **Consequence for the family.** The configuration is impossible in every rank ultraproduct. So any
  derivation of the three relations from `D != 0` is a proof of `D = 0` by contradiction, and there is
  no weaker intermediate statement to verify separately. A candidate construction can be tested only
  on exact objects where the Leavitt coefficients act. The tautological model
  `EL_4(R) <= GL_4(R)` (not a rank model) has `D = E_23 E_12 = 0` there, so it tests the formulas but
  not the `D != 0` branch.

## 2. Check (iii): the rank of the corner

**What the route needs.** Only `e != 0`, equivalently `rk(e) > 0`, and Theorem 1 then contradicts. For
`e = 0` every relation holds trivially in `0M0 = 0`, so positivity is the whole of check (iii).

**Lemma 3 (normal closure).** Let `R` be any unital ring, `G` any group, and
`sigma : EL_4(R) -> G` a homomorphism.
1. If `sigma(x_IJ(1)) = 1` for one pair `I != J`, then `sigma` is trivial.
2. If `R` is simple and `sigma(x_IJ(r)) = 1` for one pair `I != J` and one `r != 0`, then `sigma` is
   trivial.

*Proof.* Let `N` be the normal closure of the given root element. If `a` is in `N`, then so are `[a, g]`
and `[g, a]` for every `g`. Use `[x_ab(r), x_bc(s)] = x_ac(rs)` for distinct `a, b, c`, and call the
other two indices `K` and `L`.

Part 1, starting from `x_IJ(1)`:

```text
x_IK(r) = [x_IJ(1), x_JK(r)]      x_IL(r) = [x_IJ(1), x_JL(r)]
x_KJ(r) = [x_KI(r), x_IJ(1)]      x_LJ(r) = [x_LI(r), x_IJ(1)]
x_IJ(r) = [x_IK(r), x_KJ(1)]
x_KL(r) = [x_KJ(r), x_JL(1)]      x_LK(r) = [x_LJ(r), x_JK(1)]
x_KI(r) = [x_KL(r), x_LI(1)]      x_LI(r) = [x_LK(r), x_KI(1)]
x_JI(r) = [x_JK(1), x_KI(r)]
x_JK(r) = [x_JI(r), x_IK(1)]      x_JL(r) = [x_JI(r), x_IL(1)]
```

In each line the argument drawn from `N` comes from an earlier line. So `N` contains all twelve root
subgroups, hence all of `EL_4(R)`.

Part 2: `x_IK(rb) = [x_IJ(r), x_JK(b)]` and `x_LK(arb) = [x_LI(a), x_IK(rb)]` are in `N`. Choose
`sum_m a_m r b_m = 1` (possible because `R` is simple); then `x_LK(1) = prod_m x_LK(a_m r b_m)` is in `N`,
and Part 1 applies. ∎

**Corollary 4 (positivity is free).** Let `sigma : EL_4(R) -> M^x` and put `n_IJ(a) = sigma(x_IJ(a)) - 1`.
If the `EL_3`-block defect `D = n_23(1) n_12(1)` is nonzero, then:
- `sigma` is nontrivial;
- `n_IJ(1) != 0` for every pair, and `n_IJ(r) != 0` for every `r != 0` when `R` is simple (Leavitt
  algebras are simple);
- any idempotent `e` with `e X = X` or `X e = X`, for some nonzero `X` (such as `D` or a root operator),
  has `rk(e) >= rk(X) > 0`, because `rk(eX) <= rk(e)`.

The plan's `e`, "the range projection of the `x_14` data", has positive rank as soon as it absorbs
one `n_14(a)` with `a != 0` on one side. Check (iii) holds for any `e` built as a one-sided support of
a root operator or of `D`. What checks (i) and (ii) must supply is that `S_0, T_0` live in `eMe` for that
same `e`.

**Proposition 2 (least two-sided corner containing an element).** For `D` in `M`,

```text
min { rk(e) : e = e^2 in M,  e D e = D }  =  2 rk(D) - rk(D^2).
```

*Proof at matrix level.* Let `V = range D` and `W = ker D`.
- `eD = D` iff `V <= range e`, and `De = D` iff `ker e <= W`.
- Since `V <= range e` and `range e ∩ ker e = 0`, we get `ker e ∩ (V ∩ W) = 0`. So
  `ker e ⊕ (V ∩ W) <= W`.
- Hence `rank e >= rank D + dim(V ∩ W) = 2 rank D - rank D^2`, using `dim(V ∩ W) = dim V - dim D(V)`.
- **Attained:** take `ker e = W'`, a complement of `V ∩ W` in `W`. Then `V ∩ W' = 0`, so `V` extends to a
  complement `U` of `W'`, and `e` is the projection onto `U` along `W'`.

*In `M`.* Lift `e` to idempotents `e_i`, by idempotent lifting in rank ultraproducts as used in
`matrix-unit-rank-models-extract-ring-rank-models`. Lift `D` to `D_i = e_i d_i e_i`, apply the matrix
bound at each level, and take the `omega`-limit. For the upper bound, choose a per-level minimizer
for any lift of `D`. ∎

**Consequence.** Read literally, check (iii) says `rk(e) = rk(D)` for a corner containing `D`. That is
possible only when `rk(D^2) = rk(D)`, and it fails whenever `D^2` has smaller rank; if `D^2 = 0` the
least corner rank is `2 rk(D)`. The route needs neither the equality nor any support of `D`: replace
(iii) by `e != 0`, which Corollary 4 supplies.
