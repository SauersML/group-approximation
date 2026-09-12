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

## 3. Framing inputs

### 3.1 The identification `R^x ~= EL_4(R)`: source and fidelity

**The input on main.** The claim `leavitt-gl-equals-el-and-perfect-unit-group` is ESTABLISHED through
Lean, in `GroupApproximation/KOne/AllRanksElementary.lean`:

```text
theorem glAll_eq_elementary (n : ℕ) (hn : 2 ≤ n)
    (M : (Matrix (Fin n) (Fin n) (BinaryLeavittAlgebra k))ˣ) :
    M ∈ elementaryGroup (Fin n) (BinaryLeavittAlgebra k)
```

- It holds for every field `k` and every `n >= 2`. The proof lifts the rank-two collapse
  `glTwo_eq_elementary_holds` (`KOne/RefineLoopDischarge.lean`) through the prefix-code
  equivalence `A ~= M_m(A)`.
- A textual scan at tip 47302b98 finds no `sorry` and no `axiom` line in `AllRanksElementary.lean`
  or `AllRanksElementaryCore.lean`. I did not rebuild them or audit their transitive imports.

**What the plan actually uses.**
- A prefix code with four leaves gives a ring isomorphism `Theta : M_4(R) -> R`. It restricts to
  `GL_4(R) ~= R^x`, and `GL_4(R) = EL_4(R)`. So there is a group isomorphism `phi_4 : EL_4(R) -> R^x`.
  This is an isomorphism, not an equality, and it depends on the chosen code.
- Likewise `phi_3 : EL_3(R) = GL_3(R) ~= R^x`.

**Khanh--Thanh.** Huynh Viet Khanh and Vo Hoang Thanh, *Matrix generators for the unit groups of
`L_K(1,d)`*, arXiv:2607.10351v1 (11 July 2026). The local copy is `tmp/lit-audit/khanh-thanh.pdf`; I
read only pages 1--2.
- They prove `LGL_d(K) = L_d^x` for every field `K` and `d >= 2`.
- They state that `L_d` is a purely infinite simple GE-ring, that `GL_n(L_d) = E_n(L_d) D_n(K)`, and
  that `(L_d^x)_ab ~= K_1(L_d) ~= K^x / (K^x)^(d-1)`.
- For `d = 2` they state `K_1(L) = 0` and `L^x = <1 + e a f*, 1 + f b e*>`.

This agrees with the plan's "`R^x = GL_n(R) = EL_n(R)`" for `d = 2`. I did not read their proof that
`GL_n = E_n D_n(K)`. The preprint is unrefereed, and nothing on main depends on it: the Lean theorem
is the load-bearing input.

**Scope.** The identification is for the binary case only. The target claim
`leavitt-el3-rank-models-over-finite-fields-are-trivial` covers `L_K(1,n)` for all `n >= 2`. The route
covers `n = 2`, which is all its payoff needs.

### 3.2 A given `EL_3` model is not the `EL_3` block of its `EL_4` transport

- **The transport.** The gate quantifies over `sigma : EL_3(R) -> M^x`. The honest `EL_4` reading of
  `sigma` is `sigma_4 = sigma ∘ phi_3^(-1) ∘ phi_4 : EL_4(R) -> M^x`.
- **Its block.** The upper-left `EL_3` block of `sigma_4` is `sigma ∘ psi`, where
  `psi = phi_3^(-1) phi_4 |_block` is a self-embedding of `EL_3(R)` that is not onto, since the block is
  a proper subgroup of `EL_4(R)`.
- **Its defect.** The block defect `D_4 = n_23(1) n_12(1)` of `sigma_4` is
  `(sigma(psi x_23(1)) - 1)(sigma(psi x_12(1)) - 1)`, not `sigma`'s own `N_23 N_12`.
- **No transport fixes the block.** `phi_3^(-1) phi_4` would have to be the identity on the block, which
  no isomorphism `EL_4(R) -> EL_3(R)` can be.

**Why the route survives.** Run the case split on `sigma_4`.
- If `D_4 = 0`, the matrix-unit claim and the extraction claim make the block `sigma ∘ psi` trivial;
  Theorem 1 excludes `p_1 != 0` for every `K`. Then `el4-model-trivial-on-one-unit-root-element-is-trivial`
  makes `sigma_4` trivial.
- If `D_4 != 0`, Plan 1 together with Theorem 1 gives a contradiction.

Either way `sigma_4` is trivial, so `sigma = sigma_4 ∘ phi_4^(-1) ∘ phi_3` is trivial.

The route's sentence "`EL_3(R)` is a subgroup of `R^x = EL_4(R)` ... so `sigma` is a rank model of `R^x`.
Put `D = N_23 N_12`" must therefore be read with `D` the block defect of `sigma_4`. Its `D = 0` bullet
("So `sigma` is trivial") needs the normal-closure claim. Plan 1's own claim is stated for
`sigma : R^x -> M^x` read as an `EL_4` model, with `D` the block defect, which is consistent.

### 3.3 From approximate models to exact relations

**Models and soficity.**
- `M^x` is the metric ultraproduct of the `GL_(n_i)(k)` under normalized rank distance: a unit of `M`
  lifts to invertible matrices up to rank-null error.
- Maps `G -> GL_(n_i)(k)` whose rank defects tend to 0 on every pair assemble into one homomorphism
  `G -> M^x`. Separation `rk(sigma(g) - 1) > 0` for `g != 1` is injectivity.
- `F`-linear soficity (Arzhantseva--Paunescu) is an injective homomorphism into such an `M^x` over `F`.
  So if every homomorphism `EL_3(R) -> M^x` is trivial over every field of characteristic `p`, the
  infinite group `R^x` is not `F`-linear sofic for any field `F` of characteristic `p`. That settles
  `non-linear-sofic-group`, which asks for one field.

**Exact in `M`.** Every group identity of `EL_4(R)` holds exactly:
- `x_IJ(a) x_IJ(b) = x_IJ(a+b)`;
- `[x_ab(r), x_bc(s)] = x_ac(rs)`;
- `[x_ab(r), x_cd(s)] = 1` for `b != c` and `a != d`;
- consequences such as `n_IJ(a+b) = n_IJ(a) + n_IJ(b) + n_IJ(a) n_IJ(b)`, and in characteristic `p`,
  `(1 + n_IJ(a))^p = 1`, hence `n_IJ(a)^p = 0`.

**Not available.**
- The operators `n_IJ` are neither additive nor multiplicative in the coefficient, and ring elements of
  `R` have no operators of their own.
- The Leavitt relations enter only as coefficients inside group identities, such as
  `[x_12(t_i), x_23(s_j)] = x_13(delta_ij)` with `x_13(0) = 1`.
- So a Leavitt family in `eMe` has to be assembled from group-element operators. That is exactly what
  checks (i) and (ii) must do.

### 3.4 What the no-rank-model endpoint quantifies over

- **The claim.** `leavitt-algebra-has-no-unital-rank-model` says there is no unital ring homomorphism
  `L_(F_2)(1,2) -> M` over any field (gk-vf-linear reads "F-algebra" as "ring"), and equivalently no
  unital rank-approximate homomorphisms. Its proof: `M` is directly finite, and `R` is simple and not
  directly finite. gk-vf-linear's scope remark adds that corners of `M` are directly finite.
- **The route uses more than it states.** It applies the claim in both branches to `L_K(1,2)` with `K`
  finite: to `C : R -> p_1 M p_1` when `D = 0`, and to a family in `eMe` when `D != 0`. For `K != F_2`
  the claim's literal statement does not apply, although its proof does.
  `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple` covers every `K` and every characteristic in
  both branches, with three relations and no homomorphism.
- **Not needed.** The plan's step "`eMe` is again a rank ultraproduct" (Theorem D) is true, by
  idempotent lifting, but nothing uses it.

## 4. Verdict table (w4-r4-corner)

| item | verdict |
|---|---|
| endpoint: a corner Leavitt family contradicts no-rank-model | correct, and sharper: three relations suffice; the configuration is impossible outright, so the plan claim is equivalent to `D = 0` model by model |
| check (ii), completeness | not needed |
| check (i) | only `T_0 S_0 = e`, `T_0 S_1 = 0`, and any certificate that `S_1 != 0` (for instance `T_1 S_1 = e`), with `S_0, T_0` in `eMe` and `S_1` in `eM` |
| check (iii), `rk(e) = rk(D)` | replace by `e != 0`; that is free for any `e` absorbing `D` or a nonzero root operator on one side; the literal equality is false in general (Proposition 2) |
| `R^x = EL_4(R)` | on main via Lean `glAll_eq_elementary` and the prefix-code isomorphism; an isomorphism that depends on the code; Khanh--Thanh arXiv:2607.10351v1 agrees, unrefereed, not load-bearing |
| an `EL_3` model read as an `EL_4` model | not literally, since the block is `sigma ∘ psi`; the route is valid by universal quantification plus the normal-closure claim |
| approximate to exact | group identities of `EL_4(R)` are exact in `M`; coefficient relations appear only inside commutators |
| payoff field scope | fields of characteristic `p`; enough to settle `non-linear-sofic-group` |

**Not done here.** Checks (i) and (ii) themselves. No construction of `e`, `S_i`, `T_i` has been written
down yet, so I had nothing to evaluate.

## 5. Addendum: positivity for w4-r4-orth's opposite-root placement

`w4-r4-orth` (fcffe16327; `index-three-corner-placement-holds-only-modulo-two-root-defects`) uses this
placement:

```text
S(b) = n_31(b) n_13(1)        T(a) = n_34(a) n_43(1)
e    = range idempotent of n_31(1) n_13(1)
```

This `e` absorbs `n_31(1) n_13(1)` on the left. That product is not a single root operator, so
Corollary 4 does not apply directly. Positivity needs `n_31(1) n_13(1) != 0`. In characteristic two
that holds for every nontrivial model.

**Proposition 5** (`opposite-unit-root-product-vanishes-only-for-trivial-models`). Let `R` and `M` be
unital rings with `2 = 0`, and `sigma : EL_4(R) -> M^x` a homomorphism. If `n_JI(1) n_IJ(1) = 0` for one
pair `I != J`, then `sigma` is trivial.

*Proof.* Take `(I, J) = (1, 3)`, and put `X = n_13(1)` and `Y = n_31(1)`.
1. **Squares.** `(1 + X)^2 = sigma(x_13(2)) = 1`, so `X^2 = 0`. Likewise `Y^2 = 0`.
2. **Braid relation.** Over `Z`, both `x_13(1) x_31(-1) x_13(1)` and `x_31(-1) x_13(1) x_31(-1)` have
   `(1,3)` block `[[0,1],[-1,0]]`. With `-1 = 1` in `R`, the braid relation
   `x_13(1) x_31(1) x_13(1) = x_31(1) x_13(1) x_31(1)` holds in `EL_4(R)`.
3. **Expansion.** Apply `sigma` and expand: `1 + Y + XY + YX + XYX = 1 + X + XY + YX + YXY`.
   So `Y + XYX = X + YXY`.
4. **Collapse.** If `YX = 0`, both cubic terms vanish, so `X = Y =: u - 1`, where `u = sigma(x_13(1))`.
5. **A root element dies.** `x_13(1)` commutes with `x_12(r)`, and `x_32(r) = [x_31(1), x_12(r)]`.
   So `sigma(x_32(r)) = [u, sigma(x_12(r))] = 1`.
6. **Conclusion.** By Lemma 3, `sigma` is trivial. ∎

**Consequence for the placement.**
- **Positivity.** In a characteristic-two rank model with `D != 0`, `sigma` is nontrivial, so
  `rk(e) >= rk(n_31(1) n_13(1)) > 0`. For this placement check (iii) holds unconditionally.
- **What stays open.** Whether `S(b)` and `T(a)` lie in `eMe` for this `e`, together with relation (i).
  That is the deviation terms `Delta_row` and `Delta_rev` of w4-r4-orth's identity, which is the gate
  itself.
- **Calibration.** In the honest model `n_31(1) n_13(1) = E_33`, and `e = E_33` is the index-three
  matrix unit.

**Scope.** Characteristic two only. In odd characteristic the braid relation relates `n_13(1)` to
`n_31(-1)`, and the vanishing of `n_31(1) n_13(1)` does not collapse the same way. The decisive
instance `K = F_2` is in characteristic two.

**Verifier note (w4-vf-gate, e4d7e1c7fa).** In odd `p`, the `D = 0` branch of the route uses the
matrix-unit claim, and that needs `N_12^2 = 0`. It comes from
`reversed-root-pair-identity-forces-root-squares-to-vanish`, which is now added to the route's
requires.
