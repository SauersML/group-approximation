# Family R4 (rank-four gate): independent verification record

Lane `w4-vf-gate`, 2026-09-12. This lane verifies family R4:
- `w3-strategist-gate`'s plans (5b46fe59c5) and lead pass (322f1b031);
- the lanes `w4-r4-orth`, `w4-r4-complete`, `w4-r4-corner`, `w4-r4-adversary`, `w4-r4-approx`,
  `w4-heisenberg` and `w4-gate-descent`.

Each item is re-derived from the statements, the Steinberg relations and the Leavitt relations
`t_i s_j = delta_ij`, `s_0 t_0 + s_1 t_1 = 1`.

**Conventions.**
- `K` is a finite field of characteristic `p`, and `R = L_K(1,2)`.
- `M` is a rank ultraproduct over a field of characteristic `p`.
- `x_IJ(a) = 1 + a e_IJ`, and `[g,h] = g h g^-1 h^-1`.
- `n_IJ(a) = sigma(x_IJ(a)) - 1`, and `N_IJ = n_IJ(1)`.

## 1. Plan landings (5b46fe59c5) and the lead pass (322f1b031)

Nothing in 5b46fe59c5 is established. So this section checks inputs, scope and the endpoint.

### 1.1 The GL = EL input: PASS. It is internal, not a citation.

- **The node.** The input `leavitt-gl-equals-el-and-perfect-unit-group` is the Lean theorem
  `glAll_eq_elementary` (`GroupApproximation/KOne/AllRanksElementary.lean`).
- **Hypotheses.** It holds under `variable (k : Type) [Field k]` with `2 <= n`, and puts every unit of
  `M_n(L_k(1,2))` in `elementaryGroup`.
- **No sorry** in that file or in `AllRanksElementaryCore.lean` at tip 41a03cfe51.
- **Khanh--Thanh is not load-bearing.** w4-r4-corner Section 3 agrees.
- **Scope.** `R^x ~= GL_4(R)` comes from a module isomorphism `R ~= R^4` and depends on which prefix
  code is used.

### 1.2 Frames: CORRECTION, repairable forward

**The gap.** The route reads a model `sigma : EL_3(R) -> M^x` as a model of `EL_4(R)` and uses
`D = N_23 N_12` from `sigma`'s own root elements. No isomorphism `EL_4(R) -> EL_3(R)` restricts to the
identity on the block.

**Independent proof, for conjugation isomorphisms.**
1. Take `g |-> theta alpha(g) theta^-1`, where `theta : R^4 -> R^3` is a module isomorphism and `alpha`
   a ring automorphism.
2. Fixing `x_12(1)` and `x_23(1)` forces `theta e_12 = e_12 theta` and `theta e_23 = e_23 theta`.
3. Solving entrywise gives `theta = [[c,0,theta_13,theta_14],[0,c,0,0],[0,0,c,0]]`.
4. `theta` is bijective on the second coordinate, so `c` is a unit.
5. Then `(v_1, v_4) |-> c v_1 + theta_14 v_4` has nonzero kernel, which is a contradiction.

**Example of the transport.** `theta' = [[1,0,0,0],[0,s_0,0,s_1],[0,0,1,0]]`, with
`theta'^-1 = [[1,0,0],[0,t_0,0],[0,0,1],[0,t_1,0]]`, sends `x_12(1) |-> x_12(t_0)` and
`x_23(1) |-> x_23(s_0)`. So the block defect of the transported model is `n_23(s_0) n_12(t_0)` in
`sigma`'s frame. The isometry-coefficient data of `leavitt-isometry-commutators-constrain-el3-rank-models`
thus appears as a coefficient-one defect in another frame.

**Agreement.** This matches w4-r4-corner's Section 3.2 (6414c135d1), found independently.

**The repair.**
1. Run the case split on `sigma_4 = sigma o phi_3^-1 o phi_4`.
2. Kill its block, then all of `EL_4(R)`, by `el4-model-trivial-on-one-unit-root-element-is-trivial`
   (Section 2.2).
3. Hence `sigma` is trivial.

### 1.3 Odd characteristic: the conclusion holds, but for a different reason than the route gives

**What the route says.** Odd `p` "adds only the p-nilpotent bookkeeping for N_12^p = 0".

**Why that reason is wrong.**
- `el3-unit-root-matrix-units-iff-two-root-identities` (condition 3) needs `N_12^2 = 0` as well as
  `N_23 N_12 = 0`.
- `x_12(1)^p = 1` gives only `N_12^p = 0`.
- So the `p`-power bookkeeping is not the justification.

**What supplies it.** `N_12^2 = 0` does follow from `N_23 N_12 = 0` in every characteristic, by
`reversed-root-pair-identity-forces-root-squares-to-vanish` (w4-r4-adversary, 9fd9898e8e). I re-derived
it independently.
1. **Signed Weyl elements.** Put `w = x_ij(1) x_ji(-1) x_ij(1)`. These conjugate `x_ab(r)` to
   `x_(pi a)(pi b)(+-r)`, and `S_3` moves the triple `(1,2,3)` to every ordered triple.
2. **Signs do not matter.** `sigma(x_ab(-1)) - 1 = -N_ab (1 + N_ab)^-1`, and the unit commutes with
   `N_ab`. So a conjugate of `N_23 N_12` vanishes iff `N_jk N_ij` does. Hence `N_jk N_ij = 0` for all
   distinct `i, j, k`.
3. **The commutator.** With `X = 1 + N_ij` and `Y = 1 + N_jk`, the relation `[X, Y] = 1 + N_ik` gives
   `N_ik = (N_ij N_jk - N_jk N_ij) X^-1 Y^-1 = N_ij N_jk X^-1 Y^-1`.
4. **Absorption.** `N_jk N_ij = 0` gives `Y N_ij = N_ij`, so `Y^-1 N_ij = N_ij`.
5. **The square.** `N_ik^2 = N_ij N_jk X^-1 N_ij N_jk X^-1 Y^-1 = N_ij (N_jk N_ij) X^-1 N_jk X^-1 Y^-1 = 0`,
   since `X^-1` commutes with `N_ij`.
6. **Every root.** Every root `(i,k)` has a middle index `j`.
7. **Scope.** No characteristic and no rank structure is used.

**Consequence.** The route is valid in every characteristic. For odd `p` it should cite the
reversed-root-pair claim, not `N_12^p = 0`. My first reading here flagged odd `p` as missing an
identity. That was wrong, and I withdraw it before landing.

### 1.4 The endpoint: PASS. Three independent derivations agree.

**The claim.** Take `S_0, T_0` in `eMe` with `T_0 S_0 = e`, and one more relation, either `T_0 S_1 = 0`
or `T_1 S_0 = 0`, together with `T_1 S_1 = e`. Then `e = 0`. Completeness is never used.

**My derivation.**
1. Direct finiteness of the corner gives `S_0 T_0 = e`.
2. Then `e = S_0 (T_0 S_1) T_1 = 0`, or `T_1 = T_1 S_0 T_0 = 0`.

**The other two.** The lead's L1 pads by `1 - e`, and so does w4-r4-corner's Theorem 1 (Section 2.1).
Both are sound. No renormalization of `eMe` is needed.

### 1.5 The calibration a proof of (i) must pass

**Why the four Cohn relations must be used jointly.** Honest models over finitely represented
coefficient rings violate `N_23 N_12 = 0` (`fd-represented-coefficients-violate-two-root-identities`).
A derivation that skips some of the relations `t_i s_j = delta_ij` would also apply to one of those
models, and there it would build a corner family that Section 1.4 forbids. Concretely:
- one that uses only `t_0 s_0 = 1` also runs through the Toeplitz quotient onto `F_2`;
- one that uses only an off-diagonal relation also runs in `M_2(F_2)`, with `t_0 -> E_11` and
  `s_1 -> E_22`.

**What cannot be the only input.** The `EL_4` Steinberg relations, the cross frame included, hold over
every ring.

### 1.6 Plan 3 collapses to the target: PASS, agreeing with the lead and w4-r4-approx

**Why the right side is false.** An ultraproduct of the maps `phi` over the pairs `(F, eps)` is a unital
homomorphism `R -> M` with `rk(phi(x)) >= c` for `x != 0`, which Section 1.4 excludes for every `K`.
So the node is equivalent to "`R^x` is not `F_p`-linear sofic".

**The lead's finite-level bound, re-derived.**
1. `TS = 1 - E` with `rk E < eps n` gives `rk F >= (1 - 2 eps) n` for `F = ST`.
2. `F^2 - F = -SET` has rank `< eps n`.
3. `(1 - F)(im F)` lies in `im(SET)`.
4. So `rk(1 - ST) < 3 eps n`.

**The Forward attempt (5b46fe59c5) uses the wrong commutator.** `[x_12(a), x_21(b)]` has no Steinberg
formula. The product needs `[x_12(a), x_23(b)] = x_13(ab)`, and reading `phi` off `n_12(a)` needs the
matrix-unit form, which is the gate.

### 1.7 Plan 2: two overstatements; it stays OPEN with no proof

**The rank bound has no proof.**
- "`rk(n_13(a)) <= rk(N_13)`" is unproved, since `x_13(a)` and `x_13(1)` need not be conjugate.
- The commutator bound gives only `rk(n_13(ab)) <= 2 min(rk n_12(a), rk n_23(b))`, because
  `rk([g,h] - 1) = rk(g h g^-1 - h) <= 2 rk(h - 1)`, and symmetrically in `g`.
- Every normalized rank is at most 1, so "bounded rank" says nothing on its own.

**The defect is not a conjugate.**
- `n_13(ab) - XY = (1 + X)(YX)(1 + Y)`, with `X = n_12(a)` and `Y = n_23(b)`, is a two-sided unit
  multiple of `YX`. I re-derived it from `C(1 + Y)(1 + X) = XY + YX`, using `X^2 = Y^2 = 0` in
  characteristic two.
- Balance for every `(a, b)` gives `D = 0`, but the converse is proved only for unit coefficients.
- The factorization is a characteristic-two statement.

### 1.8 The lead's Kaplansky calibration L4a: CORRECTION on two points

1. **The consequence is misnamed.** L4a says an exact family in `F_2[R^x]` "makes `R^x` non-sofic,
   which is far stronger than the gate". But `R^x` is already non-sofic on main
   (`openai-leavitt-unit-nonsofic`, root; Lean `binaryLeavittRankTwo_not_isSofic`), so Elek--Szabo adds
   nothing.
   - **What such a family actually gives:** failure of Kaplansky direct finiteness for `F_2[R^x]`.
   - **Where that goes:** through `nonsurjunctive-from-stable-finiteness-failure`, that is
     `leavitt-unit-group-nonsurjunctive`, a counterexample to Gottschalk's conjecture.
   - **So** it is not an absurd outcome to be ruled out; it is the counterexample side's main target.
2. **The constraint binds (i) and (iii) jointly, not (i) alone.**
   - If (i) is a ring identity valid in `F_2[R^x]` (with `sigma` the inclusion), and (iii) is proved
     through the rank of `M`, then `e` may vanish in `F_2[R^x]`, and nothing follows.
   - The correct statement: a construction whose (i) and (iii) both survive in `F_2[R^x]` refutes
     Kaplansky direct finiteness there. Otherwise at least one of them uses a property of `M` that
     `F_2[R^x]` lacks.

**L3 checks out.** In the baseline, `pi(tau(a)) = a E_11`, and each L1 relation is the image of a
nonzero element of `ker pi`, for example `tau(t_1) tau(s_0)`. PASS as a remark.

### 1.9 Status of Plan 1

`rank-four-isometry-relations-give-corner-cuntz-family` is equivalent, model by model, to `D = 0` (lead
L2, w4-r4-corner Section 0). It remains OPEN, and no construction of `S_i`, `T_j`, `e` has landed.

## 2. w4-r4-corner (5d14c96d85, 6414c135d1)

### 2.1 `nonzero-rank-corner-cannot-hold-a-cohn-toeplitz-triple`: PASS

1. **The rank identity.** `rk(1 - ab) = rk(1 - ba)` holds at every matrix level: `v |-> Bv` maps
   `ker(1 - AB)` into `ker(1 - BA)`, injectively because `v = ABv`, and onto by symmetry.
2. **Padding.** Put `a = S_0 + (1 - e)` and `b = T_0 + (1 - e)`. The cross terms vanish because
   `S_0, T_0` are in `eMe`. So `ba = e + (1 - e) = 1` and `ab = S_0 T_0 + (1 - e)`.
3. **Conclusion.** `rk(e - S_0 T_0) = 0`, and `rk` is faithful on `M` (`d_omega` is the rank-null
   ideal), so `S_0 T_0 = e`.
4. **Items 2 and 3.** `S = eS = S_0 T_0 S = 0`, then `e = T_1 S_1 = 0`. `T_1` may be anywhere in `M`.
5. **Scope.** The `distinct_from` claim, that this implies the no-rank-model claim for every
   `L_K(1,2)`, holds with `e = 1`.

### 2.2 `el4-model-trivial-on-one-unit-root-element-is-trivial`: PASS

**Part 1: all twelve commutators, in the order given.**
- Each line uses the Steinberg relation `[x_ab(r), x_bc(s)] = x_ac(rs)` with coefficient `1 r` or `r 1`.
- Each line takes its `N`-argument from an earlier line:
  - IK and IL use IJ;
  - KJ and LJ use IJ;
  - IJ(r) uses IK;
  - KL uses KJ;
  - LK uses LJ;
  - KI uses KL;
  - LI uses LK;
  - JI uses KI;
  - JK and JL use JI.
- All twelve root subgroups are reached.
- `N` is normal, so `[a, g] = a (g a^-1 g^-1)` and `[g, a]` lie in `N`.

**Part 2.**
- `x_IK(rb) = [x_IJ(r), x_JK(b)]` and `x_LK(arb) = [x_LI(a), x_IK(rb)]`.
- `R` is simple, so `sum a_m r b_m = 1`.
- Additivity gives `x_LK(1)`.

**Scope.** The claim is stated for any ring and any target group, and it needs none of the rank
structure.

### 2.3 Corollary 4 (positivity of `e`): PASS

- `D != 0` makes `sigma` nontrivial.
- By 2.2 no `n_IJ(1)` vanishes, and for simple `R` no `n_IJ(r)` with `r != 0` does.
- `eX = X` gives `rk(X) = rk(eX) <= rk(e)`.

### 2.4 Proposition 2, `min rk(e)` with `eDe = D` equal to `2 rk(D) - rk(D^2)`: PASS

**Lower bound, at matrix level.**
- `eD = D` iff `range D <= range e`, and `De = D` iff `ker e <= ker D`.
- `ker e` meets `V = range D` trivially, so `ker e ⊕ (V ∩ W) <= W`, where `W = ker D`.
- `dim(V ∩ W) = rank D - rank D^2`, since `D|_V` has kernel `V ∩ W` and image `range D^2`.

**Attained.** Take `W'` a complement of `V ∩ W` in `W`. Then `V ∩ W' = 0` and
`dim V + dim W' = n - rank D + rank D^2 <= n`, so the projection onto a complement `U ⊇ V` along `W'`
works.

**In `M`.** Lift `D` as `e_i d_i e_i` for the lower bound, and use per-level minimizers for the upper
bound.

**Consequence.** The literal check (iii), `rk(e) = rk(D)`, is false in general. Replace it by `e != 0`.

### 2.5 Framing, Sections 3.2 to 3.4: PASS

- **3.2.** It agrees with 1.2. Its `D_4 = 0` branch uses the matrix-unit claim. For odd `p` that also
  needs the reversed-root-pair claim (1.3).
- **3.3.** The group identities of `EL_4(R)` are exact in `M`, and the coefficient relations enter only
  inside commutators. Correct.
- **3.4.** The route uses the no-rank-model endpoint over every finite `K`, beyond its `F_2` statement.
  Correct; 2.1 covers every `K`.

## 3. w4-r4-adversary (c6697aa47b, 9fd9898e8e)

### 3.1 `unipotent-frame-relations-cannot-assemble-corner-cuntz-family`: PASS

1. **The homomorphism.** For unitriangular `g, h`, `(gh)_(i,i+1) = g_(i,i+1) + h_(i,i+1)`, because the
   only nonzero terms of `sum_k g_ik h_(k,i+1)` are `k = i` and `k = i+1`. So `g |-> (g_12, g_23)` is a
   homomorphism.
   - An `F_p`-linear `phi : R -> F_p` with `phi(1) = 1` exists, since `1 != 0`.
   - `rho(g) = u^phi(g_12) v^phi(g_23)`, acting by translation on `F_p[C_p^2]`, is a homomorphism into
     `GL_(p^2)(F_p)`.
2. **The defect.** `N_12 = x = u - 1` and `N_23 = y = v - 1` on `F_p[x,y]/(x^p, y^p)`. `N_23 N_12` is
   multiplication by `xy`, whose image is spanned by `x^i y^j` with `1 <= i, j <= p-1`. So
   `rk = (p-1)^2/p^2`.
   - `x_13(1)`, `x_24(1)`, `x_14(1)` and `x_34(1)` have zero `(1,2)` and `(2,3)` entries, so their
     `N` vanish.
3. **The relations.** Every relation among unitriangular elements holds, including both isometry frames,
   both readings of `x_14(abc)`, and `x_12(1) = x_12(e_0) x_12(e_1)` (`phi` is additive).
4. **No corner family.** This is Section 1.4.
5. **Scope.** `M_(p^2)(F_p)` with normalized rank is a constant rank ultraproduct. So the model refutes
   every implication valid for all homomorphisms of `U_4(R)` into rank ultraproducts, which is exactly
   what the claim says.
6. **Weyl element.** `[[1,1],[0,1]] [[1,0],[-1,1]] [[1,1],[0,1]] = [[0,1],[-1,0]]`, and it conjugates
   `x_12(a)` to `x_21(-a)`.
7. **The characteristic-two value `3/8`.** I computed it directly.
   - `(1+y)(1+x) F_2[D_8]` is spanned by:
     - `v_1 = 1+x+y+yx`;
     - `v_2 = 1+y+xy+yxy`;
     - `v_3 = x+yx+xyx+z`;
     - `v_4 = xy+yxy+xyx+z`.
   - `v_1 + v_2 = v_3 + v_4`, and `v_1, v_2, v_3` are independent.
   - So the rank is `3/8`.
8. **The `{3,4}`-grouping dictionary (artifact Section 3).** Merge `(3,4)` by `(s_0, s_1)`. Then
   `x_23(b) |-> x_23(b t_0)` and `x_34(c) |-> 1 + s_0 c t_1 E_33`, re-derived from
   `theta = [[1,0,0,0],[0,1,0,0],[0,0,s_0,s_1]]`. PASS.

### 3.2 `reversed-root-pair-identity-forces-root-squares-to-vanish`: PASS

I derived this independently in Section 1.3, and route steps 1 to 4 match. So condition 3 of
`el3-unit-root-matrix-units-iff-two-root-identities` reduces to the single identity `N_23 N_12 = 0` in
every characteristic.

## 4. w4-r4-approx (b7b0e9d387, 9930bb89f5)

### 4.1 `toeplitz-isometry-defects-have-total-rank-at-least-one`: PASS

**Lemma 1 (push-through).**
1. `[[1,0],[-y,1]] [[1,x],[y,1]] = [[1,x],[0,1-yx]]`, and multiplying on the right by `[[1,-x],[0,1]]` gives
   `diag(1, 1-yx)`.
2. The mirror product is `diag(1-xy, 1)`.
3. Invertible factors preserve rank and block diagonals add, so `rk(1-xy) = rk(1-yx)`.

**The corner form.** For `x, y` in `eAe`, `1 - (x + 1 - e)(y + 1 - e) = e - xy`, so the corner form
follows even without orthogonal additivity.

**Lemma 2.** `X = X(e - ST) + (XS)T` for `X` in `Ae`. Subadditivity follows from the three axioms,
because `a + b` factors through `diag(a,b)` by a row and a column. Then Lemma 1 turns `e - ST` into
`e - TS`.

**Theorem 3.**
1. Lemma 2 with `X = T_1`, `S = S_0`, `T = T_0` gives `rk T_1 <= rk(e - T_0 S_0) + rk(T_1 S_0)`.
2. `rk e <= rk(T_1 S_1) + rk(e - T_1 S_1)` and `rk(T_1 S_1) <= rk T_1`.
3. **Sharpness:** `A = k`, `S_0 = T_0 = 1`, `S_1 = T_1 = 0` gives `0 + 1 + 0 = 1`.

**Corollary 4.** With `phi(1) = 1`, `phi(0) = 0` and `t_1 s_0 = 0` in `L_K(1,d)` for `d >= 2`, the
three defects are multiplicativity defects and add to at least `1`. So one is at least `1/3`.

**The corner consequence.** `rk X <= rk(e - TS) + rk(XS) = 0`, and faithfulness gives `X = 0`.

### 4.2 The collapse routes: PASS

- **`ring-rank-approximability-forces-non-linear-soficity`.** The right side is false by Corollary 4,
  since `F` contains `t_0, s_0, t_1, s_1` and `eps < 1/3`. The equivalence then makes the left side
  false. This is a valid route, conditional on the open equivalence node.
- **`ring-rank-approximability-from-leavitt-el3-triviality`.**
  - Triviality kills every model of `EL_3(R) ~= R^x`.
  - An `F_p`-linear sofic approximation would give an injective homomorphism into `M^x`
    (w4-r4-corner Section 3.3).
  - So both sides are false and the equivalence holds.

This matches Section 1.6 and the lead pass.

## 5. w4-heisenberg (f576dccf26)

### 5.1 `unitriangular-data-cannot-assemble-corner-leavitt-families`: PASS

1. **Local finiteness.** Take `b_1, ..., b_m` strictly upper triangular.
   - The nonunital `F_p`-algebra `B` they generate is spanned by words of length less than `n`, since
     `B^n = 0`.
   - So `B` is finite, and `1 + B` is a finite group, with `(1+b)^-1 = sum (-b)^j` in `1 + B`.
2. **The model.**
   - Exhaust `L` by finite `P_k`. Left regular representations are exactly multiplicative on a pair
     once both elements lie in `P_k`, so `sigma_reg` is a homomorphism into `M^x`.
   - `F_p[P_k]` is free of rank `[P_k : Q]` over `F_p[Q]`. So `rank lambda_(P_k)(alpha)` is
     `[P_k : Q]` times `rank lambda_Q(alpha)`, and the normalized rank is intrinsic to `Q`.
3. **Values.**
   - **`p = 2`:** `3/8`, recomputed in Section 3.1.
   - **Odd `p`:** `(y-1)(x-1) = yx - y - x + 1` is nonzero in `F_p[H(F_p)]`, so its rank is at least
     `1/p^3`.
   - **`diag(w,w,w)`:** it has order 2, since `w^2 = 1`, and normalizes `UT_3(R)`. So
     `UT_3(R) ⋊ <diag(w,w,w)>` is locally finite.
4. **Weakened endpoint remark.** Put `f_0 = S_0 T_0` and `f_1 = S_1 T_1`.
   - `T_1 S_0 = 0` gives `f_1 f_0 = 0`.
   - `f_0' = f_0(e - f_1)` is idempotent, since `(e - f_1) f_0 = f_0`.
   - `f_0'` and `f_1` are orthogonal.
   - `f_0' f_0 = f_0` gives `rk f_0' >= rk f_0 >= rk e`, and `rk f_1 >= rk e`.
   - So `rk e >= 2 rk e`, and `rk T_1 <= rk e` forces `T_1 = 0`.
5. **Scope.** The firewall covers derivations whose inputs hold in every rank model of `UT_4(R)`.
   The regular model has `D != 0`, while the endpoint is impossible in every `M`.

## 6. w4-r4-orth (fcffe16327)

### 6.1 `index-three-corner-placement-holds-only-modulo-two-root-defects`: PASS

**The swap identity (Sw).**
- `[x_ij(r), x_jk(r')] = x_ik(rr')` gives `x_ij x_jk = x_ik x_jk x_ij`.
- Expanding `(1 + n_ij)(1 + n_jk) = (1 + n_ik) X_jk X_ij` and substituting `X_jk X_ij = 1 + n_jk + n_ij + n_jk n_ij`
  gives `n_ij n_jk = n_jk n_ij + n_ik X_jk X_ij`.
- No characteristic is used.

**The identity.**
1. (Sw) at `(4,3,1)` gives `n_43(1) n_31(b) = n_31(b) n_43(1) + n_41(b) X_31(b) X_43(1)`.
2. `x_34` and `x_31` commute (`4 != 3` and `3 != 1`), so `n_34(a) n_31(b) = n_31(b) n_34(a)`.
3. (Sw) at `(3,4,1)` gives `n_34(a) n_41(b) = n_41(b) n_34(a) + n_31(ab) X_41(b) X_34(a)`.
4. Substituting gives exactly the three terms of the claim.

**The honest value.** Every factor of `W = X_41 X_34 X_31 X_43` has first row `e_1`, so `E_31 W = E_31`
and the first term is `rho(ab) E_33`. The deviation products `E_31 E_34` and `E_41 E_34` vanish.

**Index 4 replaced by 2.** (Sw) at `(2,3,1)` and `(3,2,1)`, together with `[x_32, x_31] = 1`.

**Remark 3.1.** I checked every nonempty ordered sub-product of `a = x_34(E_22)`, `b = x_43(1)`,
`c = x_31(E_11)`, `d = x_13(1)` in `SL_8(F_2)`.
- **Singles and pairs.** Each element is `1 + A` with `A^2 = 0`, so `(1+A)(1+B) = 1` forces `B = -A`.
  Different positions never meet that.
- **Triples.**
  - `abc`: `(ab)^-1` has entries at `(4,3)`, `(3,4)` and `(4,4)`, and `c` does not.
  - `abd`: same entries, and `d` does not have them.
  - `acd`: `ac` sits at `(3,4)` and `(3,1)`, while `d^-1` sits at `(1,3)`.
  - `bcd`: `bc` sits at `(4,3)`, `(3,1)` and `(4,1)`, while `d^-1` sits at `(1,3)`.
- **The quadruple.** `ab` sits at `(3,4)`, `(4,3)` and `(3,3)`, while `(cd)^-1` sits at `(1,3)`, `(3,1)`
  and `(1,1)`.
- **Conclusion.** The coefficient at `1` is `1`, so the cross term is nonzero.

## 7. w4-r4-complete (c22ebb8e32, b09f639b5d)

Four nodes were deleted as duplicates at b09f639b5d, on the lane's instruction, so I gave them no verdict.

### 7.1 `leavitt-completeness-transport-formula-for-root-data`: PASS

**(a)**
- `x_ac(1) = x_ac(e_0) x_ac(e_1)`, and the two factors commute, so `N = E_0 + E_1 + E_0 E_1`.
- In characteristic two `x(r)^2 = x(2r) = 1`, so `n^2 = 0`.

**(b)** Put `P = A + B + AB`.
- `[X, Y] = XYXY`, since `X^-1 = X` and `Y^-1 = Y`.
- `(1 + P)^2 = 1 + P^2`.
- `A^2 = B^2 = 0`, so `A AB = AB B = 0`.
- Hence `P^2 = AB + BA + ABA + BAB + ABAB`.

**(c)** Sum over `i`, and substitute `E_0 + E_1 = N + E_0 E_1` in characteristic two.

**Natural models.** `B_i A_i`, `A_i B_i A_i`, `B_i A_i B_i` and `A_i B_i A_i B_i` contain `E_bc E_ab` or
`E_ac E_ab`, or equal `E_ac E_ac`. All of these vanish. `E_0 E_1` contains `E_ac E_ac = 0`.

**Return operator.** `NWNW = NW`, and the completeness defect of `S_i = A_i`, `T_i = B_i W` is
`(E_0 E_1 + rho_0 + rho_1) W`.

## 8. w4-gate-descent (e24abed257, 3116be756a)

### 8.1 `leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`: PASS

**Lemma 2.1: the quotient model.**
1. **Homomorphism.** `sigma(g) f = f` gives `(1-f) sigma(g) f = 0`, so `sigma_W` is multiplicative.
2. **No fixed vectors.**
   - A fixed `x` in `(1-f)M` gives `c(g) = f sigma(g) x`, and `c(gh) = c(g) + sigma(g) c(h) = c(g) + c(h)`,
     because `sigma(g)` fixes `fM`.
   - Perfection kills `c`, so `x` lies in `fM ∩ (1-f)M = 0`.
3. **Nontrivial.** A trivial `sigma_W` lands `sigma` in `1 + fM(1-f)`, which is abelian because
   `fM(1-f) fM(1-f) = 0`.
4. **The defect.** `N f = 0` gives `(1-f) N_23 (1-f) N_12 (1-f) = (1-f) D_A`.

**Lemma 2.2: displacement.**
- `Fix_r` is the intersection of the four right annihilators `(1 - z_i x_i) M`.
- Finite intersections of principal right ideals are principal in a regular ring, and have rank at
  least `1 - sum rk(x_i)`.

**Lemma 2.3: compactness.**
1. Along the sequence, fix one maximizing generator.
2. For each `n`, finitely many relations and ranks hold within `1/n` at some level in the ultrafilter
   set.
3. Near-invertible lifts are fixed at rank cost `eps`.
4. A finitely generated field of characteristic two is finite over some `F_2(t_1..t_d)`, so it embeds in
   `Omega`, and ranks do not change.
5. The ultralimit is an exact homomorphism with `[1000]` corner product of rank `0`.
6. `two-root-identity-is-corner-local-for-leavitt-rank-models` holds over every field of characteristic
   two, and its (3)⇒(1) with `P = 1000` makes the ultralimit trivial.
7. That contradicts displacement at least `eta`.

**Theorem 2.4: the gap.**
- **Lower bound.** Apply Lemmas 2.2 and 2.3 in the renormalized corner `(1-f)M(1-f)`. Pass from `[1000]`
  to any proper cylinder by the prefix-replacement `u` of Fact 1.2.
- **Upper bounds.**
  - `((1-f) N_12 (1-f))^2 = 0`, since `N_12^2 = 0` and `N f = 0`. Fact 1.1(c) gives `rk(1-f)/2`.
  - `D_A = D_A(1-f)` gives `rk D_A <= rk(1-f)`.

**The facts used.**
- **Fact 1.1.** Parts (a) to (d) are standard dimension-function facts for regular rings.
- **Fact 1.2.** I re-derived it:
  - `T[A] S[B] = 0` for disjoint cylinders, so `iota_A` and `iota_B` commute;
  - `u = sum S[B_i] T[A_i] + sum S[C'_j] T[C_j]` satisfies `u S[A_i] = S[B_i]` and `T[A_i] u^-1 = T[B_i]`.
- **Fact 1.3.** It holds.

### 8.2 `nested-two-root-defect-pieces-decay-geometrically-both-ways`: PASS

**Lemma 3.0.**
- The case `A = 0` is the globality claim in degree `(1,0)`.
- For other `A`, `sigma(u) fM = fM`.

**Theorem 3.1.**
- **Upper bound.**
  - `N^B_12 PM = P N^B_12 M` lies in `Q_k`, so `N q_k = q_k N q_k` and `(q_k N q_k)^2 = q_k N^2 q_k = 0`.
  - `f(k+1) = rk(D_B q_k) <= rk(N^B_12 q_k) <= f(k)/2`.
- **Lower bound.**
  - `tau = q_k sigma(iota_B(.)) q_k` is a model, because `Q_k` is invariant.
  - A `tau`-fixed `v` in `Q_k` is `sigma(iota_B(R^x))`-fixed, hence lies in `fM = 0`.
  - `iota_B o iota_1000 = iota_(B1000)`, and `B1000` is disjoint from every `A_i`.
  - So the `[1000]` defect of `tau` is `D_(B1000) q_k`, whose rank is `f(k+1)` by V-transitivity on the
    configuration `(A_1..A_k, B1000)`, which still has proper union.

**Corollary 3.2.**
- **Rank bounds.** `delta_1 <= rk(1-f)` and `delta_k >= rk((1-f) Q_k) = rk(1-f) f_W(k)`.
- **No limit corner.** Its rank is below `delta_k -> 0`.
- **Not re-derived.** Item 1 rests on Lemma 1.1 of the defect-piece artifact. I did not re-derive that
  artifact, which is `w3-vf-linear`'s item.

### 8.3 `near-minimal-defect-models-have-multiplicative-cylinder-defects`: PASS

**Proposition 4.1.**
1. **The kernel corner.** `K = r.ann(P)` has rank `1 - f(k)` by Fact 1.1(a).
   - It is invariant because `P` commutes with `sigma(iota_B(.))`.
   - Its model is fixed-point-free by Lemma 3.0, and nontrivial since `rk k >= 1/2` for `k >= 1`.
   - Hence `rk(D_(B1000) k) >= c_* (1 - f(k))`.
2. **The triangular count.**
   - `TM -> J/K` is onto, with kernel `TM ∩ K ⊇ TK`, so `rk J - rk K <= rk TM - rk TK`.
   - By Fact 1.1(d), `rk J - rk K = rk(PJ) = rk(PTM) = rk(TP) = f(k+1)`.
   - `rk TM = delta`, by V-conjugacy.
3. **Algebra.** `f(k+1) <= delta - c_*(1 - f(k))`, with `c_* >= delta/(1+eps)`, gives
   `f(k+1) <= delta f(k) + eps delta`.
4. **The iterate.** Put `e_k = f(k) - delta^k`. Then `e_1 = 0` and `|e_(k+1)| <= eps delta + delta |e_k|`,
   so `|e_k| <= eps delta/(1 - delta) <= 2 eps delta`.

## 9. w4-r4-corner, second landing (ef454c9283)

### 9.1 `opposite-unit-root-product-vanishes-only-for-trivial-models`: PASS

1. **The braid relation over `Z`.**
   - `x(1) y(-1) x(1) = [[0,1],[-1,0]] = y(-1) x(1) y(-1)`, re-derived in Section 3.1.
   - With `-1 = 1` in `R` it becomes `x_13(1) x_31(1) x_13(1) = x_31(1) x_13(1) x_31(1)`.
2. **The expansion.** Using `X^2 = Y^2 = 0` and `2X = 0`:
   - `(1+X+Y+XY)(1+X) = 1 + Y + XY + YX + XYX`;
   - symmetrically `1 + X + XY + YX + YXY`;
   - so `Y + XYX = X + YXY`.
3. **The collapse.** `YX = 0` kills both `XYX` and `YXY`, so `X = Y`.
4. **The finish.**
   - `x_13(1)` commutes with `x_12(r)`, since `3 != 1` and `1 != 2`.
   - `x_32(r) = [x_31(1), x_12(r)]`, so `sigma(x_32(r)) = 1`.
   - Section 2.2 then gives triviality.
5. **Scope.**
   - For another pair `(I,J)`, use any third index `K`.
   - The claim is stated for characteristic two only, which is correct: in odd characteristic the braid
     step involves `n_31(-1)`.
6. **Positivity.** `e YX = YX` gives `rk e >= rk YX > 0` by faithfulness.

### 8.4 Route `leavitt-rank-triviality-via-strict-defect-submultiplicativity`: PASS as a conditional route

**Step 2.** It needs only Theorem 3.1, since `f(2) >= c_* delta`, and `c_* >= delta/(1+eps)`.

**Step 3.** `delta^2/(1+eps) <= theta delta^2`, with `delta > 0`, forces `1/(1+eps) <= theta`.
- **Why the model can't escape:** the open claim quantifies `theta < 1` uniformly over all nontrivial
  fixed-point-free models, so the choice of near-minimal model cannot dodge it.
- **From quotient to model:** a nontrivial `sigma` has a nontrivial fixed-point-free quotient
  (Lemma 2.1).

**Payoff.** It is as in Section 4.2.

**Scope.** The route depends on the open claim. Its three other inputs PASS (Sections 8.1 to 8.3).

**On my Section 8.2 scope limit.** Lemma 1.1 of the defect-piece artifact already has independent
passes: w3-vf-linear Section 10.1, and gk-vf-linear Section 52 (reported by w4-gate-descent).

## 10. w4-r4-orth, Section 5 (f25ccc5958): halving is locally finite data. PASS.

No node was added; this section covers an Attempts entry on
`leavitt-disjoint-cylinder-defects-strictly-submultiplicative`.

**Lemma 5.1.** Conventions: `S[mu] = s_(mu_1)...s_(mu_k)` and `T[mu] = t_(mu_k)...t_(mu_1)`.
1. **Product formula.** `iota_A(Delta(g)) = S[A0] g T[A0] + S[A1] g T[A1] + 1 - S[A]T[A] = iota_(A0)(g) iota_(A1)(g)`.
   - The cross terms die because `T[A0] S[A1] = 0`.
   - `S[A0]T[A0] + S[A1]T[A1] = S[A]T[A]`.
2. **Images of the unit pair.**
   - `s_0 S[0] T[10] t_0 = S[00] T[010]` and `s_1 S[0] T[10] t_1 = S[10] T[110]`.
   - `s_0 S[10] T[11] t_0 = S[010] T[011]` and `s_1 S[10] T[11] t_1 = S[110] T[111]`.
3. **The permutation `u`.** Its source words `{00, 010, 011, 10, 110, 111}` and target words
   `{00, 100, 110, 01, 101, 111}` are complete prefix codes, so `u` lies in `V`.
4. **Conjugation.**
   - `u S[010] = S[100]` and `T[011] u^-1 = T[110]`.
   - The refined pairs are `x_12(1) = 1 + S[00]T[100] + S[01]T[101]` and
     `x_23(1) = 1 + S[100]T[110] + S[101]T[111]`.
   - Both are recovered.
5. **Rank equalities.** They follow by conjugating by `sigma(iota_A(u))`, and from Fact 1.2 on `A0, A1`.

**Proposition 5.2.**
- **Direct product.** `L` is a direct product: the factors commute and meet trivially.
- **Swap.** `w s_0 = s_1` and `t_0 w = t_1`, so `iota_A(w)` swaps the factors.
- **Local finiteness.** `UT_3` over an `F_2`-algebra is locally finite, and so is the extension by the
  swap.
- **Free profile.** The regular model gives `D_8 x D_8` and the diagonal `D_8` the free profile. There
  `rk(alpha_0 (x) alpha_1) = (3/8)^2`, so `theta = 1` while every relation used holds.

**Remark 5.3.**
- **Mixture ranks.** They are `(3/8)(b+c)`, `(3/8)(b+d)`, the diagonal `(3/8)(b+c+d)`, and
  `f(2) = (9/64) b`.
- **Forced profile.** Lemma 5.1 forces `c = d = 0`.
- **Ratio.** `f(2)/delta^2 = 1/b`.

**Remark 5.4.** The free proportion of `V (x) V` is `2p - p^2`, which forces `p` in `{0, 1}`.

**Scope.** A `theta < 1` has to use `sigma` beyond this locally finite group. That agrees with the
Section 3 and Section 5 firewalls.

## 11. Family SUB: w4-sub-weyl (b3baccede9)

### 11.1 `near-minimal-defects-are-rank-independent-of-cylinder-commutants`: PASS

1. **Invariance.** `X` commutes with `sigma(iota_A(.))`.
   - So `XM` is invariant: `sigma(iota_A(g)) X M = X sigma(iota_A(g)) M`.
   - `K = r.ann(X)` is invariant too: `X sigma(iota_A(g)) y = sigma(iota_A(g)) X y = 0`.
   - The ranks are `rk X` and `1 - rk X` (Fact 1.1(a)).
2. **The range corner.** Put `eM = XM`.
   - `e sigma(iota_A(.)) e` is a model on `eMe`.
   - A fixed vector lies in `Fix_r(sigma(iota_A(R^x))) = Fix_r(sigma(R^x)) = 0` (Lemma 3.0).
   - `iota_A o iota_P = iota_(AP)` and invariance give defect `D_(AP) e`, whose rank is
     `rk(D_(AP) X M) = rk(D_(AP) X)`.
   - Fact 1.2 makes the normalized defect at every proper prefix the same number, which is at least
     `c_*`.
3. **The kernel corner.** Same argument on `kMk`: `rk(D_(AP) k) >= c_*(1 - rk X)`.
4. **Triangular count.** Put `T = D_(AP)`, which lies in the image of `F_2[iota_A(R^x)]`.
   - `T` commutes with `X`, so `TK` lies in `K`.
   - With `J = TM + K`: `rk TM >= rk TK + rk J - rk K`.
   - By Fact 1.1(d), `rk J - rk K = rk(XJ) = rk(XTM) = rk(TX)`.
   - `rk TM = delta`.
   - Hence `delta >= c_*(1 - rk X) + rk(D_(AP) X)`.
5. **Near-minimal case.** Put `c_* >= delta/(1+eps)`.
   - Lower side: `delta rk X - rk(DX) <= delta rk X · eps/(1+eps) <= eps delta`.
   - Upper side: `rk(DX) <= (eps delta + delta rk X)/(1+eps) <= delta rk X + eps delta`.
   - At `delta = c_*` both sides meet.
6. **Special cases.**
   - `X` a product of disjoint defects recovers Proposition 4.1.
   - Idempotents of invariant decompositions carry defect exactly `c_*` at the infimum.

### 11.2 Artifact Section 3 (finite-subgroup data firewall): PASS as a remark

- **Consistency.** Regular ranks on `F_2[Q]` for finite `Q`, extended to finite `Q' ⊇ Q`, agree with
  those on `F_2[Q]`, because `F_2[Q']` is free over `F_2[Q]`.
- **Invariance.** They are invariant under conjugation by any unit.
- **The defect product.** `D_A D_B` lies in `F_2[D_8 x D_8]` for disjoint `A` and `B`, so its rank is
  `(3/8)^2`.
- **Consequence.** Any argument that sees only relations and ranks inside finite subgroups realizes
  `theta = 1`. This matches Sections 5.1 and 10.

## 12. w4-r4-adversary, second landing (a597ebfc50)

### 12.1 `covariant-monotone-cylinder-families-in-rank-models-are-constant`: PASS, with a scope remark

1. **Proposition 1: joins and meets.**
   - **Existence of the join.** Put `f_n M = A_1 + ... + A_n`.
   - The conditions `e^2 = e`, `e f_n = f_n` for every `n`, and `rk e <= s` are finitely satisfied by
     `f_N`, since `f_n` lies in `f_N M`.
   - They are closed in the rank metric, and metric ultraproducts along a nonprincipal ultrafilter on
     `N` are countably saturated. So `e` exists.
   - **Leastness.** For principal `K` containing every `A_n`, `K ∩ eM` is principal of rank `s = rk(eM)`,
     so faithfulness gives `eM ⊆ K`.
   - **Meets.** Same argument, dual: `g_N e = e` and `rk e >= s - 1/m`, with `K + eM` for greatest.
   - **Scope remark.** Leastness is proved among principal right ideals, not all right ideals, as
     Proposition 1 states it. Every use in the claim is principal: annihilators of principal ideals,
     joins of spans.
2. **Theorem 2: rigidity.**
   - Transitivity of `V` on proper cylinders gives one rank.
   - `A_(w0) ⊆ A_w` with equal rank gives equality, so `A_(0x) = A_[0]` and `A_(1x) = A_[1]`.
   - The leaf map `(00, 01, 1) -> (00, 1, 01)` is a valid prefix replacement fixing `[00]` and carrying
     `[01]` onto `[1]`. So `A_[0] = sigma(v) A_[00] = sigma(v) A_[0] = sigma(v) A_[01] = A_[1]`.
3. **Corollary 3.** `e_w e_(wi) = e_(wi)` gives monotonicity. Covariance is conjugation. Then
   `e_(w0) = e_(w1) m`, so `e_(w0) = e_(w0) e_(w1) m = 0`, and constant rank gives `e_w = 0`.
4. **Lemma 4: root spans.**
   - `v s_w y t_(w') v^-1 = s_(vw) y t_(vw')`.
   - `s_(w0) y t_(w') = s_w (s_0 y) t_(w')`, and `t_(w'0) = t_0 t_(w')` gives the second slot.
   - `V` is transitive on disjoint pairs with proper union.
5. **Proposition 5: frame identity forces triviality.**
   - **The frame product.** The left annihilator `M(1-e)` of `V_(a0,b)` contains the join
     `L_(b,a1) = L_(b,a)`, so `N_(b,a)(y) N_(a,b)(z) = 0`. The swap in `V` reverses the product.
   - **Squares.** In characteristic two `(1+X)^2 = sigma(j(x_12(2))) = 1`, so `X^2 = 0`, and likewise
     `Y^2 = 0`.
   - **The Weyl element.** Over `F_2`, `x_12(1) x_21(1) x_12(1) = [[0,1],[1,0]]`, and
     `sigma(w) = 1 + X^2 + Y`.
   - **Conjugation.** `sigma(w) X = Y sigma(w)` gives `X + X^3 = Y + Y^2`. Then `X = Y + Y^2`, and
     multiplying by `Y` gives `Y^2 (1+Y) = 0`, so `X = Y`.
   - **Triviality.** `x_12(1) x_21(1) = [[0,1],[1,1]]` has order 3, and `sigma(j(.)) = 1 + 2X = 1`. The
     kernel is a nontrivial normal subgroup, so `binary-leavitt-unit-group-is-simple` makes `sigma`
     trivial.
6. **Consequence.** Corollary 3 gives no orthogonal covariant diagonal in any rank model or nonzero
   corner. So `leavitt-two-root-defect-piece-forces-covariant-diagonal` is model by model equivalent to
   the gate.

## 13. Family SUB: w4-sub-halving (3897962264)

### 13.1 `near-minimal-defect-ranges-are-rank-faithful-for-the-commutant`: PASS

1. **Clopen groups.** `V` is transitive on proper nonempty clopen sets. So `v U = C` for a proper
   cylinder `C`, `v G_U v^-1 = iota_C(R^x)`, and `Fix_r(sigma(G_U)) = sigma(v)^-1 fM = 0` by Lemma 3.0.
2. **Corner models.** An invariant `kM` with `k != 0` carries a nontrivial fixed-point-free model.
   - `V ∩ G_U` is transitive on frame triples with proper union inside `U`, and it preserves `kM`.
   - So `rk(D_Theta k) >= c_* rk k`.
3. **Two-sided bound.**
   - **Lower.** The range corner gives `rk(TZ) >= c_* rk Z >= delta rk Z/(1+eps)`, so
     `rk(TZ) - delta rk Z >= -eps delta rk Z/(1+eps)`.
   - **Upper.** The kernel corner and the triangular count give
     `rk(TZ) - delta rk Z <= (delta - c_*)(1 - rk Z) <= eps delta (1 - rk Z)/(1+eps)`.
4. **Matrices.** `sigma (x) 1_n` is a nontrivial fixed-point-free model with the same `delta`. Its
   `G_U`-commutant contains `M_n(C_U)`.

This sharpens Section 11.1.

### 13.2 The distortion routes: PASS as conditional routes

- **`commutant-distortion-from-strict-defect-submultiplicativity`.**
  - **Setup.** Take `U = B`, `Theta` the triple of `B0` (union `B0`, a proper subset of `B`), and
    `Z = D_A` with `A` disjoint from `B` and `A ∪ B` proper.
  - **Distortion.** `rk(D_(B0) D_A) = f(2) <= theta delta^2` and `rk Z = delta`, so the distortion is at
    least `(1 - theta) delta^2`.
  - **Constant.** `delta >= c_0` gives `kappa = (1 - theta) c_0`, independent of the model.
- **`leavitt-rank-triviality-via-commutant-rank-distortion`.**
  - **Near-minimal model.** Take one with `eps < kappa`.
  - **Faithfulness bound.** `|rk(D_Theta Z) - delta rk Z| <= eps delta/(1+eps) < kappa delta`, which
    contradicts the open distortion claim, since it fixes `kappa`, `U`, `Theta` and `n` uniformly.
  - **Payoff.** It is as in Section 4.2.

## 14. Family SUB: w4-cohn-el3 (550f005762)

### 14.1 `two-root-identity-in-all-models-iff-no-nontrivial-model`: PASS

1. **The tensor square is a model.**
   - `rk(AB (x) AB - C (x) C) <= rk(AB (x) (AB - C)) + rk((AB - C) (x) C) <= 2 rk(AB - C)`.
   - Normalized rank is multiplicative on tensors, and the characteristic stays two.
2. **Matrix units.** `u_ij u_ji = p_i` and `u_ij ∈ p_i M p_j` give `rk u_ij = rk p_i = rk p_j = rk N_12`.
3. **The product.** Each of the nine terms of `N'_23 N'_12` except `u_23 (x) u_12` and `u_12 (x) u_23`
   contains `u_23 u_12 = u_23 p_3 p_1 u_12 = 0` in some factor.
4. **Additivity.** The two summands have orthogonal left supports, `p_2 (x) p_1` and `p_1 (x) p_2`, and
   orthogonal right supports, `p_3 (x) p_2` and `p_2 (x) p_3`.
   - So `(X+Y) g = X`, `(X+Y) h = Y`, `e(X+Y) = X` and `f(X+Y) = Y`.
   - Hence `rk(X+Y) = rk X + rk Y = 2 rk(N_12)^2`.
5. **(a) implies (b).** Apply (a) to `sigma (x) sigma`. Then `rk N_12 = 0`, and `x_12(1)` normally
   generates `EL_3(S)` through Weyl conjugates and `[x_ac(1), x_cb(r)] = x_ab(r)`.

### 14.2 `cohn-elementary-group-rank-radical-is-trivial-or-everything`: PASS

1. **Embeddings.**
   - `J -> C_2`: `S^i T^j |-> s_0^i t_0^j` sends normal-form basis to basis.
   - `C_2 -> L(1,3)`: words over `{0,1}` never end in the special edge, so they stay basis words.
   - `L(1,3) -> R` through the code `{0, 10, 11}`: `s_0 t_0 + s_1 s_0 t_0 t_1 + s_1 s_1 t_1 t_1 = 1`, and
     the map is injective because `L(1,3)` is simple.
   - Injective ring maps give injective `EL_3` maps.
2. **The kernel.**
   - `(q)` is spanned by the matrix units `s_mu q t_nu = E_(mu,nu)` of the faithful Toeplitz
     representation, so `ker pi <= GL_fin`.
   - Row-changing transvections are `x_ab(s_mu q t_nu)`, and same-row ones are commutators through a
     third row. So `K <= ker pi`.
   - `SL_fin(F_2)` is a directed union of the simple `SL_n(F_2)`, `n >= 3`, so it is simple.
   - Commuting with every `E_(x,y)` forces a scalar, and the only scalar over `F_2` is `1`. So
     `C_G(K) = 1`.
3. **Normal subgroups.**
   - `N ∩ K` is `1` or `K`.
   - If it is `1`, then `[N, K] = 1`, so `N <= C_G(K) = 1`.
   - Otherwise `N/K` is normal in `pi(G) = EL_3(R)`, which is onto and `~= R^x`, a simple group.
4. **The radical.**
   - Kernels of models are `1`, `K` or `G`.
   - If every model killed `K` and some model `tau o pi` were nontrivial, then `tau` would be injective,
     and `tau o iota` with the embedding `iota` of item 1 would be an injective model. That contradicts
     radical `K`.
   - So the radical is `1` or `G`. A trivial radical forces some kernel to be `1`, since intersections
     of `K`'s and `G`'s contain `K`.

### 14.3 Route `cohn-el3-two-root-identity-from-jacobson-rank-radical`: PASS as a conditional route

- **The head survives the embedding.** The Jacobson head `x_13(1 - ST)` maps to
  `x_13(1 - s_0 t_0) != 1` in `G`.
- **The radical is `G`.** If every model of `EL_3(J)` kills that head (the open Jacobson claim), then no
  model of `G` is injective, so the radical is `G`.
- **Conclusion.** Every model is trivial, and the identity follows.

## 15. Family SUB: w4-sub-adversary (93e48b681d, cc7fef520a)

### 15.1 `locally-finite-hnn-data-allow-independent-cylinder-defects`: PASS

1. **Intertwiners.** `K_(n,u) = H_n ∩ u^-1 H_n u` is a subgroup, and `phi_u` is injective.
   - Left multiplication by `K_(n,u)` and by `phi_u(K_(n,u))` is free on `H_n`, with the same number
     of orbits.
   - `pi(k x_l) = phi_u(k) y_l` is a bijection.
   - `pi lambda(k')(k x_l) = phi(k'k) y_l = lambda(phi(k')) pi(k x_l)`.
2. **Exact relations at large stages.** For `k` in `K_u`, both `k` and `u k u^-1` lie in `H_n` for
   large `n`.
3. **Free profile.** `F_2[H_n]` is free over `F_2[Q]`.
4. **Fixed vectors.**
   - Inside `im(x_n)`, the `lambda_n(H_m)`-fixed vectors have codimension at most
     `sum_(h in H_m) rank((lambda_n(h)-1) x_n) = o(|H_n|)`.
   - `Fix(lambda_n(H_m))` has normalized dimension `1/|H_m|`, one line per free summand.
   - So `rk x <= 1/|H_m|` for every `m`.
5. **Corollary 2.1.**
   - `Q_i ~= D_8`; the factors commute and meet trivially.
   - Ranks multiply over the tensor decomposition.
   - The value `3/8` was recomputed in Section 3.1, and `rk(x+1) = 4/8`.
6. **Corollary 2.2 (firewall).** Inputs 1 to 3 hold in `sigma`, and there `theta = 1`.

### 15.2 `leavitt-right-child-frames-generate-infinite-order-units`: PASS, with a naming correction

1. **Proposition 3.1.**
   - Units of `R` inside `M_(2^n)(F_2)` are invertible there: a non-invertible matrix has a nonzero
     right annihilator, which a unit of `R` cannot have.
   - Ternary words of length `k` give `3^k` leaves inside `A`. Complete codes refine the frame and
     nine-leaf units into leaf units.
   - With `l >= |A| + 2k` there are `2^(l-|A|) >= 4^k > 3^k` subcylinders of `A`, so `w` exists.
   - Conjugates of leaf units are degree-zero matrix units, and `1 - S[A]T[A]` becomes
     `1 - sum S[beta]T[beta]` in `R_0`.
2. **Proposition 4.1(1).**
   - `sigma S[A10] = S[A110]`, `tau S[A110] = tau S[A11] s_0 = S[A100]`, so `b S[A10] = S[A10] s_0`.
   - If `b^n = 1`, then `s_0^n = 1`, and `t_1 = t_1 s_0^n = 0`, which is false.
   - **Images.** `A10 -> A100`, `A110 -> A11`, `A111 -> A101`.
   - **CORRECTION.** This map does not preserve order, so `b` lies in `V` but not in `F`. It is
     `x_0` on `A1` (`A10 -> A100`, `A110 -> A101`, `A111 -> A11`), followed by the exchange of `A101`
     and `A11`. Infinite order, and the conclusion that the frames at `A` and `A1` fit in no locally
     finite subgroup, are unaffected. "A first generator of Thompson's F" should read "an element of
     `V` of infinite order, `x_0` on `A1` composed with a leaf exchange".
3. **Proposition 4.1(2).**
   - `m = (1 + e_1) + d_1` with `d_1 = (1 + e_1) e_2` of degree 1, so the degree-`n` part of `m^n` is
     `d_1^n`.
   - `d_1 S[A0] = S[A10] + S[A0] s_0` and `d_1 S[A10] = 0`.
   - By induction `d_1^n S[A0] = S[A10] s_0^(n-1) + S[A0] s_0^n`, and `T[A0]` times it is `s_0^n != 0`.
   - I also expanded `((1+a)b)^n` directly and got the same degree-`n` word pair.
4. **Proposition 4.1(3).**
   - Each positive root monomial `S[P]T[Q]` maps its source region to strictly smaller lexicographic
     potential.
   - So products of more than 9 generators vanish, the algebra of monomials is finite and nilpotent,
     and `1 + B` is a finite group containing the roots.

## 16. Family SUB: w4-sub-weyl, second node

### 16.1 `finite-subgroup-data-cannot-force-defect-submultiplicativity`: PASS

- **Well-defined.** With `F_2[K'] = ⊕_x F_2[K] x` over right cosets, `alpha F_2[K'] = ⊕ alpha F_2[K] x`,
  so the ratio does not depend on `K'`.
- **A rank model on each locally finite subgroup.** As in Section 15.1(4).
- **Conjugation invariance.** Conjugation is an algebra isomorphism between finite-subgroup algebras.
- **The kernel count.** `dim ker((1+y)(1+x)) = 4 + dim((1+x)F_2[D_8] ∩ (1+y)F_2[D_8])`, because
  `ker(1+y) = im(1+y)`. It equals 5, which agrees with rank 3 (Section 3.1).
- **Scope.** This is a rank assignment, not one model of `R^x`. The node says so. It is consistent
  with Section 15.1, which is a single HNN model.

## 17. Family SUB: w4-cohn-el3, Section 4 (cbe5dceaf7)

### 17.1 `thompson-v-lifts-into-rank-four-cohn-elementary-group`: PASS

1. **The lift.**
   - Prefix replacements preserve `E` (sequences ending in `0^inf`), and each is `w 1 0^inf` or `0^inf`.
   - For `nu_i z 1 0^inf -> mu_i z 1 0^inf`, `phi(g) delta_(nu_i z) = delta_(mu_i z) = s_(mu_i) t_(nu_i) delta_(nu_i z)`
     in the Toeplitz representation.
   - The exceptions are the internal nodes `w`, proper prefixes of the `nu_i`, together with `delta_empty`
     of the second copy. Those are finitely many basis vectors.
   - The correction is a finite combination of `s_alpha q t_beta`, `s_alpha q`, `q t_beta` and `q`.
   - Faithfulness gives a homomorphism, `pi` kills the corrections, and `pi phi = diag(g,1)` is injective.
2. **Whitehead.** `[A,B] (+) 1_2` lies in `E_4(S)` for any ring, and `V` is perfect.
3. **Rank four.** The Section 14.2 argument with four rows goes through: `ker pi = K_4`, which is
   simple with trivial centralizer, and `EL_4(R) = GL_4(R) ~= R^x` is simple.
4. **Ordering.**
   - **V gate.** It kills `phi(V) (+) 1`, which meets `K_4` trivially, so the kernel is `G_4`.
   - **Cohn `EL_3`.** A nontrivial model of `G_4` yields an injective one, and its restriction to
     `EL_3(C_2)` is nontrivial.
   - **`R^x`.** `G_4 <= EL_4(R) ~= R^x` through the embedding of Section 14.2, and nontrivial models of
     the simple `R^x` are injective.

## 18. w4-upg-audit (0bd1b6b05f, f03a707081)

### 18.1 `regular-rank-ring-compressors-conserve-fixed-right-ideals`: PASS

**Part 1: the rank bound.**
- **Setup.** `Fix_r(sigma(Gamma)) = ∩_s A_s`, a finite intersection of principal right annihilators,
  so it is principal, `= eU`.
- **Rank of `(1-e)x`.** The right annihilator of `1-e` is `eU`. Fact 1.1(d) on `xU + eU`, which
  contains `eU`, together with modularity gives `rk((1-e)x) = rk J - rk(J ∩ eU)` for `J = xU`.
- **Rank of `(sigma(s)-1)x`.** The same argument gives `rk((sigma(s)-1)x) = rk J - rk(J ∩ A_s)`.
- **Combining.** Inside `J`, `rk(I ∩ I') >= rk I + rk I' - rk J`, and iterating over `S` gives the bound.

**Part 2: normal closure.**
- **Invariance.** `g Gamma g^-1 <= Gamma` gives `eU <= sigma(g) e sigma(g)^-1 U`. The two idempotents are
  conjugate, so the ranks are equal, and faithfulness makes the ideals equal.
- **Pointwise fixing.** `sigma(g gamma g^-1) y = y`, since `sigma(g)^-1 y` lies in `eU`.

### 18.2 `corner-defect-killing-rank-functions-are-augmentation`: PASS

This rests on established inputs I did not re-derive here: [SYL] Theorem 1 and [DI] Theorem 1.1.
- **Pullback.** `iota_P` is an injective unital endomorphism of `F_2[R^x]`, so `rk o iota_P` is a
  Sylvester rank function, and it kills `D`.
- **[SYL] Theorem 1.** It gives the augmentation rank, so `iota_P(R^x) <= N_rk`.
- **`N_rk` is a normal subgroup.**
  - `rk(1 - gh) <= rk(1-g) + rk(1-h)`;
  - `rk(1 - x g x^-1) = rk(1-g)`.
- **Simplicity.** It gives `N_rk = R^x`, so every `alpha` is congruent to `epsilon(alpha)` modulo the
  null ideal.
- **Pullback consequence.** For a faithful target, pulling back `rk_U` shows that the corner product
  vanishing forces `sigma(g) = 1`.

### 18.3 `leavitt-defect-descent-chain-holds-in-regular-rank-rings`: PASS as a transfer

I checked every step of Section 8 (my verification of [DG]) against the regular setting.

**Unchanged steps.**
- Fact 1.1 (regular rings).
- Facts 1.2 and 1.3.
- Lemmas 2.1 and 2.2.
- Theorem 3.1.
- Proposition 4.1.

**Replaced steps.**
- **Principal fixed ideal:** Theorem 2.2(1).
- **Globality:** Corollary 2.4, which consumes Theorem 2.2.
- **Corners:** Lemma 2.1(1). `x = x(eye)x`, and `rk/rk(e)` is faithful.
- **Compactness.**
  - Lemma 2.1(2) gives a product of regular rings modulo the null ideal of `rk_omega`: regular,
    faithful, characteristic two, with units mapping to units.
  - `rk_omega(D_1000) = 0` gives `D_1000 = 0`, and then Proposition 1.1, through the pullback, makes
    `sigma` trivial.
- **The infimum `c_*'`** is over the whole class, which contains the corner models.

**Scope.** [DP] Theorem 1.2 was verified by w3-vf-linear, and its steps are ring algebra plus principal
ranges.

**Consequence 3.2.** `delta^2 - 2 eps delta <= f(2) <= theta delta^2` gives `(1-theta) delta <= 2 eps`,
which contradicts `delta >= c_0'`.

### 18.4 `sylvester-rank-functions-have-a-uniform-two-root-defect-gap`: PASS

- **Independence of `P`.** `iota_B(D) = [u] iota_A(D) [u]^-1` for `u` in `V`, and rank is
  conjugation-invariant.
- **Compactness.**
  - The Sylvester axioms are closed conditions on bounded values, so the space of such rank functions is
    compact in the product topology.
  - A limit point keeps `rk(1 - [g_i]) >= eta`, and has `rk(iota_P(D)) = 0`.
  - Proposition 1.1 then contradicts it.
- **Remark 4.2 (convex combinations).** They force `c^Syl(eta) -> 0`. Correct.

## 19. Family SUB: w4-sub-halving, second node

### 19.1 `disjoint-root-halves-row-plus-column-rank-at-most-three-rho`: PASS

1. **Lemma 4.1: subproducts.**
   - With all `2k` cylinders disjoint, every cross term `S[C_i]T[C'_i] S[C_j]T[C'_j]` vanishes, so the
     product is `1 + sum S[C_i]T[C'_i]`.
   - Put `C_i -> D w_i` and `C'_i -> D' w_i` for a complete code `(w_i)`, and send the complement to
     the complement.
   - The conjugate is `1 + S[D](sum s_(w_i) t_(w_i))T[D'] = 1 + S[D]T[D']`, so the displacement is `rho`.
2. **Kernels of sums.** `(1+a)(1+b) - 1 = a + b + ab = (1+a)(a+b)`, so `rk(a+b) = rho`.
3. **Theorem 4.3: row plus column rank.** Put `K = r.ann(a+b)`, of rank `1 - rho`.
   - For `x` in `K`, `ax = bx` in characteristic two, so `ax` lies in `aM ∩ bM`.
   - The kernel of `x |-> ax` on `K` is `r.ann(a) ∩ r.ann(b) = r.ann(Ma + Mb)`, of rank
     `1 - rk(Ma+Mb)`.
   - The image rank is at most `2 rho - rk(aM + bM)`, by modularity.
   - Rank additivity gives `rk(aM+bM) + rk(Ma+Mb) <= 3 rho`.
4. **Corollary 4.4: independent halves.** The two lower bounds give `4rho - 2rho^2 - 2eta <= 3rho`,
   so `rho(1 - 2rho) <= 2 eta`.
5. **Proposition 4.5: near-minimal displacement.**
   - **Faithfulness.** The argument of Section 13.1 carries over with displacement in place of defect.
   - **Row sum.** `K = r.ann(b)` is invariant under the cylinder group of `a`, which is disjoint from
     `b`'s support. So `rk(aK) = rk(Ma + Mb) - rho` and `rk(aK) >= rho_*(1 - rho)`. That gives
     `rk(Ma+Mb) >= 2rho - rho^2 - eps rho`.
   - **Column overlap.** Item 3 then gives `rk(aM ∩ bM) >= rho - rho^2 - eps rho`.
   - **Product.** Faithfulness at `Z = b` gives `rk(ab) <= rho^2 + eps rho`.

## 20. w4-defect-cov (2960587575, 6d29d4abcb)

### 20.1 `binary-locally-finite-hnn-models-violate-two-root-identity`: PASS

- **Intertwiners.**
  - `F_2[Lambda_j]` is free of rank `[Lambda_j : Gamma]` over `F_2[Gamma]` through `a |-> lambda_j(a)`,
    and also through `a |-> lambda_j(g a g^-1)`.
  - Free modules of equal rank are isomorphic, which gives an invertible `X_j` with
    `X_j lambda_j(a) = lambda_j(g a g^-1) X_j` on `Gamma_(i(j))`.
  - Since `i(j) -> infinity`, `[X_j]` intertwines on all of `B_g`.
- **The defect.** `ba F_2[D_8] = span{v_1, v_2, v_3}` (Section 3.1). `bab = v_1 + v_2`, and I computed
  `abab = 1 + x + y + xy + yx + xyx + yxy + z = v_2 + v_3`. So `span{ba, bab, abab}` has dimension 3,
  and the rank is `3/8`.
- **Scope.** Letters carry only partial-conjugation relations, with no torsion and no multi-letter
  relations. The consequence as stated is correct. It agrees with Section 15.1, which is the same model
  in permutation form.

### 20.2 `swap-group-cylinder-lift-trees-halve-but-never-refine`: PASS

**Lemma 3.1.**
- **(a)** `u^2 = 1 + s_0 (t_1 s_0) t_1 = 1`.
  - Through `r |-> (t_i r s_j)`, `u = [[1,1],[0,1]]`, `v = [[1,0],[1,1]]`, and `c = [[1,1],[1,0]]` of
    order 3.
  - `s s_0 = s_1` and `t_1 s = t_0` give `s u s = v`.
- **(b)** `u c u = uv = c^-1 = c^2`, and `(1+c+c^2)^2 = 1 + c^2 + c` in characteristic 2.
- **(c)** On the `e`-block, `c` becomes `1`, so `v = cu = u` and `p_i = 1 + u + u + u^2 = 0`. On
  `M_2(F_2)`:
  - `I + (u+v) + uv = [[1,0],[0,0]]`;
  - `I + (u+v) + vu = [[0,0],[0,1]]`;
  - `p_0 + p_1 = uv + vu = c^2 + c = 1 + e`.
- **(d)** `ev(p_0) = 1 + (s_0 t_1 + s_1 t_0) + (1 + s_0 t_1 + s_1 t_0 + s_0 t_0) = s_0 t_0`, and
  `I + c + c^2 = 0` over `F_2`.

**Theorem 3.2.**
1. **Split and covariance.** The linear extensions give the orthogonal split and covariance.
2. **Ranks.** `sigma(iota_w(s))` exchanges the halves, and ranks add over orthogonal idempotents.
3. **Positivity.** Simplicity makes `sigma` injective. If `E_w = 0`, then `sigma(c_w)^2 = sigma(c_w)`,
   so `sigma(c_w) = 1`, a contradiction.
4. **Evaluation.** `ev(iota_w(p_i)) = S[w] s_i t_i T[w] + 4(1 - S[w]T[w]) = 1_[wi]`, and
   `ev(iota_(wi)(1+e)) = S[wi](c + c^2)T[wi] + 2(...) = 1_[wi]`.
5. **Subadditivity.** It gives `rk(A_(wi) - E_(wi)) >= eps - eps/2`.

## 21. w5-c3-signed-thompson (c4f44ada52)

### 21.1 `signed-thompson-z-moving-rank-functions-match-v-rank-functions`: PASS

**Lemma 1.1.**
- **Group law.** `phi(tau_C)` flips the first letter exactly when the tail lies in `C`, and `phi(g)` acts on
  the tail. Both are prefix replacements.
- **Conjugation.** `phi(g) phi(tau_C) phi(g)^-1 (eps x) = (eps + 1_(gC)(x)) x = phi(tau_(gC))(eps x)`.
- **Products.** Over `F_3`, `(1 - 2P_C)(1 - 2P_(C'))` equals `1 - 2P_(C Δ C')`, since `4 = 1`. `phi` respects
  this because flips add mod 2.
- **`z`.** `phi(z) = sigma_0`.

**Equivalence (2) ⟺ (3).** `N_rk ∩ V` is normal in the simple group `V`, so it is `1` or `V`.

**Implication (1) ⟹ (2).** Suppose `V <= N_rk`.
- `g tau_A g^-1 = tau_(gA)`, and `[g, tau_A] = g (tau_A g^-1 tau_A^-1)` lies in `N_rk`, so `tau_(gA)` and
  `tau_A` are congruent.
- Transitivity of `V` on proper clopen sets gives one class `c`.
- `tau_[0] = tau_[00] tau_[01]`, by orthogonality, so `c = c^2` and hence `c = 1`.
- Then `z = tau_[0] tau_[1]` lies in `N_rk`.

**Implication (3) ⟹ (1).** Pull back along the unital map `K[phi]`. The result moves `z`, because
`rk(1 - sigma_0) > 0`.

**The wiring checks.**
- **`refuted_by`.** Both entries are consistent: the two open claims are negations of each other, and
  soficity implies non-augmentation.
- **`ternary-units-kill-minus-one-via-thompson-v-augmentation`.** Restriction still moves `z`, then
  direction (1) ⟹ (2), then contradiction. PASS as a conditional route.
- **`thompson-v-ternary-nonaugmentation-rank-function-from-soficity`.**
  - A cycle of length `l >= 2` gives `rank(P - I) = l - 1 >= l/2`, so `rank(P - I) >= m/2`.
  - Asymptotic freeness then gives rank at least `1/2`.
  - PASS as a conditional route.
- **Section 4.4.** A detecting rank function pulls back to a `z`-moving one, and in characteristic `!= 2` it
  compresses to `eps_-`. The swap makes `N(q_[0]) = 1/2`, so `c' q_[0] b' = eps_-` would force
  `1 <= 1/2`. This agrees with w3-corner-crossed's rank-function obstruction.

## 22. w5-c3-submult (5281756de8)

### 22.1 `anti-central-sofic-data-cannot-force-defect-submultiplicativity`: PASS

- **Lemma 1.2.**
  - `F_3[K'] eps_- = ⊕_c F_3[K] eps_- c`, with `dim = |K|/2`.
  - Conjugation fixes `eps_-`.
  - `(1-z) eps_- = 2 eps_-` has full rank.
- **Proposition 1.3(c): the Heisenberg count, re-derived independently.**
  - `L_y e_(i,j,k) = e_(i,j+1,k-i)`, and orbits are labelled by `w = k + ij`.
  - `X^2 = 1 + L_x + L_x^2` sends `f_(i,w)` to the indicator of `d + ib = w`.
  - The kernel is `sum_i p_i(d + ib) = 0`. With `p_i = alpha_i + beta_i t + gamma_i t^2`, the six monomials
    give 2 dimensions for `alpha`, 1 for `beta`, and 0 for `gamma` (Vandermonde).
  - So `dim(XM ∩ ker Y) = 3`, and `rank(YX) = 18 - 3 = 15` in `27` dimensions, which is `5/9`.
  - The same count on `F_2[D_8]` gives `4 - 1 = 3`.
- **Proposition 1.3(d).** The frames commute and meet trivially, the 3-group product avoids `z`, and tensor
  ranks multiply.
- **Theorem 2.1.**
  - The letters satisfy `phi_u(z) = z`, so intertwiners between the free `F_3[Gamma_i] eps_-`-modules of equal
    rank `[K_n : Gamma_i]` preserve the `eps_-`-part.
  - The index moves along the stages.
  - Lemma 0.1 gives no fixed vectors.
- **Theorem 2.2.**
  - `(2(1-P))^2 = 2(1-P)` over `F_3`, because `P^2 = 1`.
  - `tau(z) f = -f`.
  - Freeness on all but `o(n)` points gives `rho(f) = 1/2` and the profile.

## 23. w5-c3-descent (backlog)

### 23.1 `sylvester-rank-functions-compress-along-commuting-elements`: PASS

1. **Compression.** `(XY)'P = X'Y'P`, whose rank is at most `N(Y'P)`, and `X'Y'P = X'PY'`, whose rank is at
   most `N(X'P)`. Direct sums and triangular blocks multiply entrywise by the scalar matrix `P`.
2. **Commuting idempotents.** `U^2 = 1`, and `U diag(eP, (1-e)P) = [[eP, (1-e)P],[0,0]]`. The column
   operations use `eP = Pe` and reach `diag(P, 0)`.
3. **Frobenius.**
   - Take `col_2 - col_1 Z`, then `row_1 - X row_2`: this reaches `[[0, -XYZ],[Y, 0]]`.
   - Swapping rows and columns gives the upper triangular `[[YZ, Y],[0, XY]]`.
4. **Commuting nilpotents.** `2 a_(j+1) <= a_j + a_(j+2)`, since `x^j P x = x^(j+1) P`. Convexity with
   `a_m = 0` gives `a_1 <= (1 - 1/m) a_0`.
- **Item 5.** `N(eps_+) = 1 - N(eps_-) = 0`, so `N(X) = N(X eps_-)`.
- **Consequence in characteristic two.** `N(D_B P) <= N(N^B_12 P) <= N(P)/2` for every abstract Sylvester
  function.

### 23.2 `ternary-anti-central-two-root-defect-has-a-uniform-gap`: PASS

- **Lemma 1.4: corner locality.**
  - The pullback kills `D`.
  - In the quotient by its null ideal, the reversed-root lemma (Section 3.2) gives `N_12^2 = 0`.
  - `leavitt-rank-functions-killing-two-root-defect-are-augmentation`, stated for characteristic
    `p > 0` with both conditions, gives the augmentation rank.
  - `iota_A(G) <= K_N`, and normal subgroups are `G` or lie inside `<z>`, so `K_N = G` and
    `N(eps_-) = 0`.
- **Theorem 2.1(1).** Compactness and closedness give the minimum, and it is positive by Lemma 1.4. In
  characteristic 3 `N_12^3 = [x_12(3)] - 1 = 0`, so Lemma 1.1.4 with `m = 3` gives `N(D) <= N(N_12) <= 2/3`.
- **Item (2).** Compressing along the central idempotent `eps_-` gives an anti-central function.
- **Item (3).**
  - `tau_(X\A) = z tau_A`, so `Q_(X\A) eps_- = 2(1 + [tau_A]) eps_- = (1 - Q_A) eps_-`, because
    `-1 = 2` in `F_3`.
  - `V`-conjugation and Lemma 1.1.5 give `N(Q_A) = N(1 - Q_A) = 1/2`.
  - `Q_A` commutes with `F_3[iota_A(G)]`, and `F_3[iota_A](eps_-) = Q_A`. So the compressed function is
    anti-central, and `N(D_A Q_A) >= c_3/2`.
- **Item (4).** `A_M` is closed through the diagonal ultraproduct (Section 8.1), and `A_M ⊆ A_S`.

## 24. w5-cohn-lef (74e4783d63)

### 24.1 `cohn-pair-compression-embeds-el-2n-into-el-n`: PASS

1. **The Cohn pair.**
   - `q s_i = s_i - s_i = 0`, `t_j q = 0`, and `q^2 = q`.
   - `iota(x) iota(y) = sum s_a x_ab (t_b s_c) y_cd t_d = iota(xy)`, and `t_c iota(x) s_d = x_cd`.
   - `iota(x) q = q iota(x) = 0`.
   - So `psi_n(g) psi_n(h) = psi_n(gh)`, with `psi_n(1) = (1 - q) + q = 1`, and `psi_n` is injective.
2. **Cross-block generators.** The diagonal blocks are `1_2`, which go to `1 - q + q = 1`, and
   `iota(c E_ab) = s_a c t_b`.
3. **Same-block generators.** For `a != b`, `x_((i,a),(i,b))(c) = [x_((i,a),(j,0))(c), x_((j,0),(i,b))(1)]`.
   These are distinct indices, and `n >= 2` gives a `j`.
4. **Kernels.** `pi o psi = psi^R o pi`, where `psi^R` is the injective Leavitt isomorphism. So `K` maps
   into `K`, and complements into complements.
5. **Iteration.** Upper-left inclusion into `EL_(3·2^k)` followed by repeated compression gives
   `EL_m -> EL_3`, and `J -> C_2` (Section 14.2) gives `EL_m(J) <= EL_3(C_2)`.
6. **`V'`.** `phi(V) (+) 1_4 <= EL_6(C_2)` (Section 17.1, Whitehead). `V' ∩ K = 1` because `pi o phi` and
   `psi^R` are injective.

### 24.2 Route `cohn-coefficient-el3-two-root-identity-from-v-gate`: PASS as a conditional route

- **The kernel is normal.** `ker sigma ⊇ V' != 1`, so it is one of `1`, `K`, `G` (Section 14.2).
- **It is not `K`.** `V' ∩ K = 1`, so `ker sigma = G`.
- **Conclusion.** Every model is trivial, and the identity holds.

### 24.3 `cohn-elementary-group-is-not-lef`: PASS, with one import at statement level

1. **Matrix units in `J`.** `Q S = 0` and `T Q = 0`, so `Q T^b S^c Q = delta_bc Q`, and
   `e_ab e_cd = delta_bc e_ad` with `e_ab = S^a Q T^b`.
2. **Pigeonhole.** In characteristic two some `x_13(r)` dies, with `r = e_a0 + e_(a'0)` and `a != a'`.
3. **The commutator chain.**
   - `[x_13(r), x_32(1)] = x_12(r)`.
   - `[x_31(e_0a), x_12(r)] = x_32(e_0a r) = x_32(e_00) = x_32(Q)`, because `a != a'`.
   - `[x_13(1), x_32(Q)] = x_12(Q)`.
   - `[x_12(Q), x_23(1)] = x_13(Q)`.
   - All four are Steinberg relations in the indices `1, 2, 3`.
4. **The finitely presented cover.** A LEF partial embedding of the finite set of generators, relator
   prefixes and word prefixes defines `St_4(J) -> H` with `H` finite and `x_13(Q) != 1`. Steps 2 and 3 in
   `H` then contradict this.
   - **Import.** `St_4(J)` is finitely presented. That is imported at statement level from
     `steinberg-finite-presentation-and-kazhdan-theorem`, and I did not re-derive it.
5. **Subgroups.** LEF passes to subgroups, and `EL_4(J) <= EL_m(C_2)` by Section 24.1.

### 23.3 `ternary-cylinder-defect-products-descend-in-sign-sectors`: PASS

1. **Upper bound.** `N^B_12` commutes with `P_k`, since the cylinders are disjoint, and has cube `0`.
   Lemma 1.1.4 gives `f(k+1) = N(N^B_23 N^B_12 P_k) <= N(N^B_12 P_k) <= (2/3) f(k)`.
2. **Lower bound.**
   - `Q_B` is central in `F_3[iota_B(G)]`, so `D_B Q_B P_k = Q_B D_B P_k`.
   - `E = Q_B P_k` commutes with `F_3[iota_B(G)]`.
   - Compressing along `E` gives `N'(eps_-) = N(Q_B Q_B P_k)/h_k = 1` and `N'(D) = N(D_B Q_B P_k)/h_k >= c_3`.
3. **Sector half.**
   - `tau_C = z prod tau_(A_i)`, and `[tau_(A_i)] R_s = s_i R_s`, so `[tau_C] Y = -pi(s) Y = -Y` when `pi(s) = +1`.
   - Then `Q_(C\B) Y = 2(1 + [tau_B]) Y = (1 - Q_B) Y`.
   - `u` in `V` is the identity on every `A_i` and exchanges the nonempty clopens `B` and `C\B`.
   - So `u` commutes with `P_k`, `R_s` and `eps_-`, and `u Q_B u^-1 = Q_(C\B)`.
   - Lemma 1.1.3 splits along `Q_B`, giving equal halves. Summing over orthogonal `R_s` gives
     `h_k >= N(R_+ P_k)/2`.
4. **Positivity.**
   - `h_k = 0` gives `N(Q_(Bw) P_k) = 0`, by configuration invariance.
   - `iota_B(tau_w) = tau_(Bw)`, so `N^(iota_B)_(P_k)` kills `1 - [tau_w] = 2 Q_w`.
   - `tau_w` is not in `<z>`, so the null normal subgroup is `G` and the compressed function is augmentation.
   - Hence `f(k+1) = f(k) N''(D_(w')) = 0`.
   - Conversely `f(k+1) >= c_3 h_k`.

**The open route `ternary-rank-kill-via-anti-central-defect-deficit`.** It is valid as a conditional route.
- **The mechanism.** At a minimizer `N_0`, compressing along `Q_B D_A` is anti-central (item 2), with
  defect at least `c_3` (item 2). An open deficit bound `N_0'(D) <= theta N_0(D)` would contradict it.
- **Where the gap is.** The route's validity rests entirely on that open claim delivering the bound for the
  compressed function, as the route states.

## 25. w5-commutant-distort (1139b6be43)

### 25.1 `commuting-subgroup-witnesses-cannot-distort-defect-ranges`: PASS, with a scope remark

**Lemma 1.1.**
1. `sigma(g) Z M_n(M) = Z sigma(g) M_n(M)`, so the ideal is invariant. `rk(TZ) = rk(TJ)`, since both are
   the same principal right ideal.
2. `T` commutes with `e`, so `T = eTe + (1-e)T(1-e)`, and ranks add.

**Theorem 2.1.**
- **Commuting factors.**
  - `(g-1)(h-1) = p_U (g-1) p_U p_(U^c) (h-1) p_(U^c) = 0`, so `gh = g + h - 1 = hg`.
  - An element lying in both groups equals `1`.
- **Tensor ultraproduct.**
  - Once `n` is large, `lambda_n` is exact, so the error at `(n,i)` is `lambda_n(gg') (x) (rho_i(h) rho_i(h') - rho_i(hh'))`.
  - Its normalized rank equals `rho`'s error, and `lim_(U(x)V) = lim_U lim_V` kills it.
  - Ranks of elementary tensors multiply.
- **Values.** `T = sigma_L((y+1)(x+1)) (x) 1` has rank `3/8`, and `T (1 (x) Y) = sigma_L(alpha) (x) Y` has
  rank `(3/8) rk Y`.
- **Fixed points.** The codimension bound is as in Section 15.1, now with the factor `Omega^(k_i)`, and
  `Fix(lambda_n(H_m)) (x) Omega^(k_i)` has normalized dimension `1/|H_m|`.

**Scope remark.**
- **Trivial `rho`.** The theorem holds for any rank model `rho`, the trivial one included. There every
  witness is a scalar, and the statement says nothing.
- **Where the content is.** It comes from a `rho` that separates `Lambda`, as in Corollary 2.2: cyclic
  permutation stages for `<b>` and for `<x^A_12(s_0) x^A_21(1)>`, or sofic, amenable, residually finite or
  `F_2`-linear sofic subgroups.
- **The whole complement.** For `Lambda = G_(U^c) ~= R^x`, a separating `rho` is the gate itself. Section 3,
  item 2, already says this.

**Remark 2.3.** In `F_2[C_2 x C_2] = F_2[s,t]/(s^2, t^2)`, `sM + tM = (s,t)` has dimension 3 of 4. So the
row-plus-column bound is attained: `3/4 + 3/4 = 3 · (1/2)`.

## 26. w5-regular-rankfn (ebede0e17d, ca4ff63cb5)

### 26.1 `sylvester-rank-functions-descend-to-quotients-and-compressions`: PASS

**Lemma 1.1: ideal quotients.**
- **The matrix `Y_A`.** `J` is two-sided, so `x_i a_pq = sum_j y x_j`, giving `X A = Y_A X` with sizes
  `km x kn` times `kn x n`.
- **(S2).** `rho(X AB) = rho(Y_A X B) <= rho(XB)`, and `rho((XA)B) <= rho(XA)`.
- **(S3) and (S4).** The block `i` of `X(A ⊕ B)` is `x_i A ⊕ x_i B`. Permuting rows gives `(XA) ⊕ (XB)`,
  and the triangular case is the same.
- **Independence.** It follows from mutual domination of the generating columns.
- **`J = J^2`.** Then `J^2 = sum_(i,j) S x_i x_j`, so `X = Y(XX)`.
  - One direction: `rho(XZ) <= rho(XXZ)`.
  - The other: `XXZ = (X (x) I)(XZ)`, so `rho(XXZ) <= rho(XZ)`.
  - Hence `rho_J(XZ) = rho(XXZ)/rho(X) = rho_J(Z)`.

**Lemma 1.2.** Same as Section 23.1.

**Sylvester inequality.**
- `col_2 - col_1 B`, then `row_1 - A row_2`, carries `[[A,0],[I,B]]` to `[[0,-AB],[I,0]]`.
- Swapping rows and then columns gives the triangular `[[B,I],[0,A]]`.

**Frobenius.**
- `col_2 - col_1 C`, then `row_2 - A row_1`, carries `[[B,BC],[AB,0]]` to `[[B,0],[0,-ABC]]`.
- Swapping columns gives `[[BC,B],[0,AB]]`.

**Stacking.** `[A;B] = (A ⊕ B)[I;I]`.

### 26.2 `perfect-group-augmentation-quotient-ranks-are-fixed-point-free`: PASS

**Lemma 2.1.**
- `gh - 1 = g(h-1) + (g-1)`.
- `h |-> h - 1 mod omega^2` is a homomorphism with spanning image and abelian target, so a perfect group
  gives `omega = omega^2`.
- `rho(X) = 0` kills every `1 - [h]`.

**Corollary 2.3.** `rho_omega(X) = rho_omega(I_1) = 1`, and stacking gives `max >= 1/r`.

**Proposition 3.1.**
1. **Right translates.** `B omega_Gamma B` contains `n - 1` for the normal closure. Expanding `c` gives
   finitely many right translates.
2. **Invariance.** For `h` in `P_Gamma`:
   - `X_(hSh^-1) = Y_h X_S = (h (x) I) X_S h^-1`, so `rho(Y_h X_S) = rho(X_S)`.
   - Frobenius with `(Y_h, X_S, Z)` gives `rho(X_S Z) <= rho(Y_h X_S Z) <= rho(X_S Z)`.
   - So `rho(X_S Z) = rho(X_S h^-1 Z)`. The invariant `h` form a group containing `P_Gamma`.
   - This holds for every `psi`.
3. **Density.** `psi(Z) = psi(XZ) <= sum_j psi(X_S h_j Z)`.

### 26.3 `sylvester-leavitt-defect-gap-and-geometric-descent`: PASS

**(1) Gap.**
- `rho_omega` is non-augmentation and displaces some generator by at least `1/4`.
- The uniform gap (Section 18.4) gives `c_0`.
- `(N^A_12)^2 = 0` and the Sylvester inequality give `2 rho(N) <= 1`.

**(2) Descent.**
- **Conjugation invariance.** `X u = (u (x) I)(u^-1 X u)`, and `u^-1 X u` is again a generating column of
  `omega`, so `rho_omega` is conjugation invariant.
- **Compression along `P`.** `tau = (rho_omega)_P o iota_B`, and `tau(D_1000) = f(k+1)/f(k)`, since the
  tuple `(A_i, B1000)` has proper union.
- **Upper factor.** `tau(N^1000_12) <= 1/2`.
- **Lower factor.**
  - `iota_B(X) = X_(S_B)`. Proposition 3.1(3), for `psi = rho_omega` and `Gamma_B` (a conjugate of
    `Gamma_0`, with the same `m_0`), gives `tau(X) >= 1/m_0`.
  - (S2) gives `tau(E) >= tau(XE) = tau(X) tau_omega(E) >= c_0/m_0`.

**Inputs taken as established, not re-derived here:** that the compression semigroup of `Gamma_0` generates
`R^x` (the rigid-defect and packet nodes), and simplicity.

## 27. w5-c3-outside

### 27.1 `leavitt-prime-field-units-generated-by-v-and-one-transvection`: PASS

1. **Elementary generators.** `psi: e_ij (x) r |-> s_(alpha_i) r t_(alpha_j)` is an isomorphism, and
   `GL_3 = EL_3` (the internal Lean theorem, Section 1.1).
2. **Monomials.** `s_(alpha_i) s_mu t_nu t_(alpha_j) = s_(alpha_i mu) t_(alpha_j nu)`. The words start with
   different codewords, so they are incomparable.
3. **Splitting.** `s_sigma t_kappa = sum_w s_(sigma w) t_(kappa w)`. `t_(kappa w) s_(sigma w') = 0` for
   incomparable `kappa w, sigma w'`, so the factors commute and square to zero.
4. **Conjugation.**
   - `t_c s_sigma = delta_(c,sigma)` inside the code `C`, so `g s_sigma t_kappa g^-1 = s_00 t_01`.
   - If `[sigma] ∪ [kappa] = X`, then `{sigma, kappa} = {0,1}`, and one split gives proper unions.
5. **Prime fields.** `T(λ) = T(1)^λ`.
6. **Proposition 1.3.**
   - `tau_[kappa] s_sigma = s_sigma` and `t_kappa tau_[kappa] = -t_kappa`, so `T_(sigma,kappa)(1)` is
     conjugate to `T_(sigma,kappa)(-1)`, and the other factors are fixed.
   - One `V`-element sends the chosen pairs to `(00w_i, 01w_i)`. The product is `x` by step 3.

### 27.2 `leavitt-semisimple-torsion-units-conjugate-iff-same-support`: PASS

1. **Spectral idempotents.** `char K ∤ m` makes `x^m - 1` separable, so there are orthogonal `e_q(g)`
   summing to 1.
2. **Module structure.** `P_q = e_q(g)R` is a `(K_q, R)`-bimodule, with `K_q` acting through `g`, so it is a
   right `R_q = K_q (x)_K R ~= L_(K_q)(1,2)`-module.
   - It is finitely generated and `R`-projective, being a summand of `R_R`.
   - `K_q/K` is separable, so `R_q` is a separable `R`-algebra, and an `R`-projective `R_q`-module is
     `R_q`-projective.
3. **Freeness.** `binary-leavitt-nonzero-projectives-are-free` over the field `K_q` gives `P_q ~= R_q`.
4. **The conjugating unit.**
   - Put `φ = ⊕ φ_q`, an automorphism of `R_R`, so `φ` is left multiplication by the unit `u = φ(1)`.
   - `φ(g e_q p) = g' φ_q(e_q p)` summed over `q` gives `ug = g'u`.
5. **Corollaries.**
   - **(1) Square roots of `z`:** `g^2 = -1` gives support `{x^2+1}`.
   - **(2) Involutions:** support `{x-1, x+1}`.
   - **(3) Order 8:** `x^4 + 1 = (x^2+x-1)(x^2-x-1)` over `F_3` checks. The claim that every signed
     permutation unit with fourth power `z` has spectrum closed under negation was not re-derived here.
     Only the node's main theorem is certified.

### 27.3 Route `v-augmentation-from-minus-one-gate-and-extension`: PASS as a conditional route

- **Setup.** A non-augmentation function on `F_3[V]` detects every nontrivial element, since `V` is simple.
- **The two open inputs.** The open extension claim would give `rk(1 - [z]) > 0` on `F_3[G_3]`, which
  contradicts the open minus-one gate.
- **Attempts section.** Its "no homomorphism `G_3 -> V`" step imports the Haagerup property of `V` from the
  literature, as the node states.

**Addendum to 27.2, corollary (3), now re-derived.** Take a signed permutation unit `a = tau v`, with `tau` in `E` and
`v` in `V`, such that `a^4 = z`.
1. **Every orbit has length 4.** `a^4` lies in `E`, so `v^4 = 1`. On a `v`-orbit of length 1 or 2 the sign of
   `a^4` is a square, hence `+1`, while `z` acts by `-1`. So every point has orbit length exactly 4.
2. **Choice of `A`.** The free action of `<v>` on the Cantor set has a clopen fundamental domain `B`. Put
   `A = B ∪ v^2 B`. Then `vA = X \ A`.
3. **Conjugation.** `tau_A a tau_A = tau tau_A tau_(vA) v = tau z v = -a`.
4. **Conclusion.** `S(a)` is closed under `x |-> -x`, which exchanges `p_+` and `p_-`. So `S(a) = {p_+, p_-}`,
   and the corollary holds.

## 28. w5-sub-fock (2cf82d01d7, 0d600e4efd)

### 28.1 Proposition 1.1: the Toeplitz pair is finite-subgroup data. PASS

- **(a)** In characteristic two `X^2 = x_12(2 t0) = 1`. `[X,Y] = x_13(t0 s0) = x_13(1)`, and for involutions
  `[X,Y] = (XY)^2`, so `XY` has order 4.
- **(b)** The `(1,3)` entry of a product is `a_13 + b_13 + a_12 b_23`, and `span(1,t0) span(1,s0) = span(1, s0, t0)`
  since `t0 s0 = 1`. The grading puts `1, s0, t0` in degrees `0, +1, -1`, so they are independent and the order is
  `128`. The generators are `x_13(s0) = [x,Y]`, `x_13(t0) = [X,y]` and `x_13(1) = [x,y]`.
- **(c)** It is a regular module, and the free count gives `3/8`.

### 28.2 `sofic-subgroups-carry-independent-cylinder-defects`: PASS

1. **The model.** Permutation matrices of the sofic approximation give a homomorphism into the rank
   ultraproduct.
2. **Freeness.**
   - Keep the points where the finitely many identities of `K` hold at every point of their `K`-trajectory and no
     nontrivial element fixes the point. This set is invariant, has `n_i - o(n_i)` points, and carries an honest
     free action.
   - Rank on a free module of rank `m` is `m dim(alpha F_2[K])`.
3. **Defects.** Disjoint frames commute and meet trivially, `F_2[D_8^k]` is a tensor product, and
   `dim(D F_2[D_8]) = 3`, which gives `(3/8)^k`.
4. **Fixed vectors.**
   - For `l <= N`, `phi_i(g)^l = phi_i(g^l)` off `o(n_i)` points, and `phi_i(g^l)` has `o(n_i)` fixed points. So
     only `o(n_i)` points lie on cycles of length at most `N`.
   - Over `F_2`, `dim Fix` equals the number of cycles, which is at most `n_i/N + o(n_i)`, so the normalized rank of
     the fixed space is at most `1/N`.
5. **Scope.** Relation-only arguments. The global gap and near-minimal inputs are not covered, as stated.

### 28.3 `toeplitz-pair-and-weyl-elements-generate-jacobson-el3`: PASS

- **One coefficient set.** Each `C_ij` is additive, and signed permutations conjugate `x_ij(r)` to
  `x_(pi(i)pi(j))(±r)`, so there is one set `C`, closed under negation.
- **Products.** `[x_ij(a), x_jk(b)] = x_ik(ab)`.
- **(a)** `C` contains `1, s0, t0`, so `C ⊇ J`, and the generators lie in `EL_3(J)`.
- **(b)** `p = s0 t1 + s1 t0` lies in `R_0`, with `p s0 = s1` and `t0 p = t1`. So `C = R`, and
  `G' = EL_3(R) = R^x`.
- **`F_3`.** The same argument works, because `EL_3(F_3)` contains the signed permutations.

## 29. w6-mismatch-c2 (d0f2b3f648)

Artifact `mismatched-factor-graph-of-groups-firewall-2026-09-12.md`. Every step was re-derived.

### 29.1 `graphs-of-locally-finite-groups-carry-regular-rank-models`: PASS

- **Stages.** `K_(n,e)` is a subgroup, and each finite subset of `K_e` lies in it eventually. `|H_(n,v)|` divides
  `N_n`, so free actions exist.
- **Forest.** Both `K_(n,e)`-sets are free with `N_n/|K_(n,e)|` orbits, so `beta` exists. Transporting by
  `beta^-1` gives `lambda_w(phi_e(k)) = beta^-1 phi_e(k) beta = lambda_v(k)`. `F cap Y_n` is a forest, so the
  induction closes.
- **Letters and limit.** Orbit matching gives the intertwiners. Each relation of `pi_1(Y)` holds exactly at almost
  every stage, so `sigma` is a homomorphism.
- **(1)–(3).**
  - The free profile comes from `F_2[Omega_n] = F_2[Q]^(N_n/|Q|)`.
  - Nontriviality needs some `L_v != 1`. The artifact says so and the node leaves it implicit.
  - The fixed vectors of a free `H`-set have normalized rank `1/|H|`.
  - `M_k` of the ultraproduct is the ultraproduct of `M_(k m_n)`, and `rk(I - AB) = rk(I - BA)` at each stage.
- **Corollary 1.2.** Disjoint frames give `D_8^k <= L_v`. An involution has rank `4/8`, `D` has rank `3/8`, and
  tensor ranks multiply.
- **Scope.** Corollary 1.3 quantifies over the relations of one `pi_1(Y)` of the main case and over rank calculus.
  Global inputs are outside it, as the node states.

### 29.2 Artifact Section 2, the mismatched pair: PASS

- **Involutions and `[h,c] = 1`.** `t_1 s_0 = t_00 s_1 = t_00 s_01 = 0`, and both cross products of `s_1 t_00`
  and `s_01 t_00` vanish.
- **Infinite order.** `A = s_0 t_1 + s_1 t_00 + s_0 t_00`. All four action formulas re-checked on the Cantor-point
  module. `A^2 W_l ⊆ W_(l-1)`. Modulo `W_(l-2)`, `A^2` sends `(q_l, r_(l-1))` to `(q_(l-1), q_(l-1) + r_(l-2))`,
  which is invertible (onto `span(q_0, q_1)` at `l = 2`). So `A^(2(l-1)) != 0` on `W_l`.
- **Conjugates.** `g s_1 = s_10`, `g s_01 = s_0` and `t_00 g^-1 = t_11` give `T_(10,11)` (degree 0) and `T_(0,11)`
  (degree −1).
- **`K`.**
  - The blocks go to degrees `d_P - d_Q`, with `d = (1, 0, -1)` distinct.
  - Blocks are recovered as `t_(P') x s_(Q')`, so they cannot cancel.
  - `K` is the block-diagonal part.
- **`H`.**
  - `U` is parametrized by `(x, y)`, is elementary abelian, is normalized by `K`, and `U cap K = 1`.
  - A finitely generated subgroup has finite image in `K` and a finite-index elementary abelian part, so it is
    finite.
- **Corollary 2.2.** `h ∈ L_1 cap H`, `c ∈ H cap L_2` and `K <= H`, so `[h,c] = 1` and the identifications of `K`
  hold in `pi_1(Y)`.
- **Note on the `binary-complement-corner-has-no-weakly-finite-image` Attempts entry.** The entry omits `L_0` and
  is still correct for `A = [0]`, whose frame lies in `L_2`:
  - `g iota_[0](x_12(1)) g^-1 = 1 + s_11 t_00` and `g iota_[0](x_23(1)) g^-1 = 1 + s_00 t_01` have degree 0.
  - Two disjoint cylinders need the vertex `L_0`, as in the artifact and the other entry.

### 29.3 Section 3: PASS

- **Proposition 3.1.** A pinch would need `c ∈ R_0^x` or `T_(0,11) ∈ R_0^x`, and both have degree −1 parts. So
  Britton's lemma gives `[h, ĉ] != 1`. The statement is limited to the natural lift, as written.
- **Remark 3.2.**
  - `EL_3(R) = St_3(R)/K_2(3,R)`.
  - Each Steinberg relation holds in a subgroup of order at most 8 over `F_2`.
  - The list of three options restates the firewalls. It is a remark, and not claimed as a theorem.

## 30. w6-mismatch-c3 (74247b5cf, a5226d475)

Artifact `depth-monotone-leavitt-firewall-2026-09-12.md` (blob df157d486a). Every step was re-derived.

### 30.1 `depth-monotone-leavitt-subalgebras-are-stably-finite`: PASS

- **Grading.** Both defining relations are homogeneous for the `Z^2`-degree. So
  `span{s_mu t_nu : omega(mu) <= omega(nu)} = ⊕_(omega·n <= 0) R_n`, which is a unital subalgebra. `*` with
  `s_i* = t_i` preserves both relations and sends `s_mu t_nu` to `s_nu t_mu`.
- **Lemma 1.1.** All `S_i, T_i` formulas were re-checked. In the detection step at `x = mu_0 1 0^M 1 y'`, a proper
  prefix of `mu_0` puts the leading `1` of `w` at position `L - j + 1 ∈ [2, M+1]`, where `[w]` needs `0`.
  - An independent second proof: `L_K(1,2)` is simple and `pi(1) = id`.
- **Stopping partitions.**
  - Weight strictly increases along prefixes, so the pieces form a finite complete prefix code.
  - The partitions refine as `r` grows.
  - `1_[w] ∈ F_r` once `r >= omega(w)`.
- **Lemma 1.2.**
  - `omega(mu) <= r` forces `mu` to be a prefix of the stopping prefix `u`, so membership in `[mu]` is a function
    of `u`.
  - `u = mu v` with `v = p_(r - omega(mu))(y)`.
  - `r - omega(nu) <= r - omega(mu)` makes `p_(r - omega(nu))(y)` a prefix of `v`, so `p_r(nu y)` depends only
    on `u`.
- **Theorem 1.**
  - `phi` is eventually multiplicative, and it is injective by Lemma 1.1 and `C = ∪ F_k`.
  - `M_n(Q)` is again a product modulo a sum of finite-dimensional matrix algebras, so it is stably finite.
  - The `≥` side follows through `M_n(A^op) = M_n(A)^op`.
- **Model test.**
  - `t_0 y = 1` forces `y = s_0 + s_1 t_1 y`, whose degree `+1` part `s_0 + s_1 w_0` is nonzero, since
    `t_0(s_0 + s_1 w_0) = 1`. So `t_0` has no right inverse in `R^1_≤`.
  - Dually, `s_0` has no left inverse in `R^1_≥`.
  - Consistent with the sharpness remark.
- **Corollary 2.** Inverses lie in the subalgebra, so some `F_k` (`k >= k_0`) is invariant under `Gamma_0`, and
  `Gamma_0 -> ∏ GL(F_k)` is injective. On the `≥` side, `g -> (g*)^-1` is a group isomorphism.

### 30.2 `depth-monotone-configurations-cannot-force-ternary-minus-one`: PASS

- **Theorem 3.**
  - Over `F_3`, `eps_- = [z] - 1` is a central idempotent, and `Phi(eps_-) = 2·2 = 1`.
  - `Q != 0`, since `dim F_k >= 1` for every `k`.
  - Theorem 1(b) of the ternary artifact kills `J_omega`.
  - A certificate whose group elements, pair entries, defects and multipliers all lie in `Gamma_0` is a
    derivation inside the subring `eps_- F_3[Gamma_0]`.
  - The sofic alternative is sound (`linear-sofic-group-algebra-is-stably-finite` is ESTABLISHED on main).
- **Placement.**
  - `T_(σ,κ)(λ)^(-1) = T_(σ,κ)(-λ)` for incomparable `σ, κ`.
  - `w_0 = s_0 t_1 - s_1 t_0` with `w_0^2 = z`.
  - `A^2 = B^2 = 0`, `AB = s_0 t_00`, `BA = s_1 t_10`, `ABA = s_0 t_10`, `BAB = s_1 t_000`, and
    `(AB)^n = s_0 t_(0^(n+1))`. All have degree `<= 0`.
- **Infinite order over `F_3`.**
  - `A q_0 = q_1`, `A q_1 = 0`, `A q_n = q_(n-1) + r_(n-2)` for `n >= 2`, and `A r_m = q_(m+1)`. All coefficients
    are `+1`.
  - `A W_l ⊆ W_l`, and `A^2 = [[1,1],[0,1]]` from level `l` to level `l - 1`.
  - The Frobenius identity gives `(ac)^(3^k) = 1 + A^(3^k)`. So the prime-to-3 argument holds.
- **Remark 3.2.**
  - `Phi = phi ∘ Ad(u) ∘ ev` kills `D = N_23 N_12`, because `ev(D) = e_23 e_12 = 0`.
  - With the code `(0,10,11)`, `e_12 = s_0 t_10` has degree −1 and `e_23 = s_10 t_11` has degree 0.
  - Theorem 2 of the ternary artifact is about all of `Gamma = R^x`, so a nontrivial `Phi` with `Phi(D) = 0` only
    blocks running it inside `H^1_≤`, as stated.
- **Calibration.** Two checks against main agree with the firewall:
  - `leavitt-group-algebra-not-stably-finite` is OPEN.
  - `one-transvection-ternary-s0-lift-is-left-invertible` independently finds that its support needs
    depth-raising elements.
- **Section 4.**
  - Lemma 4.1: a nonempty `R_n`-component sends `1` to the indicator of a nonempty union of cylinders. Then Kraft
    gives termwise equality.
  - The depth-vector table: all six rows re-derived.
  - The three weight inclusions and the four-set exclusion re-checked.
  - The conjugation by `u` (`0->00`, `10->01`, `11->1`) gives `T_(01,00)` and `T_(00,01)`.

### 30.3 Precision note (forward, wording only)

- **The issue.** The Attempts entry on `ternary-leavitt-units-have-no-weakly-finite-representation` says a
  certificate's group elements "must generate a subgroup that no conjugation puts inside any weighted unit group:
  elements of V that are weight-level for no weight, or sets like {T_(0,1), T_(1,0), T_(1,00), T_(00,1)}".
- **Why it overstates.** Those are candidates. They escape every `H^omega_±` without conjugation, but no
  conjugation invariant is proved. The artifact's §4 ("obvious source") and the claim node ("escaping is not yet a
  criterion") state this correctly.

## 31. w7-el3j-sofic (58760b6ad)

Sources: artifact `jacobson-el3-soficity-firewalls-2026-09-12.md`, Sections 0–2 (blob `ecc44bd3`); claims
`jacobson-elementary-subgroups-are-locally-finite-by-linear` and `jacobson-elementary-groups-are-lea-only-if-lef`, each
with its route. Both claims landed ESTABLISHED before verification. **Verdict: PASS on both.** No corrections. Neither
verdict is decision-level: the soficity of `EL_3(J)` stays open.

### 31.1 `jacobson-elementary-subgroups-are-locally-finite-by-linear`: PASS

- **Kernel.**
  - `S^a T^b` is a basis. So `ker(J_F -> F[z,z^(-1)])` is the set of sums `Σ λ_ab S^a T^b` with
    `Σ_(a−b=d) λ_ab = 0` for every `d`. It is spanned by `S^a T^b − S^(a+1) T^(b+1) = S^a Q T^b`.
  - `QS = 0`, `TQ = 0` and `Q^2 = Q` give `E_kl E_mp = δ_lm E_kp`. For `l > m` the product contains
    `Q T^(l−m−1) (TQ) = 0`, and for `m > l` it contains `(QS) S^(m−l−1) Q = 0`.
  - An element of `L_n` and its inverse both lie in `1 + M_fin(N x n, F)`. So `L_n <= GL_fin`, which is locally finite.
- **Residual finiteness.** `z^(−m) p(z)` is a unit times `p`, and `p` is nonzero modulo `z^N − 1` once `N > deg p`.
- **Proposition 1.3.**
  - **Kernel.** `(H ∩ L_n) M / M` is a locally finite normal subgroup of a finitely generated infinite simple group, so
    it is trivial. Hence `H/M = π(H)/π(M)`.
  - **Bounded exponent.** For torsion `g` in `GL_n(F(z))`, the characteristic polynomial has coefficients in `F`,
    because `F` is algebraically closed in `F(z)`. So the semisimple part has order dividing
    `lcm_(k<=n) (q^k − 1)`, and `p^r >= n` kills the unipotent part.
  - **Zariski closure.** `x^e = 1` holds on the closure `𝐌`, so `𝐌°` contains no torus and is unipotent. `π(H)`
    normalizes `𝐌`.
  - **Two cases.**
    - If `π(H) ∩ 𝐌 = π(M)`, then `H/M` embeds in the `K`-points of the affine group `N(𝐌)/𝐌`. That group is linear,
      so `H/M` is residually finite by Mal'cev.
    - Otherwise `π(H) <= 𝐌`, and `H/M` is virtually nilpotent.
    - Both contradict simplicity.
- **Examples.**
  - **Cohn algebra.** `P = 1 − s_0 t_0 − s_1 t_1` is idempotent, with `t_i P = 0 = P s_i`. So `(P)` is spanned by the
    matrix units `s_v P t_w`, and it is the simple ring `M_fin`.
  - The kernel of `EL_3(C_2) -> EL_3(L_(F_2)(1,2))` therefore lies in `1 + M_fin` and is locally finite, while the
    quotient `R^x` is simple. Proposition 1.3 applies.
  - A torsion-free group has no nontrivial locally finite normal subgroup, so `F`, `BS(2,3)` and Higman's group are
    excluded through item 3.
- **Monolith, checked independently (consequence line only).**
  - The `x_ij(E_kl)`, `i != j`, are the finitary transvections between distinct colours. Their commutators
    `[1 + e_xy, 1 + e_yw] = 1 + e_xw`, with `y` of a third colour, give every transvection. So
    `L = GL_fin(N x {1,2,3}, F_2)`, which is simple because `GL_fin = SL_fin` over `F_2`.
  - If `g` centralizes `L`, then `1 + gv ⊗ φg^(−1) = 1 + v ⊗ φ` for all `φ(v) = 0`. So `gv ∈ F_2 v` for every `v`,
    hence `g = 1`.
  - For a nontrivial `N ⊴ E`, `[N, L]` is a nontrivial normal subgroup of `L`, so `L <= N`. `x_13(Q) ∈ L`, and `E` is
    infinite and Kazhdan (31.2). So `E` is not residually amenable.
- **Dependency note.** The route's `requires` omits `binary-jacobson-mark-dichotomy-holds-from-rank-two` and
  `binary-jacobson-self-centralizing-kernel-proof`, which the monolith line cites. Both facts are re-derived above, and
  the monolith is not a Statement item. No change needed.

### 31.2 `jacobson-elementary-groups-are-lea-only-if-lef`: PASS

- **Property (T), rank three.** `J_F` is a quotient of `F<x,y>`, and `EL_3` of a quotient ring is a quotient group. So
  (T) comes from `elementary-group-property-t-over-free-algebras` (ESTABLISHED).
- **Rank at least four.** (T) for `EL_n(J)` follows from the Kazhdan Steinberg cover, or directly from
  Ershov–Jaikin-Zapirain for `EL_n(F_2<x,y>)`, `n >= 3`. Item 3 needs only `EL_4(J)`.
- **LEA implies LEF.**
  - A finitely generated Kazhdan group is a quotient of a finitely presented Kazhdan group `Γ` (Shalom).
  - The marked groups satisfying the finitely many relators of `Γ` form a neighbourhood, and all of them are quotients
    of `Γ`, hence Kazhdan.
  - A group that is both amenable and Kazhdan is finite.
  - Marked limits agree with local embeddability: a partial embedding of `B_r` makes words of length `<= r` trivial in
    the image exactly when they are trivial in the group.
- **Not LEA for `n >= 4`.** `cohn-elementary-group-is-not-lef` (ESTABLISHED) shows that `EL_4(J)` is not LEF, through
  the finitely presented `St_4(J)`. Block inclusion carries this to every `n >= 4`, since LEF and LEA pass to
  subgroups. So `EL_n(J)` is not LEA.
- **Scope.** The claim is about approximation classes only, and it records that sofic approximations other than
  amenable local embeddings are not excluded. It proves no triviality.

## 32. w7-el3j-sofic (07d43b6a3)

Sources: artifact `jacobson-el3-soficity-firewalls-2026-09-12.md`, Section 3 (blob `02494d50`); claim
`jacobson-one-sided-symbol-preimages-are-lef` (blob `65991c8a`) and its route (blob `4e7a07c7`). The claim landed
ESTABLISHED before verification. **Verdict: PASS.** No corrections. Not decision-level: it proves LEF for the halves,
proves no triviality, and leaves the soficity of `EL_3(J)` open.

### 32.1 `jacobson-one-sided-symbol-preimages-are-lef`: PASS

- **Item 1, structure.**
  - Over a Euclidean ring the Euclidean algorithm reduces a column to `(u, 0, 0)` by elementary moves, and
    `diag(u, u^(-1), 1)` is elementary. So `SL_3 = E_3` over `F`, `F[z]`, `F[z^(-1)]`, and over `F[z, z^(-1)]` (its
    Euclidean function is the width of the exponent range).
  - `π` is entrywise injective on `M_3(F[S])`, so `π : EL_3(F[S]) -> SL_3(F[z])` is an isomorphism. For `h in H_+`
    with `π(h) = π(d)`, `h d^(-1) in L_3`. So `H_+ = L_3 x| EL_3(F[S])`, and likewise for `H_-`. Since
    `F[z] ∩ F[z^(-1)] = F`, `H_0 = L_3 x| SL_3(F)`.
  - **Generation.** `x_ik(S^a T^b) = [x_ij(S^a), x_jk(T^b)]`, the first factor in `H_+` and the second in `H_-`.
- **Item 1, the twist.**
  - `σ(TS - 1) = σ(S)σ(T) - 1 = TS - 1`, and `σ(ST) = ST`, so `σ` descends to `J_F` and fixes `Q`.
  - Entrywise, `σ(gh)^t = σ(h)^t σ(g)^t`, so `θ(g) = (σ(g)^t)^(-1)` is a homomorphism. On generators
    `θ(x_ij(a)) = x_ji(-σ(a))`, so `θ^2 = 1` and `θ(E_F) = E_F`.
  - `π(σ(S^a T^b)) = π(S^b T^a) = z^(b-a)`, which is `π(S^a T^b)` with `z -> z^(-1)`. So `πθ = θ̄π`, and `θ̄` exchanges
    `SL_3(F[z])` and `SL_3(F[z^(-1)])`. Since `θ` and `θ̄` are involutions, `θ(H_+) = H_-`.
- **Item 2, truncation.**
  - **Faithfulness, checked.** If `x = Σ λ_ab S^a T^b` acts as zero on `V`, then on `e_k` with `k` large it gives
    `Σ_d (Σ_(a-b=d) λ_ab) e_(k+d) = 0`. So `π(x) = 0`, and `x` lies in the span of the matrix units `E_kl`, which act
    as independent operators. Hence `x = 0`.
  - `L_3 <= 1 + M_fin(N x 3, F)`. If `g - 1` has row and column support below level `N`, then `g` fixes `U_N`
    pointwise and preserves `W_N`, and so does `g^(-1) = 1 - g^(-1)(g - 1)`. These `L_(3,N)` form an increasing union.
  - Entries in `F[S]` raise the level, so `d in EL_3(F[S])` preserves `U_N`. On `U_N = F[S]^3` it acts by
    left multiplication by `d` itself. Its `W_N`-block `A` is invertible, because `d^(-1)` has the same shape.
  - **The product rule, recomputed.** With `g(w, u) = (Aw, Bw + Du)`,
    `g g'(w, u) = (AA'w, (BA' + DB')w + DD'u)`. This is block multiplication in `M_(3N+3)(F[S])`, and
    `[[A, 0], [B, D]]^(-1) = [[A^(-1), 0], [-D^(-1)BA^(-1), D^(-1)]]`. The operator determines `A`, `B` and `D`
    (`D` from `D ε_j`). So `⟨L_(3,N), EL_3(F[S])⟩` embeds in `GL_(3N+3)(F[S])`.
  - `GL_m(F[S]) -> GL_m(F[S]/(S^k))` has finite target and separates `g != 1` once `k` exceeds every degree in
    `g - 1`. A finitely generated `K <= H_+` lies in some `⟨L_(3,N), EL_3(F[S])⟩`, so it is residually finite and
    LEF. LEF is a local property, and LEF groups are sofic. `H_-` follows by `θ`.
  - **The head.** `π(Q) = 1 - z z^(-1) = 0`, so `x_13(Q) in L_3 <= H_0`. A finite quotient of `⟨Φ⟩` that is injective
    on `Φ` keeps it.
- **Item 3, proper cover.**
  - `[x_ij(a), x_jk(b)] = x_ik(ab)` with `[x, y] = x y x^(-1) y^(-1)`. Recomputed with noncommuting entries:
    `E_jk E_ij = 0`, `E_ik E_ij = 0` and `E_ik E_jk = 0` kill every other term. So `[x_12(S), x_23(T)] = x_13(ST)`,
    and `ST = 1 - Q`, with symbol `x_13(1) in SL_3(F)`.
  - `π(x_12(±S)) = x_12(±z)` is not constant, and likewise for `x_23(±T)`. So the word alternates between
    `H_+ \ H_0` and `H_- \ H_0`, and by the normal form theorem it is not in `H_0 <= P`. Its image equals that of an
    element of `H_0`, and `φ` is injective on `H_0`. So `φ` is not injective.
  - **The Toeplitz remark.** `[x_12(T), x_23(S)] = x_13(TS) = x_13(1)`, and the word alternates `H_-`, `H_+`, `H_-`,
    `H_+`. So the relation fails in `P` as stated.
- **Firewall line, checked.**
  - Over `F_2` every permutation matrix is elementary. So the constants and `x_12(z^(-1))` give all `x_ij(z^(-1))`,
    and through commutators all `x_ij(z^(-m))`. That is `SL_3(F_2[z^(-1)])`, which is infinite and Kazhdan, hence
    nonamenable. The subgroup of `H_-` is LEF by item 2.
  - Corollary 3.4's contrast, that amenable quotients of `E` kill `L`, is the monolith line of 31.1 together with
    (T) from 31.2.
  - Commit `0d600e4ef` exists.
- **Subsumption scan.** Landed nodes matching `SL_3(F[z])` or "symbol preimage" at `0a5550bed`:
  - `binary-jacobson-monomial-symbol-preimage-is-marked-mf` and `binary-jacobson-two-target-parabolic-is-marked-mf`
    concern MF characters of monomial and parabolic preimages. Neither proves LEF for a full half.
  - The OPEN `binary-jacobson-el3-is-sofic` and the Toeplitz bullet describe this claim accurately.
- **Scope.** Item 2 is a positive approximation result for subgroups. Item 3 is a structural statement. Neither says
  that rank models or finite models of `E` are trivial.

## 33. w6-v-extend (0144b771c and follow-up)

Sources:
- `research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md`: Sections 1–2 at blob `d7230199`
  (0144b771c), Sections 3–5 at blob `e104a8c5` (60501cc20). Between the two blobs Sections 1–2 are unchanged, and
  only the Summary moved.
- The OPEN target `v-detecting-rank-functions-extend-to-ternary-leavitt-units` (blob `1d1d2a8b`, 4ae2882d7),
  `w6-v-extend` Attempts entry.

**Verdict: PASS on Sections 1–5 and on the Attempts entry.** No corrections. The decision-level content is the
reduction (33.1) and the location of an obstruction (33.6). Neither changes the decision: the lane found no
construction and no obstructing relation, and the target stays OPEN.

### 33.1 Reduction (artifact Section 1). PASS

- **Truth table.** The target says: some detecting function on `F_3[V]` gives a function on `F_3[G_3]` with
  `rk(1 − [z]) > 0`.
  - Its contrapositive is "link 1 ⟹ no detecting function on `F_3[V]`". By
    `simple-group-rank-functions-are-augmentation-or-detecting`, that is "link 1 ⟹ V gate".
  - The known direction is "V gate ⟹ link 1": restrict to `E ⋊ V`, apply
    `signed-thompson-z-moving-rank-functions-match-v-rank-functions` (1) ⟹ (2), then the dichotomy.
  - So the target is "link 1 ⟺ V gate". This agrees with §27.3.
- **No Hamming extension (1.2).**
  - The center of `G_3` is `⟨z⟩`. If `N ⊴ G_3` maps onto `PG_3`, then `G_3/N` is abelian, so `N = G_3` by
    perfectness. The normal subgroups are therefore `1`, `⟨z⟩` and `G_3`.
  - `ker ρ = 1` contradicts `d-ary-leavitt-groups-nonsofic-over-finite-fields` (ESTABLISHED).
  - `ker ρ = ⟨z⟩` needs `PG_3` nonsofic. Independent check: `g ↦ s_0 g t_0 + p_10 + p_11` is an injective
    homomorphism `G_3 → G_3` whose image misses `−1` (`p_10 ≠ −p_10`), so `G_3` embeds in `PG_3`.
  - `z ∉ V`, so a nontrivial Hamming model of `V` extends to no `ρ`.
- **No averaging (1.3).**
  - (T) for `L_k(1,2)^x` is closed in `leavitt-gl-equals-el-and-perfect-unit-group`, and a co-amenable subgroup of a
    Kazhdan group has finite index.
  - `GL_(2^n)(F_3) ∩ V = S_(2^n)`, since a prefix-code sum with some `|μ_i| ≠ |ν_i|` has a component of nonzero degree.
    So the index is infinite.

### 33.2 Haar values and the evaluation lift (2.1–2.2). PASS

- **Signs.** `1/2 = −1` in `F_3`, so `P^+ = −(1 + [τ])` and `P^− = [τ] − 1`, with `ev(P_α^−) = p_α`.
- **Lemma 2.1.**
  - Even patterns vanish, because `∏_(c ∈ C) τ_c = z`.
  - `V` is transitive on codes of equal size.
  - Induction gives `r_(n+1)(k) = r_n(k)/2` for odd `k <= n`, and `r_(n+1)(n+1) = β 2^(−n)`, starting from `r_1(1) = β`.
- **Proposition 2.2.**
  - `p_00 w = s_00 t_01`.
  - `[w] P_00^− [w] = P_01^−`, so `N^3 = P_00^− P_01^− [w]`.
  - Splitting over `P_1^±` leaves `q_(−,−,−)`, of rank `>= β/4`.

### 33.3 Fock lift and splitting (2.3–2.4). PASS

- **Proposition 2.3.**
  - `ev(e_(+−)) = p_01`.
  - `e_(+−)[w] = [w] e_(−+)` gives `N_F^2 = 0`.
  - `τ_00 w = w τ_01` gives `[τ_00] N_F [τ_00] = −N_F`.
  - Cylinder-preserving `v` commute with `w`.
- **Splitting.** `t_010 s_001 = 0`, so `x = x_0 x_1`.
- **Proposition 2.4.**
  - `P_00^+ g = 0`, `f_1 g = 0` and `f_0 g = g`, so `D g = −[w_0] g`.
  - `g >= q_(+,−,−,+,−)` gives rank `>= β/16`.

### 33.4 Unipotent classes (artifact Section 3). PASS

- **Lemma 3.1.**
  - (a) `t_0 s_0 = 1`, so `ker(s_0 t_1) = ker t_1 = p_0 R`, using `t_1 p_0 = 0`. The image is `s_0 R = p_0 R`.
  - (b) `t_01 = t_1 t_0` and `t_01 s_00 = t_1 s_0 = 0`, so `n^2 = 0`. Also `ker n = (1 − p_01) R`, `im n = p_00 R`, and
    `t_1 : p_1 R → R` has inverse `s_1`.
  - (c) `−2 = 1`, so `(c_3 − 1)^2 = 1 + c_3 + c_3^2`, the all-ones matrix. It is nonzero because `M_3(F_3) → R` is
    injective.
  - **Invariants.** `n_(ugu^(−1)) = u n_g u^(−1)`, so kernel and image are carried by left multiplication by `u`. The
    quotient is `0` for `T(0,1)` and `≅ R` for `x`, and `n^2 ≠ 0` for `c_3`.
- **Proposition 3.2.**
  - `(u − 1)^2` has the single entry `ac`, which gives 12 regular elements and 14 square-zero ones. The square-zero
    ones have rank one: `a = 0` leaves one column and `c = 0` one row.
  - **Conjugator.** `v = s_0 t_00 + s_10 t_01 + s_11 t_1` and `v^(−1) = v^*` give `v s_00 = s_0` and `t_01 v^* = t_10`, so
    `v x v^(−1) = T(0,10)`.
  - `c_3` has minimal polynomial `X^3 − 1 = (X − 1)^3`. Rank functions are conjugation invariant.
- **3.3.**
  - A group of order 54 gives a free `F_3[X]/(X − 1)^3`-module, with profile `(2/3, 1/3)`.
  - The natural module gives `(1/3, 0)` on the rank-one elements.
  - The Frobenius inequality `2 rk(N^2) <= rk(N) + rk(N^3)` holds.
  - `z`, `T(0,10)` and `T(10,11)` have `|σ| <= |κ|`, as in the depth-monotone node, line 29.

### 33.5 Fock parity and the intertwiner (Section 4). PASS

- `Λ(τ_c) e_S = (−1)^|S ∩ c| e_S`, so `Λ(P_c^−)` is `−2 = 1` on odd `S` and `0` on even `S`.
- **Proposition 4.1.**
  - (a) `Λ_2(x)` sends `e_01` to `e_01 + e_00`, and the extra term dies if `00 ∈ S`. `Λ_2(X_F)` corrects exactly when
    `00 ∉ S` and `01 ∈ S`, replacing `e_01` in place. So the two agree.
  - (b) `x = x_0 x_1` at level three, and `Λ_3` is multiplicative. For `S = {001, 010}`: `Λ_3(X_F) e_S = e_S`, but
    `Λ_3(x) e_S = e_S + e_001 ∧ e_000`. The cell parities are `(+, −, −, +)`.
- **4.3.** The cited nodes are ESTABLISHED on main at `1da285e70`:
  - `level-unit-hnn-extensions-have-anti-central-rank-models`, with `B_g = {a ∈ L : g a g^(−1) ∈ L}` at line 17;
  - `fock-local-letters-extend-level-models-with-disjoint-commutation`;
  - `natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter`;
  - `exterior-tensor-powers-are-asymptotically-free`.

### 33.6 Obstruction location and the weakly finite version (Section 5). PASS

- **5.1.** `σ_reg(x) = σ_reg(x_0) σ_reg(x_1)` is a level identity, and `X_(v_i)` intertwines on `B_(v_i) ∋ x`. So the
  HNN model satisfies splitting.
- **Corollary 5.1.** Under the hypothesis, the target's conclusion is "not link 1".
- **The gloss "kills every extension", checked.**
  - `{g : rk(1 − [g]) = 0}` is a normal subgroup. If it contained `V` it would be `G_3`, and then `β = 0`.
  - So a function with `β > 0` restricts to a non-augmentation function on `V`, which is detecting by the dichotomy.
  - Killing every extension of every detecting `rk_V` is therefore link 1.
- **5.3.** With `B_g` as in 33.5, `B_(v,v') ⊆ B_(v v')`, and both commutant bullets recompute.
- **Proposition 5.2.**
  - The kernel misses `V \ 1`, so it is `1` or `⟨z⟩`.
  - `e = (1 − u)/2 ≠ 0` is central in the image.
  - `(A + (1 − e)1_n)(B + (1 − e)1_n) = 1_n` gives `BA = e 1_n`.
  - `linear-sofic-group-algebra-is-stably-finite` exists. `ternary-anti-central-summand-has-no-weakly-finite-image` is
    OPEN, as the Status bullet treats it.
- **Candidates.** Untested and not verified here. `T(00,1)` has `|σ| > |κ|`.

### 33.7 The Attempts entry (target node). PASS

- It matches the artifact on each item: the reduction, both bounds, the classes, the intertwiner, the two letters
  outside `L`, and the weakly finite version.
- "Via `ker n / im n`" separates `T(0,1)` from `x`, and `n^2 ≠ 0` separates `c_3`. Both are `R_R` invariants, so no
  change is needed.
- **Scope.** Every bound is a multiple of `β`, and no item forces `β = 0` or rank triviality. Plan 1 and the gate stay
  OPEN.

## 34. w7-k2-unstable (8afa07966)

Sources:
- Artifact `leavitt-unstable-k2-steinberg-reduction-2026-09-12.md` (blob `c47819ab`), Sections 0–5. Sections 6–8 were
  checked as listings.
- The OPEN claim `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` (blob `5a8142c3`).
- The lane's Attempts entries on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (entry as landed at
  `ac79e865`) and `binary-complement-corner-has-no-weakly-finite-image` (blob `97bd6534`).

**Verdict: PASS on Sections 1–5, the claim display and both entries.** No corrections. The imports are exactly those
the artifact's Section 7 names:
- Khanh's (KH1), Lemma 5.2, Theorem 5.1 and Proposition 4.2;
- the statement of Voronetsky's Proposition 1;
- for the ternary host, `khanh-acyclicity-and-steinberg-criteria` through the host theorem.

It is decision-level for the gate plans. Option 2 of Remark 3.2 in the mismatched-factor firewall is empty for both
hosts. Nothing here says that rank models or weakly finite images are trivial. The binary corner claim, both
submultiplicativity claims and Plan 1 stay OPEN. The lane may create the route.

### 34.1 Stable K-theory and the identification (Sections 0–1). PASS

- **Stable groups.** For one vertex with two loops, `N_E = (2)` and `1 − N_E^t = −1`, which is invertible on every
  `K_n(k)`. In the long exact sequence every map `K_n(k) → K_n(k)` is then an isomorphism, so each `K_n(L_k(1,2))`
  is squeezed between a zero cokernel and a zero kernel. This agrees with `ara-cortinas-leavitt-tensor-k-theory-vanishes`.
- **The identification.** The code `{0, 10, 11}` gives `R ≅ R^3` as right modules, so `M_3(R) ≅ R` and `R^x ≅ GL_3(R)`.
- **`GL_3 = E_3`.** Binary: `leavitt-gl-equals-el-and-perfect-unit-group`. Ternary: part 2 of the host theorem, whose
  proof takes GE from Menal–Moncasi and not from the Steinberg comparison, so the use is not circular.

### 34.2 Binary: `K_2(3, R_2) = 0` (Section 2). PASS

- **Step 1, recomputed.**
  - `x_ij(a) = [x_ik(a), x_kj(1)]`, so `S_3` is perfect.
  - The five-term sequence gives `H_2(G_3) → N_3/[S_3, N_3] → H_1(S_3) = 0`. `(KH1)` covers `n = 2`, `r = 3`: it holds
    "for every n > 0 and r >= 1" (`leavitt-steinberg-map-iso-from-rank-three`, line 17). So `N_3 = [S_3, N_3]`.
  - Lemma 5.2 makes `j_3(N_3)` central in `S_4`. Hence `j_3(N_3) = [j_3(S_3), j_3(N_3)] = 1`.
- **Step 2.** The hypotheses (1)–(3) listed match Theorem 5.1 as quoted in item 2 of
  `khanh-acyclicity-and-steinberg-criteria`: `GL_(n−1) = E_(n−1)` and `GL_(n−2) = E_(n−2)`, `j_(n−1)(N_(n−1)) = 1`, and
  `|X_n|` simply connected, at `n = 4`. Imported.
- **Step 3, recomputed.**
  - `U_3 T_3 (x) = (x_1, x_2, (ee* + ff*) x_3) = x`, and `T_3 U_3 (x_1, x_2, y, z) = (x_1, x_2, e*(ey + fz), f*(ey + fz)) =
    (x_1, x_2, y, z)`.
  - `T_3 E_33 U_3` sends `(x_1, x_2, y, z)` to `(0, 0, y, z)`, which is `E_33 + E_44`.
  - For `i < 3`, `E_i3 U_3 = e E_i3 + f E_i4`. So `α_3(1 + a E_i3) = 1 + ae E_i3 + af E_i4 = (1 + ae E_i3)(1 + af E_i4)`,
    since `E_i3 E_i4 = 0`.
  - **Voronetsky's family.** `E_11, ..., E_44` is a complete orthogonal family, and it is Morita equivalent because
    `E_ii = E_ij E_jj E_ji`. With `n = 4` and `S = {1}`, `b = α_3(a E_i3) = ae E_i3 + af E_i4` has `b E_33 = ae E_i3` and
    `b E_44 = af E_i4`. So `F_α ∘ St(α_3)` agrees with `D_3` on generators, and `φ_4 D_3 = α_3 φ_3` holds on generators,
    hence everywhere.
- **Step 4.** `ker φ_3 = ker(α_3 φ_3) = ker(φ_4 D_3) = D_3^(−1)(N_4) = 1`. Only the injectivity of `D_3` is used.

### 34.3 Ternary: `K_2(3, R_3) = 0` (Section 3). PASS, conditional as stated

- Theorem 3.1 of `boone-higman-prime-field-leavitt-hosts-2026-09-12.md`, read at `bd53fc92c`:
  - part (1) with `N = 2` gives `H_n(GL_r(R); Z) = 0` for `1 <= n <= 2` and all `r`;
  - part (2) needs `N >= 2` and gives `St_r(R) ≅ GL_r(R)` for `r >= 3`.
- `B = F_3` is simple and unital, and 34.1 gives every `K_i(R_3) = 0`.
- The step descriptions match the proof list of Theorem 3.1: Theorem 2.1 (`n >= 4`, any nonzero unital ring) replaces
  Theorem 5.1, and Voronetsky's refinement needs no characteristic hypothesis.
- The prime-field host node is ESTABLISHED conditional on `khanh-acyclicity-and-steinberg-criteria`, as Section 7
  says.

### 34.4 The Steinberg residue (Section 4). PASS

- **(St3) index check.** `[x_ij(a), x_kl(b)] = 1` needs `j ≠ k` and `i ≠ l`. Both hold for `x_ik` against `x_ij` and
  against `x_jk`. So `x_ik(c)` commutes with both.
- **Closure, recomputed.** From (St2), `x_jk(b) x_ij(a) = x_ik(−ab) x_ij(a) x_jk(b)`. Then
  `(λ, μ, ν)(λ', μ', ν') = (λ + λ', μ + μ', ν + ν' − λ'μ)` on `x_ij(λa) x_jk(μb) x_ik(νab)`. This is a quotient of the
  Heisenberg group over `F_p`, of order at most `p^3`: 8 over `F_2`, which is Remark 3.2's bound (line 204), and 27
  over `F_3`.
- **Option 2.** `N_3 = 1` means (St1)–(St3) present `S_3 ≅ R^x`, so there is no `K_2(3,R)` element to use.

### 34.5 Hexagon presentation, calibration and limits (Section 5). PASS

- **Arcs, recomputed.** In the cyclic order `123, 213, 231, 321, 312, 132`, each root's arc of three consecutive
  vertices is:

  | root | vertices |
  |---|---|
  | `(1,2)` | 5, 6, 1 |
  | `(2,1)` | 2, 3, 4 |
  | `(1,3)` | 6, 1, 2 |
  | `(3,1)` | 3, 4, 5 |
  | `(2,3)` | 1, 2, 3 |
  | `(3,2)` | 4, 5, 6 |

  Adjacent vertices share 2 roots, vertices at distance two share 1, and opposite vertices share 0. The shared root at
  distance two lies in both edge groups at the middle vertex.
- **(SPG2) at `n = 3`, independently.**
  - Every Steinberg relation lies in one `U_π`:
    - (St1) lies in any `U_π` containing its root;
    - (St2) for `(i,j)` and `(j,k)` lies in `U_(ijk)`;
    - (St3) for a common source `i` lies in `U_(i··)`, and for a common target `k` in `U_(··k)`.

    No other pair of distinct roots satisfies the (St3) conditions.
  - So `S_3 → colim` is defined. It is inverse to `colim → S_3`, because the copies of each `x_ij(a)` are identified
    along the arc.
  - Killing the off-forest letter of `π_1(Y_hex)` gives the free product of the vertex groups amalgamated along
    every edge, which is the colimit.
- **Calibration.** The main case of Theorem 1.1 of the mismatched-factor firewall applies:
  - The graph is countable and may have cycles.
  - `U_π(R_2)` is countable and locally finite. Finitely many `(a_i, b_i, c_i)` stay inside the finite set
    `span{a_i} × span{b_i} × span{c_i, a_i b_j}`, which is closed under `(a, b, c)(a', b', c') = (a + a', b + b', c + c' + ab')`.
  - Every edge unit is `1`, which is allowed off the forest.
  - `σ` takes values in a weakly finite characteristic-two algebra (Theorem 1.1(3)), is nontrivial, and has
    `σ(t) = [π_(n,e)]`.
  - The representation form of `binary-complement-corner-has-no-weakly-finite-image` ("every homomorphism of
    `L_(F_2)(1,2)^x` into the units of a weakly finite ring of characteristic two is trivial") is refuted by any
    nontrivial such `σ` that kills `t`. The Corollary 1.3-type conclusion, that a relation-only proof must use
    `t = 1`, follows.
- **No `D_A` statement.** Corollary 1.2 needs both unit root pairs in one vertex group (line 95). The frame-vertex
  remark is correct: the amalgam `R^x *_K L_0` needs further relations. Both are non-claims.

### 34.6 Claim display, entries, consumers and scope. PASS

- **Display.** Points 1–4, "Not claimed" and "Payoff" match Sections 1–5. Point 2's "order at most `p^3`" is 34.4.
- **Entries.** The `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` entry and the
  `binary-complement-corner-has-no-weakly-finite-image` entry each state option 2 empty, order at most 8 over `F_2`,
  the two remaining options, and the hexagon as a presentation, not a firewall. That is accurate.
- **Consumers (Section 6).** The plan line numbers 45, 319 and 325 were read at `1754aa79d2`. The plan has since
  moved: it now says this at lines 46–47 and 372–386. The listing is time-stamped, so nothing needs changing. The
  three marked-graph nodes concern Laurent hosts, and are correctly listed as non-consumers.
- **Subsumption scan at `25d2ad26e8`.** `K_2(3` occurs in 11 research files:
  - the claim and its artifact;
  - both entries;
  - `graphs-of-locally-finite-groups-carry-regular-rank-models`;
  - the firewall artifact, the plans artifact and this artifact;
  - the three marked-graph nodes.

  The binary part of point 1 is `(KH2)` at `r = 3`, which the claim's `distinct_from` records. No landed node states the
  ternary rank-three case or the hexagon presentation.
- **Route.** Section 8's five required nodes exist on main and are ESTABLISHED; two of them are literature imports,
  and the host node is conditional. Advisory: Step 2 quotes Theorem 5.1 through
  `khanh-acyclicity-and-steinberg-criteria` directly, so the route may list it too.
- **Scope.** Everything here is a presentation or a vanishing statement about `K_2`. None of it forces a rank model,
  a weakly finite representation or `θ` to be trivial.

## 35. w7-sub-multiletter (37bafd8f30)

Sources:
- Artifact `multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md` (blob `71cb2271`), Sections 0–6.
- The OPEN claims `split-cylinder-data-cannot-force-defect-submultiplicativity` (blob `7a134bb1`) and
  `lex-decreasing-units-with-order-preserving-letters-are-amenable` (blob `99448841`).
- The routes `split-cylinder-data-defect-firewall-proof` (blob `10ba7520`) and
  `lex-decreasing-units-order-preserving-letters-amenability-proof` (blob `10e58dd6`).

**Verdict: PASS on Sections 2–5, both claim displays and both routes, with one CORRECTION to Lemma 6.1 (35.4).**
- The literal hypothesis of Lemma 6.1 is too weak, and its first conclusion is false: an explicit order preserved by
  `b` makes every positive root move points strictly one way, but not all the same way.
- The lemma is correct when the positive roots of each frame move one common way, and that is all the mechanism of
  Theorem 3.5 needs. Nothing in either claim statement depends on the literal version. The scope sentence of the lex
  claim needs "in one common direction".

It is decision-level for the SUB plans:
- a relation-only deficit from `Gamma_2(R^x)` would be the gate itself;
- one from `U_< ⋊ F` would prove `F` nonamenable.

Nothing here proves that rank models are trivial. `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, the
gate and Plan 1 stay OPEN.

### 35.1 Cylinder swaps (Section 2). PASS

- **Lemma 2.1, recomputed.** Incomparable `A`, `B` give `T[B]S[A] = 0 = T[A]S[B]`. So
  - `tau S[A] = S[B] + S[A] − e_A S[A] = S[B]`, and `T[A] tau = T[B]`;
  - `tau e_A tau = S[B]T[B] = e_B`, which conjugates `iota_A(g)` to `iota_B(g)`.
  - As a partial-map sum, `tau` exchanges `[A]` and `[B]` and fixes the finite union of cylinders
    `X ∖ ([A] ∪ [B])`. So it is an involution in `V`.
- **Lemma 2.2, recomputed.**
  - Disjoint supports give `iota_A(g) iota_B(h) = S[A]gT[A] + S[B]hT[B] + 1 − e_A − e_B`, which is symmetric.
  - Compressing `prod iota_(A_i)(g_i)` by `T[A_j] · S[A_j]` returns `g_j`, so `G^k` is faithful.
  - `pi -> sum S[A_(pi i)]T[A_i] + 1 − sum e_(A_i)` is an injective homomorphism `S_k -> V`, and it sends
    transpositions to the swaps.
  - The kernel `K` of `G wr S_k -> Gamma_k(G)` is normal and meets the normal subgroup `G^k` trivially, so it
    centralizes `G^k`.
  - An element with `pi(i) != i` sends `iota_(A_i)(a)`, `a != 1`, into another slot. So `K <= G^k`, and `K = 1`.
- **Proposition 2.3, recomputed.**
  - `P_pi (Y_1 (x) ... (x) Y_k) P_pi^(−1)` moves slot `i` to slot `pi(i)`. So `sigma_n(x) sigma_n(y)` and
    `sigma_n(xy)` differ slotwise by `rho_n(g_i) rho_n(h') − rho_n(g_i h')`.
  - `rk(X (x) Y − X' (x) Y') <= rk(X − X') rk(Y) + rk(X') rk(Y − Y')`, with normalized ranks at most `1`, gives the
    sum bound. So `sigma` is an asymptotic homomorphism.
  - `sigma_n(D_(A_i))` is `D_rho` in slot `i`, exactly at every stage. A product over distinct slots has normalized
    rank `delta_(rho_n)^m`, and the limit is `delta_rho^m`.
  - The joint fixed space of `(rho_n(s) − 1) (x) 1`, `s in S`, is `ker(col_S) (x) (rest)`, of normalized rank
    `f_(rho_n)(S)`. In the ultraproduct `Fix(sigma(Gamma_k))` lies inside it for every finite `S`, so the fixed rank
    is at most `f_rho`.
- **Corollary 2.4.** With `k = m = 2`, `delta^2 <= theta delta^2` forces `delta = 0`.
  - Sofic `G` with an element of infinite order: Theorem S gives `delta = 3/8`, and `G wr S_2` is sofic.
  - Finite `G`: `Gamma_k(G)` is finite.
  - `G = R^x`: incomparable words are nonempty, so `[A]` is a proper cylinder. The gap gives `delta >= c_0` in every
    nontrivial fixed-point-free model, so `delta = 0` means every model is trivial, and in particular the gate holds.
    This is a conditional firewall. It does not assert that models are trivial.
- **Characteristic three.** `iota_A(−1) = 1 + e_A`. When `[A] ∪ [B] = X`, `iota_A(z) iota_B(z) = 1 − 2 = −1 = z` goes
  to `(−1) (x) (−1) = +1`. When the union is proper, every element of `Gamma_2(G)` is `1` on the complementary
  corner, so `z` is not in `Gamma_2(G)` and `<z> x Gamma_2(G)` takes an anti-central model.
- **Scope.** `x_0` sends `[10]` onto `[01]` and `[11]` onto `[1]`, so it is not a single prefix replacement per
  cylinder. That is correct.

### 35.2 The lexicographic Borel group (Section 3). PASS

- **Lemma 3.1, recomputed.** In the case `v' = wu`, `w'` is a prefix of `w` is impossible, since then
  `[wu] ⊆ [w']`. So `[w'] ⊆ [w]`, or `[w] < [w']`, and either way `[vu] ⊆ [v] < [w']`. The case `w = v'u` is the
  mirror image.
- **Lemma 3.2, recomputed.**
  - The ranges of `P_k` are nested nonempty compact sets.
  - The pullbacks `eta_j` increase strictly, and every length-`n` prefix is eventually constant.
  - For `j` large, `m_j = S[v]T[w]` has `v` a prefix of `eta_(j−1)` and `w` a prefix of `eta_j`. Both agree with
    `eta_inf` beyond length `L`, so `v` and `w` are comparable, which contradicts `[v] < [w]`.
- **Corollary 3.3.** `N` is finite over `F_2`, the inverse is a finite geometric sum, and `(1 + n)^(2^r) = 1 + n^(2^r)`.
- **Lemma 3.4.** Each term of `g S[v]T[w] g^(−1)` restricts `g ∘ (wy -> vy) ∘ g^(−1)`, with range in `g[v]` and domain
  in `g[w]`. `g` preserves order, so `g[v] < g[w]`.
- **Theorem 3.5.**
  - `U_<` is torsion and `F` is torsion-free, so the product is semidirect.
  - Locally finite by amenable is amenable, and a nontrivial `P` supplies an element of infinite order for
    Theorem S.
  - `F` is a quotient of `U_< ⋊ F`, which gives the "only if".
- **Example 3.6.**
  - (1) With `(p_1, p_2, p_3) = (0, 10, 11)`, `[A p_a u] ⊆ [A p_a] < [A p_b] ⊇ [A p_b u']`. This includes `A` empty,
    so the order-128 Toeplitz group lies in `U_<`.
  - (2) `x_0` maps `0 < 10 < 11` onto `00 < 01 < 1`, so it is in `F`. In `R^ω_≤` the pair `y = S[00]T[0]`,
    `z = S[0]T[00]` has `zy = e_0` and `yz = e_00`, so `XY = 1` and `YX = 1 − e_01`. The `R^ω_≥` case uses
    `S[1]T[11]` and `S[11]T[1]` in the corner `e_1`.
- **Corollary 3.7 and characteristic three.** The torsion of `U_< ⋊ P` lies in `U_<`. `−1` would need `1 in T_<`, but
  `T_<` is locally nilpotent. `(1 + n)^(3^r) = 1 + n^(3^r)` makes `U_<` a 3-group.

### 35.3 One-chart coefficients (Section 4). PASS

- **Fact 4.1.** `S/I` is finite over `F_2`, so `GL_#Q(S/I)` is finite.
- **Corollary 4.2.** `iota_(A_i)(x_ab(c)) = Phi_Q(1 + c E_(A_i p_a, A_i p_b))` for `c in S`. Item 3 of the right-child
  node supplies infinite order.
- **Lemma 4.3, recomputed.**
  - Conjugation by the permutation `pi` carries `u E u^(−1) < E_(q')` to `E' < E`.
  - `W^(−1) E' W = E` gives `xy = E`, and `W E W^(−1) = E'` gives `yx = E'`.
  - `x`, `y` lie in `E M_Q(S) E`, so the cross terms vanish, and `XY = 1`, `YX = 1 − (E − E')`.
  - **Ideal step.** `(1 − ab) a = 0 = b (1 − ab)`. So in `(1 − ab) b^k a^i b^(i') a^l (1 − ab)` a term survives only if
    `i = k` and `i' = l`, or `i < k` on the same diagonal. The minimal choice of `k` makes the second case have
    coefficient `0`.
  - Products of finite-dimensional algebras are directly finite.
- **Corollary 4.4.** The leftmost leaf of `Q != {empty}` is `0^k` with `k >= 1`, and `x_0` carries `[0^k]` onto
  `[0^(k+1)]`.

### 35.4 Lemma 6.1 (Section 6). CORRECTION to the hypothesis; PASS in the corrected form

**The literal statement is false.** Read literally, the hypothesis says that each positive root of the frames at `A`
and `A1` moves all its points strictly one way. Under that hypothesis the conclusion "all of them move the same way"
fails, and `b` preserves some such order.

- **Counterexample.** Identify `[A]` with `X` through `Ay -> y`. On `[A]`, `b` is `0y -> 0y`, `10y -> 100y`,
  `110y -> 11y`, `111y -> 101y`. Let `phi_2(0y) = 1 phi_2(y)` and `phi_2(1y) = 0y`, and put
  `Psi = (0y -> 0y, 10y -> 10y, 111y -> 110y, 110y -> 111 phi_2(y))`. Order `[A]` by `xi ≺ eta` iff
  `Psi(xi) <_lex Psi(eta)`, and order the rest of `X` lexicographically, with the block `[A]` in its place.
- **`b` preserves `≺`.** Recomputed: `Psi b Psi^(−1)` is `0 -> 0`, `10 -> 100`, `110 -> 101`, `1110 -> 110` and
  `1111 -> 111`. For the last two:
  - `phi_2^(−1)(0w) = 1w`, and `1110w -> 110 1w -> 111w -> 110w`;
  - `phi_2^(−1)(1w) = 0 phi_2^(−1)(w)`, and `1111w -> 110 0 phi_2^(−1)(w) -> 11 0 phi_2^(−1)(w) -> 111w`.

  The domain code `0 < 10 < 110 < 1110 < 1111` goes to `0 < 100 < 101 < 110 < 111`, so this is in `F`, and `b`
  preserves `≺`.
- **Directions.** The blocks are ordered `[A0] ≺ [A10] ≺ [A111] ≺ [A110]`. So:
  - at `A`, `S[A0]T[A10]`, `S[A10]T[A11]` and `S[A0]T[A11]` move down;
  - at `A1`, `S[A10]T[A110]` and `S[A10]T[A111]` move down, but `S[A110]T[A111]` moves up.

  Every root moves its points strictly one way, not all the same way, and `b` preserves the order.
- **Where the proof slips.** "Same direction" shows only that `S[A10]T[A110]` follows the roots at `A`. The root
  `S[A110]T[A111]` compares two subcylinders of `[A11]`, and no root at `A` constrains them.

**Corrected statement.** Consider total orders on `X` in which the positive roots of each frame all move points
strictly one common way. Then both frames move the same way, and no such order is preserved by `b`.
- The artifact's two steps prove this.
- "Same direction" transfers the direction of the frame at `A` to `S[A10]T[A110]`, and so to the whole frame at `A1`.
- "Not preserved" uses the downward roots `S[A10]T[A110]` and `S[A110]T[A111]`. They give `[A100] ≺ [A11] ≺ [A101]`,
  which is impossible because `[A101] ⊆ [A10] ≺ [A11]`.

**Consequences.**
- **Section 6, item 1.** "Lemma 6.1 rules out the mechanism of Theorem 3.5" stands. That mechanism needs all six roots
  in one `T_≺`, which is one common direction.
- **Contraction.** `b` sends `[A10 0^k]` onto `[A10 0^(k+1)]`. On `[A1]` it is three prefix replacements, so Section 2
  does not apply.
- **What the counterexample does not show.** It gives no amenability or soficity of `Gamma_b`, which stays open.
- **Wording to correct forward.** Two sentences use the literal wording, "no order preserved by `b` makes both frames'
  positive roots monotone":
  - the Scope of `lex-decreasing-units-with-order-preserving-letters-are-amenable` (line 38);
  - the w7-sub-multiletter entry on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (line 231).

  Both should say "monotone in one common direction". The plans artifact (line 426) already says "all move one way",
  which is correct. No claim statement depends on the literal version.

### 35.5 Model tests, displays, routes, subsumption and scope. PASS

- **Section 5, item by item.**
  - Free sofic model: Proposition 2.3 with Theorem S's `rho` gives `(3/8)^2` on the sofic `G wr S_2`.
  - Finite subgroups: the order-128 group lies in `UT_3(R) <= U_<`, as in 35.2.
  - Right-child items 2–4:
    - the four positive roots lie in `T_<`, since `A0 < A10 < A110 < A111`;
    - `x^A_12(s_0) x^A_21(1)` uses a negative root;
    - the frame entries of `iota_A(w_23)` include `s_0`, `s_1`, `t_0`, `t_1`, and `b` contracts `e_(A10)`.
  - Jacobson nodes: `binary-jacobson-el3-is-sofic` and the halves node read as in Sections 31–32 here, and property (T)
    with residual finiteness is no conflict.
  - Depth-monotone: Example 3.6(2) and Corollary 4.4.
  - Ternary target: line 29 records `theta = 1` for independent factors.
  - Toeplitz quarter: its group lies in `U_<`.
- **Claim displays.**
  - Split-cylinder: Statements 1–3 are Lemmas 2.1–2.2 and Proposition 2.3 as re-derived in 35.1. The Consequence is
    Corollary 2.4. The Scope is Section 2's, including characteristic three.
  - Lex claim: items 1–4 are Lemmas 3.1–3.4, Theorem 3.5 and Example 3.6(1). The Consequences are 3.6(2), 3.7 and
    characteristic three. The Scope sentence is corrected in 35.4.
- **Entries.**
  - The entry on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (blob `da18a78a`) and the one on the
    ternary target summarize Sections 2–4 and the characteristic-three port accurately. The wording on line 231 is as
    in 35.4.
  - The plans record (blob `19de3bf9`, lines 412–426) is accurate.
- **Routes.**
  - `lex-decreasing-units-order-preserving-letters-amenability-proof` requires
    `sofic-subgroups-carry-independent-cylinder-defects`, which is ESTABLISHED. Its five steps are 35.2.
  - `split-cylinder-data-defect-firewall-proof` requires nothing, and Statements 1–3 are self-contained.
  - Advisory: the claim's Consequence uses Theorem S and the defect gap, both ESTABLISHED, and the route may list them.
- **Subsumption scan at `0bb651f36d`.** `tau_AB`, `wr S_k`, `U_<`, "lexicographically decreasing" and "Borel group" hit
  28 research files. Outside this lane's files the hits are other notation:
  - the sign involutions `[tau_(A_i)]` of the characteristic-three descent;
  - barycenters;
  - Steinberg coordinates;
  - `H wr S_k` for finite-index overgroups;
  - function-field Borel groups.

  The four-transvection escape artifact consumes `U_< ⋊ P` as a firewall. The right-child node (item 4) and Section 4
  of the locally-finite-conjugation artifact prove finiteness for four positive roots through a potential, and
  Lemma 3.2 generalizes that, which `distinct_from` records. No duplicate.
- **Scope.** Each firewall is conditional: a deficit from these relations would imply the gate, or would imply that
  `F` is nonamenable, or it contradicts Theorem S. None of them forces a rank model or `theta` to be trivial. The next
  live systems, `Gamma_b`, `U_< ⋊ F` and `EL_3(J)`, stay OPEN.

## 36. w7-escape-set (45282c2142)

Sources:
- Artifact `four-transvection-escape-set-2026-09-12.md` (blob `cb33ab0f`), Sections 0–5.
- The claims `four-transvection-set-escapes-depth-monotone-units` (blob `1339c38f`),
  `four-transvection-units-have-a-weakly-finite-symbol-image` (blob `fcc45de7`) and
  `depth-monotone-units-carry-weakly-finite-nonzero-defect` (blob `9e696bc5`).
- The OPEN claim `four-transvections-and-x23-force-defect-vanishing` (blob `1f3ccdee`).
- The routes `four-transvection-escape-proof` (blob `384f5613`), `four-transvection-symbol-firewall-proof` (blob
  `85927ae8`), `depth-monotone-tensor-cube-defect-proof` (blob `06b2138e`) and
  `summand-obstruction-from-four-transvection-defect` (blob `0aff6a1e`).
- The entries on `ternary-leavitt-units-have-no-weakly-finite-representation` (blob `a274ca7f`) and
  `ternary-weakly-finite-representations-kill-two-root-defect` (blob `99a42c33`).

**Verdict: PASS on Sections 1–4, the three claim displays and the three proof routes.** The OPEN claim is correctly
OPEN, and `summand-obstruction-from-four-transvection-defect` is a valid implication. There are three wording
advisories (36.5) and no correction.

It is decision-level for the ternary counterexample route:
- the defect form (iv) is firewalled on every sofic subgroup of `G` containing `z` and the standard frame, and
  explicitly, without soficity, on `H^ω_≤` with `ω(0) <= ω(1)`;
- so a proof of `ternary-weakly-finite-representations-kill-two-root-defect` must use relations that hold in none
  of them;
- the smallest known input for `ternary-anti-central-summand-has-no-weakly-finite-image` is `Γ_5 = <S4, x_23(1)>`,
  which is OPEN, and soficity of `Γ_5` would refute it.

Every model built here is nontrivial, with `z -> -1` and `D != 0`. Nothing proves that rank models are trivial.
Gottschalk on `G`, the gate and Plan 1 stay OPEN.

### 36.1 The escape invariant (Section 1). PASS

- **Theorem 1.1, recomputed.** Put `A = s_0 t_1`, `A' = s_1 t_0`, `B = s_1 t_00` and `B' = s_00 t_1`, the four
  transvections minus `1`.
  - `B'A' = s_00 t_0`, `A'A = s_1 t_1` and `AB = s_0 t_00`.
  - `x = s_00 t_0 + s_1 t_1` and `y = s_0 t_00 + s_1 t_1` give `yx = s_0 t_0 + s_1 t_1 = 1`, because
    `t_00 s_1 = 0 = t_1 s_00`.
  - `xy = s_00 t_00 + s_1 t_1 = 1 − s_01 t_01`.
  - A conjugate of `<S4>` inside `H^ω_≤` would put the conjugated pair inside the stably finite `R^ω_≤`
    (`depth-monotone-leavitt-subalgebras-are-stably-finite`). The `≥` side is the same.
- **Remark 1.2, recomputed.** With `ω(0) = a` and `ω(1) = b`, the roots compare `a : b` (`A`), `b : a` (`A'`),
  `b : 2a` (`B`) and `2a : b` (`B'`).
  - `{A, A', B}` lies on the `≤` side and `{A, A', B'}` on the `≥` side, both with `a = b`.
  - `{A, B, B'}` lies on the `≤` side and `{A', B, B'}` on the `≥` side, both with `b = 2a`.
  - The inverses `1 − n` stay in each span.
- **Proposition 1.3.** It rests on Lemma 1.2 of `depth-monotone-leavitt-firewall-2026-09-12.md`, read at its lines
  66–72:
  - each `F_r` is finite-dimensional, `F_r ⊆ F_r'` for `r <= r'`, and `C = ∪_r F_r`;
  - `π(s_μ t_ν) F_r ⊆ F_r` when `ω(μ) <= ω(ν)` and `ω(μ) <= r`.

  So a finite combination of `≤` monomials preserves `F_r` for large `r` and is locally finite.
  - If `π(ugu^(-1))` is locally finite, so is `π(g) = π(u)^(-1) π(ugu^(-1)) π(u)`.
  - On the `≥` side, `(ugu^(-1))^* = (u^*)^(-1) g^* u^*` lies on the `≤` side.
- **Corollary 1.4, recomputed.** `x_0 = s_0 t_00 + s_10 t_01 + s_11 t_1`.
  - On `1_[1^n]` with `n >= 1`, only `s_11 t_1` contributes, and it gives `1_[1^(n+1)]`. So the orbit of `1_[1]`
    spans an infinite-dimensional space.
  - `x_0` is the element `00y -> 0y`, `01y -> 10y`, `1y -> 11y` of `V`, so `x_0^* = x_0^(-1)`.
  - An invertible locally finite operator maps each finite-dimensional invariant subspace bijectively onto itself,
    so its inverse is locally finite. Both sides fail for `x_0`.

### 36.2 The symbol image (Section 2). PASS

- **Theorem 2.1(a), recomputed.** For incomparable `σ = σ_1 σ'` and `κ = κ_1 κ'`, the formula
  `t_i s_σ t_κ s_j = δ_(i σ_1) δ_(j κ_1) s_(σ') t_(κ')` gives `Φ(S4) = {E_01(1), E_10(1), E_10(t_0), E_01(s_0)}`.
  - `e_10 (s_0 e_01) = s_0 e_11` and `(s_0 e_01) e_10 = s_0 e_00`, so `s_0 I` lies in the span, and likewise `t_0 I`.
    With `M_2(K)` this gives `M_2(T)`.
  - Conversely every generator and its inverse lies in `M_2(T)`.
  - `T = K<s_0, t_0>` is the Jacobson algebra, by the normal-form basis `s_0^a t_0^b`.
- **(b).** `E_01(1)` and `E_10(1)` generate `SL_2(F_3)`, which contains `−I`. So `z in <S4>`.
- **(c), recomputed.** Under `s_0 -> ζ`, `t_0 -> ζ^(-1)`:
  - `w(ζ) = E_01(ζ) E_10(−ζ^(-1)) E_01(ζ) = [[0, ζ], [−ζ^(-1), 0]]`, `w = w(1)`, and
    `w(ζ) w^(-1) = diag(ζ, ζ^(-1))`, the inverse of `h = diag(ζ^(-1), ζ)`;
  - conjugating `E_01(1)` and `E_01(ζ)` by `h^n` gives `E_01(ζ^(-2n))` and `E_01(ζ^(1-2n))`, so `E_01(p)` for every
    Laurent polynomial `p`, and conjugating by `w` gives `E_10(p)`;
  - `F_3[ζ, ζ^(-1)]` is Euclidean, so `E_2 = SL_2` and the image is `SL_2(F_3[ζ, ζ^(-1)])`, with `z -> −I`.
  - The kernel of `T -> F_3[ζ, ζ^(-1)]` is spanned by `s_0^a (1 − s_0 t_0) t_0^b = s_0^a s_1 t_1 t_0^b`.
- **(d) and Lemma 2.2.** A unital algebra map into a weakly finite algebra with `[z] -> −1` sends
  `ε_- = 2(1 − [z])` to `4 = 1`. So `ε_- F_3[<S4>]` maps unitally onto a nonzero weakly finite algebra. Conjugation
  gives an isomorphic group algebra.

### 36.3 Relations and algebra-level models (Section 3). PASS

- **Lemma 3.1.** `N_23 N_12 = ψ(s_10 t_11 · s_0 t_10)`, and `t_11 s_0 = t_1 t_1 s_0 = 0`. In a conjugate frame the
  product is `ψ(u · 0 · u^(-1))`.
- **Proposition 3.2, recomputed.**
  - (a) `Φ(s_0 t_10) = t_0 e_01`. `E_01(1) E_10(−1) E_01(1) = e_01 − e_10 = w` and `w e_10 w^(-1) = −e_01`, so
    `E_01(−t_0)` and its inverse `E_01(t_0)` lie in `Φ(<S4>)`.
  - (b) `Φ(s_10 t_11) = s_0 t_1 e_11`, and `s_0 t_1` is a normal-form monomial outside `span{s_0^a t_0^b}`.
  - (c) The `Φ`-entries of the six roots:
    - code `{0, 10, 11}`: `s_0 t_10 -> t_0`, `s_10 t_0 -> s_0`, `s_0 t_11 -> t_1`, `s_11 t_0 -> s_1`,
      `s_10 t_11 -> s_0 t_1`, `s_11 t_10 -> s_1 t_0`;
    - code `{1, 00, 01}`: `s_1 t_00 -> t_0`, `s_00 t_1 -> s_0`, `s_1 t_01 -> t_1`, `s_01 t_1 -> s_1`,
      `s_00 t_01 -> s_0 t_1`, `s_01 t_00 -> s_1 t_0`.

    Only `t_0` and `s_0` lie in `T`, and they come from `{0, 10}` and `{1, 00}`. The roots `x_12` and `x_23` of a code
    frame use the distinct pairs `{c_1, c_2}` and `{c_2, c_3}`.
- **Proposition 3.3, recomputed.**
  - (a) Incomparable `σ, κ` make `s_σ t_κ` square-zero, so `T^(-1) = 1 − λ s_σ t_κ`. `e_ki (λ m e_ij) e_jl = λ m e_kl`
    gives `m I`. Conversely every generator and inverse lies in `M_2(W)`.
  - (b) `Q = 1 − s_0 t_0` lies in `T`, and `ψ(t_0) ψ(s_0) = 1` forces `ψ(Q) = 0`.
    - If `β = 0^(j-1) 1 β''`, then `t_β = t_(β'') t_1 t_0^(j-1)`, and
      `m s_0^(j-1) Q t_0^(j-1) = s_α t_(β'') t_1 s_1 t_1 t_0^(j-1) = m`.
    - The case of `α` is the mirror image.
  - (c) On `K[Ω]` the relations `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1` hold, since every sequence has a first
    letter.
    - If `β` contains a `1`, then `t_β e_(0^∞) = 0`. The line `K e_(0^∞)` is invariant, with `s_0, t_0 -> 1` and
      `m -> 0`.
    - If `β = 0^b` and `α` contains a `1`, then `s_0` and `t_0` preserve `U = span{e_ξ : ξ != 0^∞}`, and `m` sends
      `e_ξ` to `0` or to `e_(αξ')` with `αξ' != 0^∞`. On the one-dimensional quotient `s_0, t_0 -> 1` and `m -> 0`.
    - Otherwise `m = s_0^a t_0^b` lies in `T`, and `χ` is the symbol at `ζ = 1`.

    Over `F_3`, `M_2(χ)` sends `z` to `−I`.
  - (d) `Φ(s_01 t_1) = s_1 e_01` and `Φ(s_1 t_01) = t_1 e_10`, so `W = R`. A nonzero map from the simple algebra `R` is
    injective and keeps `t_0 s_0 = 1 != s_0 t_0`.
- **Corollary 3.4, recomputed.**
  - `t_0 · s_0 t_1 = t_1`, so `W_5 = K<s_0, t_0, t_1>`. Words reduce by `t_0 s_0 = 1` and `t_1 s_0 = 0` to the
    monomials `s_0^a t_ν`.
  - (b) The images of the `e_ij` are matrix units summing to `1`, so `W = M_2(W')`. `W'` is a corner of a weakly finite
    algebra, so it is weakly finite, and `ψ∘Φ^(-1) = M_2(ψ')`. Proposition 3.3(b) with `β = 1` gives `ψ'(s_0 t_1) = 0`.
  - (c) `t_ν s_0^b` is `t_(ν'')` if `ν = 0^b ν''`, is `s_0^(b-c)` if `ν = 0^c` with `c < b`, and is `0` otherwise.
    - So the product of two basis monomials is `s_0^a t_(λν'')`, `s_0^(a+b-c) t_λ` or `0`.
    - `σ_5` is multiplicative in each case, since `|λν''| = |λ| + |ν| − b`, and the value is `0` once `ν` or `λ` has a
      `1`.
    - `σ_5(s_0 t_1) = 0`, so `x_23(1) -> I`.

### 36.4 Weakly finite models with D != 0 (Section 4). PASS

- **Theorem 4.1, recomputed.**
  - `F_3[Γ_0]` is stably finite by `linear-sofic-group-algebra-is-stably-finite` (ESTABLISHED): `Γ_0` is countable,
    and sofic groups are linear sofic.
  - `[z]` is central with `[z]^2 = 1`, so `ε_-^2 = 4(2 − 2[z]) = 2(1 − [z])` mod `3`.
  - A corner at a central idempotent of a stably finite ring is stably finite. `ρ(gh) = ε_-[g] ε_-[h]`, and
    `ε_-[z] = −ε_-`.
  - `x_23(1) x_12(1) = 1 + s_0 t_10 + s_10 t_11`, because `s_10 t_11 s_0 t_10 = 0`.
    - The four elements `1`, `x_12(1)`, `x_23(1)`, `x_23(1) x_12(1)` are `1` plus distinct sums of the independent
      monomials `s_0 t_10` and `s_10 t_11`.
    - Their `z`-multiples have coefficient `−1 != 1` on the monomial `1`.
    - So the eight terms of `D_ρ`, each with coefficient `±2`, are distinct and `D_ρ != 0`.
- **Corollary 4.2.** `ω(0) <= ω(10) = ω(1) + ω(0)`, and `ω(10) <= ω(11)` if and only if `ω(0) <= ω(1)`. `H^ω_≤` is
  countable and sofic (`depth-monotone-leavitt-subalgebras-are-stably-finite`, ESTABLISHED).
- **Theorem 4.3, recomputed.**
  - For large `k`, `F_k` is invariant under `g`, `h` and `gh`, so `(gh)_k = g_k h_k` and `(g^(-1))_k = g_k^(-1)`.
  - `AB = I` in `M_n(Q_3)` means `A_k B_k = I` for all large `k`, so `B_k A_k = I` for all large `k`.
  - `z_k^(⊗3) = (−1)^3 = −1`.
  - `mn = π(s_10 t_11 s_0 t_10) = 0`.
    - `(1 + n)^(⊗3) − 1 = Σ_(S != ∅) n^S`, and `m^T n^S` carries `mn` on `S ∩ T`.
    - Each coordinate lies in `S`, in `T` or in neither, so there are `3^3 − 2^3 − 2^3 + 1 = 12` survivors. Each has
      coefficient `1`, and their patterns in `{1, n, m}^(⊗3)` are distinct.
  - Put `(π(s_μ t_ν) f)(μξ) = f(νξ)`. Then `n 1_[10] = 1_[0]`, `m 1_[10] = 0`, `n 1_[11] = 0` and
    `m 1_[11] = 1_[10]`.
    - So `1`, `n`, `m` are independent, and the `27` elementary tensors in them are independent.
    - So `D_k != 0` for all large `k`, which is `D_(ρ_3) != 0` in `Q_3`.
- **Remark 4.4.**
  - `(gh)^* = h^* g^*`, so `g -> (g^*)^(-1)` is an automorphism of `G`. It exchanges `H^ω_≥` and `H^ω_≤`, and it sends
    `x_12(1)` to `1 − s_10 t_0`.
  - Advisory 3 in 36.5 concerns this remark's wording.

### 36.5 Section 5, claim displays, entries, routes, subsumption and scope. PASS

- **Section 5, item 1: the route `summand-obstruction-from-four-transvection-defect`, recomputed.**
  - A unital `ψ : S_- -> W` gives `ρ(g) = ψ(ε_- g)`, a homomorphism `G -> W^x` with `ρ(z) = ψ(−ε_-) = −1`.
  - `D_ρ` involves only `x_12(1)` and `x_23(1)`, both in `Γ_5`, so the OPEN claim gives `D_ρ = 0`.
  - `weakly-finite-leavitt-representations-killing-defect-are-trivial` (ESTABLISHED, characteristic `p > 0`,
    `Γ = R^x`) makes `ρ` trivial. Then `−1 = 1`, so `W = 0` in characteristic three.
  - The target says that no nonzero quotient of `S_-` is weakly finite. Such a quotient is a `W` as above, so the
    implication is valid, and the route is correctly OPEN.
- **Refuters, recomputed.**
  - Soficity: Theorem 4.1 applies to a sofic `Γ_5`, since `z` and `x_12(1)` lie in `<S4>`.
  - Finite quotients: let a finite quotient `Q` separate the eight elements.
    - The image of `z` is central of order two, so `ε_-` is a central idempotent of the finite-dimensional algebra
      `F_3[Q]`.
    - The same eight-term `D` is nonzero there.
- **Item 2.**
  - `jacobson-elementary-subgroups-are-locally-finite-by-linear` is ESTABLISHED (Section 31.1 here).
  - The Tits alternative holds for finitely generated linear groups in every characteristic.
    `SL_2(F_p[ζ, ζ^(-1)])` is not virtually solvable, so `<S4>` is not amenable and lies in no `U_< ⋊ P`.
  - A graph of groups with sofic vertex groups and amenable edge groups is sofic.
- **Items 3–4** restate Propositions 3.3(d) and 3.2(c).
- **Claim displays.**
  - Escape claim: items 1–4 are Theorem 1.1, Remark 1.2, Proposition 1.3 and Corollary 1.4, as recomputed in 36.1.
  - Symbol claim: items 1–5 are Theorem 2.1(a)–(c), Lemma 2.2, and Propositions 3.2 and 3.3(c)–(d). The
    non-amenability consequence is item 2 above.
  - Defect claim: items 1–4 are Theorem 4.1, Corollary 4.2, Theorem 4.3 and Lemma 3.1. The Scope is Remark 4.4.
  - OPEN claim: the statement, the refuters and the algebra-level Attempt are as recomputed. The Attempt is
    Corollary 3.4(b): a weakly finite image kills `s_1 t_1` and `s_0 t_1`.
- **Entries.** The two entries on the ternary nodes summarize Sections 1–5 accurately, subject to advisory 1.
- **Routes.**
  - `four-transvection-escape-proof` requires `depth-monotone-leavitt-subalgebras-are-stably-finite`, which is
    ESTABLISHED. Its steps are 36.1.
  - `four-transvection-symbol-firewall-proof` requires only the Alahmedi–Alsulami–Jain–Zelmanov normal form
    (literature). Its steps are 36.2–36.3.
  - `depth-monotone-tensor-cube-defect-proof` requires the depth-monotone node and
    `linear-sofic-group-algebra-is-stably-finite`, both ESTABLISHED. Its steps are 36.3–36.4.
- **Advisories (wording only).**
  1. "Every five-transvection set" means `S4 ∪ {T}`. The phrase appears in the Scope of the escape claim and in the
     first ternary entry. Section 5, item 4 says that other five-transvection sets are not covered.
  2. The symbol claim's consequence "An anti-central model that is not an algebra homomorphism needs at least six
     transvections" is about obstructions, not models. Suggested wording: "for a set containing `S4`, an obstruction
     that no algebra-level model defeats needs at least six transvections, or a relation outside the span of the
     group".
  3. Remark 4.4 says that `z -> −1` and `D != 0` "fail together only for algebra-level models", which is not proved.
     What is proved is Lemma 3.1, plus the non-additive models of Theorems 4.1 and 4.3. No claim display uses the
     stronger wording.
- **Subsumption scan at `39971c4c98`.** Seven phrases hit 145 research files: "tensor cube", "weakly finite corner",
  "one-sided inverse pair", "transvection set", `EL_2(J`, `SL_2(F_3[` and "nonzero defect". I read the claim and
  route nodes among them by title and hit line.
  - **Unitriangular groups, no `z`.** `unitriangular-data-cannot-assemble-corner-leavitt-families` and
    `unipotent-frame-relations-cannot-assemble-corner-cuntz-family` give rank models with nonzero two-root defect on
    unitriangular groups. Those groups do not contain `z`, so neither is the anti-central form. The defect claim may
    list the first in `distinct_from`.
  - **Inputs to the route.** `ternary-weakly-finite-representations-give-anti-central-images` and
    `no-weakly-finite-representation-from-summand-obstruction` relate representations and summand images, which the
    route uses.
  - **Different targets.** `ternary-defect-is-full-in-largest-weakly-finite-image` is a different OPEN target, and
    `rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup` is about Kazhdan subgroups of `EL_2(J_k)`.
  - **Other senses.** The remaining hits use the phrases in other senses: A8 certificates, one-hot encodings, Hamming
    defects, and orbits of one-sided pairs.
  - **Recorded.** `distinct_from` already records `depth-monotone-configurations-cannot-force-ternary-minus-one`,
    whose models kill `D`. It also records `anti-central-sofic-data-cannot-force-defect-submultiplicativity` (rank
    `5/9` on cylinder defects) and `ternary-weakly-finite-representations-kill-two-root-defect`.

  No duplicate.
- **Scope.** Each firewall exhibits a nontrivial weakly finite model. None forces a rank model, or `theta`, to be
  trivial. Still OPEN: soficity of `<S4>` and of `Γ_5`, whether `<S6> = G`, and conjugate frames inside `<S4>`.

## 37. w7-sub-multiletter follow-up (07136ca640)

Sources:
- Artifact `multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md` (blob `e60bf257`), Section 6.
- `lex-decreasing-units-with-order-preserving-letters-are-amenable` (blob `1d8fdf38`).
- `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (blob `915925b1`).

**Verdict: PASS. The correction of 35.4 has been applied.**
- **Lemma 6.1.** The hypothesis now requires that, for each of the frames at `A` and `A1`, all positive roots move
  points in one common direction.
  - The "Same direction" step carries the direction at `A` to `S[A10]T[A110]`, and so to the whole frame at `A1`.
  - The "Not preserved" step is unchanged.
  - This is the corrected statement of 35.4, proved by the same two steps.
- **Remark.** The added remark reproduces the counterexample of 35.4, including the block order
  `[A0] < [A10] < [A111] < [A110]`. It rests item 1 of Section 6 on the common-direction hypothesis, which is what
  Theorem 3.5 uses.
- **Wording.** Two places now say "monotone in one common direction":
  - the Scope of the lex claim;
  - the w7-sub-multiletter bullet on the SUB target.
- **Status.** No claim statement changed, so the PASS of Section 35 carries over to the new blobs.

## 38. w7-hexagon-closing (32f4345ad1, 91f646046f)

Sources:
- Artifact `hexagon-closing-letter-stage-obstruction-2026-09-12.md` (blob `6f8d62ac`), Sections 0–8.
- The OPEN claim `stage-models-cannot-close-the-leavitt-hexagon` (blob `96a06a51`).
- The lane's Attempts entry on `binary-complement-corner-has-no-weakly-finite-image` (blob `79ab0157`).
- Inputs verified here earlier: Theorem 1.1 of `mismatched-factor-graph-of-groups-firewall-2026-09-12.md` (Section
  29), and (SPG2) with point 4 of `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` (Section 34).

**Verdict: PASS on Sections 1–6 and the claim display.** No mathematical corrections. There are five advisories
(38.5), one of them about the requirements of the future route. Section 5's ternary transfer, which the artifact
leaves unverified, is re-derived in 38.4.

It is decision-level for the refutation side of `binary-complement-corner-has-no-weakly-finite-image`:
- no stage model closes the hexagon, exactly (Theorem 2.3, Corollary 2.4) or in rank (Proposition 3.1, with the
  uniform gap of Corollary 3.2);
- so a refutation needs a weakly finite target that is neither an algebraic ultraproduct of finite or
  commutative-linear matrix groups nor a monomial rank model.

Calibration holds: the argument uses finite presentation, the absence of finite quotients and nonsoficity of `G`, and
Section 4 exhibits closing models over `F_p`, `R_0` and `F_2[x]`. Nothing makes a rank model trivial. The binary
corner claim, the gate and Plan 1 stay OPEN.

### 38.1 The letter (Section 1). PASS

- **Edge groups, recomputed.** The roots positive at both ends of each edge are:

  | Edge | Orders | Common roots |
  |---|---|---|
  | `e_1` | `123 – 213` | `(1,3)`, `(2,3)` |
  | `e_2` | `213 – 231` | `(2,1)`, `(2,3)` |
  | `e_3` | `231 – 321` | `(2,1)`, `(3,1)` |
  | `e_4` | `321 – 312` | `(3,1)`, `(3,2)` |
  | `e_5` | `312 – 132` | `(1,2)`, `(3,2)` |
  | `e_6` | `132 – 123` | `(1,2)`, `(1,3)` |

  Each pair shares a source or a target, so `[x_ij(a), x_kl(b)] = 1` (`j != k`, `i != l`), and every edge group is
  `R ⊕ R`.
- **(1).** With the path as maximal tree and one off-tree edge carrying inclusions, `π_1(Y_hex)` is
  `<P, t | t x^132 t^-1 = x^123 (x ∈ K)>`. Killing `t` imposes `x^132 = x^123`. The `x` satisfying this form a
  subgroup, so `x_12(r)` and `x_13(r)` for `r ∈ B` suffice. With point 4 of the unstable-`K_2` claim this gives
  `G ≅ P/<<W_12(r), W_13(r)>>`.
- **(2).** `(1,2)` is positive exactly on `312, 132, 123`, and `(1,3)` exactly on `132, 123, 213`. The path cuts each
  arc only at `e_6`, and `e_5`, `e_1` carry the stated identifications.
- **(3).** Collapsing the vertex groups gives `π_1(Y_hex) -> Z`. It kills every conjugate of every `U_π` and sends `t`
  to a generator. So no `t^m` with `m != 0` is conjugate into a vertex group, and `t` is hyperbolic on the Bass–Serre
  tree.
- **(4).** In the firewall's Theorem 1.1 the letter permutations are the `π` with `π λ_132(k) π^-1 = λ_123(k)` for
  `k ∈ K_n`. Two of them differ by right multiplication by the centralizer of `λ_132(K_n)`. For `K` abelian acting
  freely on `K × [r]`, an equivariant bijection permutes the orbits and translates inside each, which gives
  `K wr Sym(r)`.

### 38.2 No exact closing (Section 2). PASS

- **Lemma 2.1.** Each relator holds at the chosen representatives on a `U`-large set. The finite intersection is
  `U`-large, and there `s -> g_(s,n)` defines `ρ_n` with `ρ(γ) = [ρ_n(γ)]` for every word `γ`.
- **Lemma 2.2, recomputed.**
  - **Binary.** `G` is infinite and simple.
  - **Ternary.** `St_3(R)` is perfect, since `x_ij(a) = [x_ik(a), x_kj(1)]`.
    - If `NZ = Z`, then `N ⊆ Z` is finite of finite index, and `G` would be finite.
    - If `NZ = G`, then `G/N ≅ Z/(N ∩ Z)` is abelian and perfect, so `N = G`.
  - **The host hypothesis.** The host theorem needs `K_1` and `K_2` to vanish. For `L_(F_3)(1,2)` the localization
    sequence multiplies `K_i(F_3)` by `1 − 2 = −1`, which is invertible. So `K_1 = K_2 = 0`.
  - **Linear targets.** A finitely generated subgroup of `GL_m(A)` with `A` commutative is residually finite
    (Malcev). An image of `G` has no nontrivial finite quotient, so it is trivial.
- **Theorem 2.3.** If `ρ(t) = 1`, then `ρ` factors through `G`.
  - `G` is finitely presented: `leavitt-unit-group-finitely-presented` (ESTABLISHED, literature import); ternary, the
    host theorem.
  - Lemma 2.1 gives `ρ_n : G -> H_n`, and Lemma 2.2 makes each trivial.
  - A Theorem 1.1 model takes values in `(prod_U M_(m_n)(F_p))^x = prod_U GL_(m_n)(F_p)`. It is nontrivial by (1) of
    that theorem, so `σ(t) != 1`.
- **Corollary 2.4, recomputed.**
  - **Edge pieces.** The firewall defines `K_(n,e) = {k ∈ K_e ∩ H_(n,v) : φ_e(k) ∈ H_(n,w)}` and notes that every
    finite subset of `K_e` lies in `K_(n,e)` for large `n` (its lines 64–66). So the stage diagrams increase and
    exhaust the hexagon diagram. Colimits commute, and `colim_n C_n = colim_π U_π = G` by (SPG2) (Section 34).
  - **Words.** Directed colimits of groups are computed on underlying sets. So an element of `C_n` that is trivial in
    the colimit is trivial at some later stage, and at every stage after that. The finitely many relators and
    `x_12(1)^-1 w` give `n_1`, which depends neither on the model nor on the finite target.
  - **The stage.** A homomorphism `f : C_n -> F` with `n >= n_1` sends each relator to `1`, so `s -> f(word)` defines
    `G -> F`. That map is trivial, so `f(x_12(1)) = f(w) = 1`.
  - **The model.** Suppose `id` were a letter permutation. Then the `λ_(n,π)` agree on all six `K_(n,e)`, which gives
    `C_n -> Sym(Ω_n)` with `x_12(1)` acting freely. That contradicts the stage step. So `id` is not in the coset
    `π_n^0 C_n` of Proposition 1.1(4) (advisory 1).
- **Remark 2.5.** `x_12(1) != 1` in `C_n`, since it maps to `x_12(1) != 1` in `G`. Every finite quotient kills it, so
  `C_n` is infinite and not residually finite.

### 38.3 No rank-null closing (Section 3). PASS

- **Proposition 3.1, recomputed.**
  - **Hamming.** `j` sends `prod_U Mon_(m_n)(F_q)` to `prod_U Sym(X_(m_n))`, where rank-null is Hamming-null
    (`monomial-rank-models-are-hamming-models`, ESTABLISHED, factor two). The null subgroup is normal, so the
    composite `π_1(Y_hex) -> prod_U Sym / null` kills `<<t>>`. It factors through `G`, nontrivially on `x_12(1)`.
  - **Binary.** The kernel is a proper normal subgroup of the simple `G`, so it is trivial. `G` embeds in a universal
    sofic group and is sofic (Elek–Szabó), which contradicts `openai-leavitt-unit-nonsofic`.
  - **Ternary.** The kernel `N` misses `x_12(1)`, so `NZ != G` by the argument of Lemma 2.2. Hence `N ⊆ Z`, and the
    image is `G` or `G/Z`.
    - `G` is nonsofic by `d-ary-leavitt-groups-nonsofic-over-finite-fields`.
    - `G/Z` is nonsofic by `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`. Alternatively, a sofic `G/Z`
      with `Z` finite would make `G` sofic (amenable extension).
  - **Coverage.** A Theorem 1.1 model is monomial (permutation matrices). `x_12(1)` has order `p` and acts freely, so
    `rk(σ(x_12(1)) − 1) = (p − 1)/p > 0`.
- **Corollary 3.2, recomputed.**
  - **The letter.** A permutation `π` has `rank(π − I) = |supp π| − (number of nontrivial cycles) >= |supp π|/2`.
    So `rank(π − I)/m < 1/k` gives `|supp π|/m < 2/k`, and `d_H(π a π^-1, a) <= 2|supp π|/m < 4/k`.
  - **Relators.** At the stage, vertex relations and forest identifications hold exactly. Each use of `e_6` costs at
    most `4/k`, since `d_H` is bi-invariant. So every relator holds up to `4L/k`, and `w` is within `4L/k` of the
    free permutation `λ(x_12(1))`.
  - **The limit.** Over `k`, the ultraproduct satisfies the relators exactly, which gives `G -> prod_U Sym / null`
    with `x_12(1)` at Hamming distance `1` from the identity. Proposition 3.1 excludes it.
  - **Uniformity.** `S`, `Q`, `w`, `D` and `L` are fixed before any model is chosen, so `ε_p` is uniform. For `p = 3`
    the models are those of 38.4.

### 38.4 Calibrations, ternary transfer and the rank-two kernel (Sections 4–6). PASS

- **Calibrations, recomputed.**
  - `|SL_3(F_2)| = 168 = 8 · 21` and `|SL_3(F_3)| = 26 · 24 · 18/2 = 5616 = 27 · 208`. The regular representation
    restricts to free actions of the `U_π(F_p)` that agree literally on every edge. So `σ(t) = 1` and `σ` is
    nontrivial.
  - `R_0`: each stage piece lies in the finite `GL_(3·2^k)(F_2)`, whose regular representation closes the stage.
    `EL_3(R_0)` is the union of the simple groups `SL_(3·2^k)(F_2)`, so it is infinite and simple but not finitely
    generated.
  - `F_2[x]`: `SL_3(F_2[x]/(f))` are finite quotients.
  - UT₄: a perfect group has no nontrivial nilpotent image.

  Each calibration closes the hexagon. None makes a rank model trivial.
- **Ternary transfer (Section 5), re-derived here.** Every step of the firewall's Theorem 1.1 (lines 53–95 there) is
  independent of the field:
  - `|H_(n,w)|` divides `N_n`, and free actions of one finite group on equal sets are isomorphic;
  - the orbit matching for letters;
  - `F_p[Ω_n] ≅ F_p[Q]^(N_n/|Q|)`, and the fixed-vector bound `1/|H_(m,v)|`;
  - `rank(I − AB) = rank(I − BA)` over a field.

  `U_π(L_(F_3)(1,2))` is countable and locally finite by the span argument of Section 34 with `F_3`-spans. So the
  `F_3` model exists with `M = prod_U M_(m_n)(F_3)`.

  The root-pair pieces: `[x_ij(ua), x_jk(vb)] = x_ik(uv ab)` is central, so the order is at most `27`. Since
  `(a, b, c)^3 = (3a, 3b, 3c + 3ab) = 1`, the exponent is `3`. Sections 2–3 for `p = 3` are conditional as the host
  theorem is.
- **Rank-two kernel.**
  - `(i,j)` and `(j,i)` are positive on complementary arcs, so no `U_π` contains opposite roots.
  - Over `F_2`, `[[1,1],[0,1]] [[1,0],[1,1]] = [[0,1],[1,1]]`, whose cube is `I`. So `ω -> 1` in `E_3(R)`, and in `G`
    by Section 34.
  - `x_12(1)` and `x_21(1)` lie outside `E_1 = <x_13(R), x_23(R)>`. So `ω` is a reduced alternating word of length
    `6` in `U_123 *_(E_1) U_213`, which embeds in the tree amalgam `P`. Hence `ω != 1` in `P`.
  - The `F_2` calibration kills `ω` at every stage.

### 38.5 Claim display, entry, subsumption and advisories. PASS

- **Claim display.**
  - Point 1 is Proposition 1.1(1)–(3). Point 2 is Theorem 2.3 and Corollary 2.4. Point 3 is Proposition 3.1 and
    Corollary 3.2. Point 4 is Section 4. All are as recomputed in 38.1–38.4.
  - Point 2 cites Theorem 1.1 through `graphs-of-locally-finite-groups-carry-regular-rank-models`, which is
    ESTABLISHED (Section 29).
  - The "Payoff" and "Not claimed" paragraphs match Section 7.
- **Inputs on main.**
  - `leavitt-unit-group-finitely-presented` is ESTABLISHED (literature import).
  - `monomial-rank-models-are-hamming-models`, `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` and
    `graphs-of-locally-finite-groups-carry-regular-rank-models` are ESTABLISHED.
  - `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` is ESTABLISHED conditional on its import.
  - `binary-leavitt-unit-group-is-simple`, `openai-leavitt-unit-nonsofic`,
    `d-ary-leavitt-groups-nonsofic-over-finite-fields` and `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`
    each have a proof route. I did not re-check those routes.
- **Entry** on `binary-complement-corner-has-no-weakly-finite-image` (its lines 74–90). It summarizes Sections 1–4 and
  7 accurately, except for the rank bullet (advisory 4).
- **Subsumption scan at `4e7e23aa0d`.** Six phrases hit 133 research files: "closing letter", "close the hexagon",
  "closes the hexagon", "hexagon closing", "no nontrivial finite quotient" and "kills the closing". I read the claim
  and route nodes among them by title and hit line.
  - **Same tool, different complex.** `leavitt-regular-atlas-asymptotic-permutation-cover` (its lines 93–100)
    excludes exact finite covers of the A8 atlas by the same no-finite-quotient argument, applied to `U_Q`. It is
    about atlas covers, not the hexagon letter. It may be listed in `distinct_from`.
  - **Same tool, other statements.** These nodes use the absence of finite quotients for other conclusions:
    - `binary-leavitt-unit-group-is-weakly-sofic` (weak soficity);
    - `simple-group-relator-width-in-finite-simple-targets` (relator width);
    - `large-window-table-groups-present-the-ambient-group` (window screens);
    - `atlas-rankwise-gap-is-ultraproduct-obstruction` (atlas gaps);
    - `finite-orbit-indices-miss-twists-without-finite-quotients` (orbit indices);
    - `thompson-v-not-lef` (LEF).
  - **Recorded.**
    - `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` mentions the letter in an entry.
    - `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` is already in `distinct_from`.
  - **Everything else.** The remaining hits are hyperbolic, Kazhdan, Rips, Higman, random-complex and Titz–Witzel
    nodes, plus artifacts. None concerns stage models of the hexagon.

  No duplicate.
- **Advisories.**
  1. `C_n` names two groups.
     - The centralizer `K_n wr Sym(r_n)`: Summary, Proposition 1.1(4), and the coset in Corollary 2.4's last sentence.
     - The six-piece colimit: Corollary 2.4, Remark 2.5, and claim point 2.

     Rename one, for example `Z_n` for the centralizer.
  2. The Summary and Remark 2.5 speak of "the finite six-piece colimit `C_n`". `C_n` is a colimit of finite pieces
     and is itself infinite. Suggested wording: "the six-piece colimit of finite pieces".
  3. **Route requirements (Section 8).** The claim covers `p = 3`, but the list names only binary inputs.
     - A route should also require `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` and
       `d-ary-leavitt-groups-nonsofic-over-finite-fields`.
     - It should also require `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`, as long as Proposition 3.1
       cites it. The claim's point 3 Inputs omit that node too.
     - Alternatively, the display keeps the ternary half conditional.
  4. **The entry's rank bullet.** It says "`rk(σ(t) - 1) >= ε > 0` in every monomial rank model", which fails for
     the trivial model. What is proved:
     - `rk(σ(t) − 1) > 0` in every monomial rank model with `rk(σ(x_12(1)) − 1) > 0` (Proposition 3.1);
     - the uniform `ε_p` in Theorem 1.1 models (Corollary 3.2).

     A diagonal ultraproduct gives a gap that is uniform over monomial rank models with
     `rk(σ(x_12(1)) − 1) >= δ`, for each `δ > 0`. Suppose `σ_k` violate `1/k`. Their ultraproduct over `k` is a
     monomial rank model with `rk(σ(t) − 1) = 0` and `rk(σ(x_12(1)) − 1) >= δ`, and the proof of Proposition 3.1
     works over any ultrafilter. The claim display (point 3) is already correct.
  5. Section 7 attributes to Arzhantseva–Păunescu the question whether linear sofic groups are sofic, from memory.
     That matches my recollection, but I did not check the source.
- **Scope.** Sections 2–3 obstruct stage models from closing the letter. They make no rank model trivial, and Section
  4 exhibits closing models wherever a hypothesis fails. Still OPEN: `binary-complement-corner-has-no-weakly-finite-image`,
  `binary-leavitt-unit-group-is-f2-linear-sofic`, the gate and Plan 1. The lane may create the route, with advisory 3.

## 39. w7-escape-set follow-up (6b94153534)

Sources:
- Artifact `four-transvection-escape-set-2026-09-12.md` (blob `bd8af4a3`).
- The claims `four-transvection-set-escapes-depth-monotone-units` (blob `01226942`),
  `four-transvection-units-have-a-weakly-finite-symbol-image` (blob `e957dd5f`) and
  `depth-monotone-units-carry-weakly-finite-nonzero-defect` (blob `2666d2b3`).
- The entry on `ternary-leavitt-units-have-no-weakly-finite-representation` (blob `275475a0`).
- The diff against `45282c2142`, read in full: 24 insertions, 15 deletions.

**Verdict: PASS. The advisories of 36.5 are applied, and no statement changed.**
- **Advisory 1.**
  - The escape claim's Scope, the symbol claim's `distinct_from` and the first ternary entry now say `S4 ∪ {T}`.
  - The Scope adds that other five-transvection sets are not covered.
- **Advisory 2.** The symbol claim's consequence now uses the suggested obstruction wording.
- **Advisory 3.**
  - Remark 4.4 now cites Lemma 3.1 and the non-additive models of Theorems 4.1 and 4.3, and says that other
    non-additive models are undecided.
  - The defect claim's consequence cites item 4 for the algebra-level case.
- **Optional note.** The `distinct_from` entry for `unitriangular-data-cannot-assemble-corner-leavitt-families` is
  added, and it describes that node as 36.5 does.
- **Status lines.**
  - The three claims now read ESTABLISHED. They cite their routes and Sections 36.1, 36.2–36.3 and 36.3–36.4, which
    matches the route verdict lines landed at `89d646844c`.
  - The artifact header cites Section 36.

## 40. w7-hexagon-closing follow-up and route (767ec353f4)

Sources: the diff of `767ec353f4`, read in full. It changes:
- the artifact (blob `2531cb49`);
- the claim (blob `7cd9eb6b`);
- the entry on `binary-complement-corner-has-no-weakly-finite-image` (blob `2b207bda`);
- the new route `stage-models-cannot-close-the-leavitt-hexagon-proof` (blob `ba6d5b55`).

**Verdict: PASS.** The advisories of 38.5 are applied and no mathematical statement changed. One residual rename
remains (advisory 1 below), and there is one optional advisory on the status line.

- **Advisories of 38.5.**
  1. **The `C_n` clash.**
     - The centralizer is now `Z_n` in the Summary, Proposition 1.1, proof step (4) and Remark 1.2.
     - Residual: artifact line 119 (Corollary 2.4, last sentence) still reads `id ∉ π_n^0 C_n`, where the coset of
       Proposition 1.1 is meant. It should read `π_n^0 Z_n`, as the route already does. This is wording only: the
       coset is defined in Proposition 1.1, and the argument of 38.2 is unaffected.
  2. **The colimit.** The Summary and Remark 2.5 now say "the six-piece colimit `C_n` of finite pieces".
  3. **The ternary inputs.**
     - The route requires all three: the prime-field host, d-ary nonsoficity and projective nonsoficity.
     - Point 3 of the claim now lists `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`.
     - Section 8 of the artifact matches the route.
  4. **The rank bullet.** The entry now says `> 0` when `rk(σ(x_12(1)) − 1) > 0`, with the uniform `ε_p` over the
     Theorem 1.1 models. The corner claim stays OPEN.
  5. **The attribution.** Section 7 now says it is from memory and unchecked.

  The `distinct_from` entry for `leavitt-regular-atlas-asymptotic-permutation-cover` is added.
- **Route requirements, checked on main at `cbaef238a3`.** All ten nodes exist.
  - `steinberg-group-is-glued-over-the-permutohedron` (the (SPG2) source used in Section 34) is ESTABLISHED.
  - `leavitt-unit-group-finitely-presented` is ESTABLISHED (literature import).
  - `leavitt-unit-groups-have-no-unstable-k2-at-rank-three`, `graphs-of-locally-finite-groups-carry-regular-rank-models`
    and `monomial-rank-models-are-hamming-models` are ESTABLISHED.
  - `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` is ESTABLISHED, conditional on its import.
  - `binary-leavitt-unit-group-is-simple`, `openai-leavitt-unit-nonsofic`,
    `d-ary-leavitt-groups-nonsofic-over-finite-fields` and `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`
    each have a route, which I did not re-check.

  No requirement is missing: the argument of 38.1–38.4 uses exactly these, together with Elek–Szabó and Malcev
  (literature).
- **Route body.** It summarizes 38.1–38.4 correctly:
  - the letter and the coset `π_n^0 Z_n`;
  - no exact closing, through finite presentation, no finite quotients, Malcev, Łoś and per-stage colimits;
  - no rank-null closing, through the Hamming comparison, a kernel that is `1` or lies in `Z`, and Elek–Szabó;
  - the uniform `ε_p` from `rank(π − I) >= |supp π|/2` and relator error `4L/k`;
  - the ternary transfer.

  The lane wrote the verdict line in the verifier's format, citing Section 38. I replace it here with the line citing
  Sections 38 and 40.
- **Optional advisory on the status line.** The claim reads "**Proof verified.**". The escape-set claims (Section 39)
  use `**ESTABLISHED**` with their routes cited. A matching line here would say that the claim is ESTABLISHED, and
  for `p = 3` conditional on the import of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`.
- **Scope.** Unchanged from 38.5. Still OPEN: `binary-complement-corner-has-no-weakly-finite-image`,
  `binary-leavitt-unit-group-is-f2-linear-sofic`, the gate and Plan 1.

## 41. w7-hexagon-closing final fix (a2c10e4f68)

Sources: the diff of `a2c10e4f68`, read in full. It changes the artifact (blob `6f985740`) and the claim (blob
`6e95eb55`).

**Verdict: PASS.**
- **The residual of 40.** Artifact line 120 (Corollary 2.4, last sentence) now reads `id ∉ π_n^0 Z_n`. No
  `π_n^0 C_n` is left, and `C_n` names only the stage colimit.
- **Status line.** The claim now reads `**ESTABLISHED**`. It cites the route and Sections 38 and 40, and makes
  `p = 3` conditional on the import of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`. That is the
  optional advisory of 40, stated correctly.
- **Everything else.** Line rewrapping and Attempts entries only. No statement changed, and the route is untouched.
- **Scope.** Unchanged. Still OPEN: `binary-complement-corner-has-no-weakly-finite-image`, the gate and Plan 1.
