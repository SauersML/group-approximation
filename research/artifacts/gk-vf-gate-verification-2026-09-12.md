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
