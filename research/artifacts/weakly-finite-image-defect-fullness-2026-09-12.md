# Defect fullness in the largest weakly finite image of the ternary anti-central summand

Lane `w7-wdw-fullness`, 2026-09-12. Paper only, no compute. Every result here is held OPEN until `w4-vf-linear-b`
re-derives it.

Sources:
- [MSD] `research/artifacts/matrix-state-deficit-item-two-2026-09-12.md`, Lemmas 5.1 and 5.2;
- [WFR] `research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md`, Theorems 1–3;
- [GATE] `research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md`, Section 1, step 3;
- [RR] `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md`, Proposition 8 and Corollary 9;
- [TRI] `el3-unit-root-matrix-units-iff-two-root-identities`, Theorem A;
- [CHAIN] `research/artifacts/gk-vf-chain-verification-2026-09-12.md`, Sections 3–4;
- census Theorem E (`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`);
- Theorem C (`rank-condition-rings-have-weakly-finite-images`).

## 0. Summary

1. **The defect ideal is the evaluation kernel (Theorem 2.1).** `S_- D S_- = ker pi` and `S_-/S_- D S_- ≅ R`.
   So for every quotient `W` of `S_-`, `W/WDW` is `0` or `R`. Case 2 of [MSD] Lemma 5.2 says exactly that `pi` factors
   through `W`, and it fails the rank condition because `R ≅ R^2`.
2. **Fullness in `W_max` is a refutation target sitting between the corner and stage one (Theorem 3.1).** Every
   implication runs one way only:
   - `F3 ⟹ VIS1 ⟹ FULL ⟹ SF3 ⟹ Gott3`;
   - `Rep3 ⟹ WF_- ⟹ FULL`;
   - `¬FULL` maps `W_max` onto `R`, which gives a nontrivial weakly finite representation and kills both corner routes.

   So deciding Lemma 5.2 for `W_max` decides between a stage-one refutation and the death of the corner routes. Neither
   side is decided.
3. **`D^((+)k)` does not pass to `D` (Proposition 4.1).** In a weakly finite skew Laurent domain over `F_3`, `D = 1 + x`
   has `I_1 <~ D^((+)3)` and no nonzero idempotent minor. In artinian rings the passage holds.
4. **Models (Section 5).**
   - Inside `GL_3(F_3) <= G`, the natural module kills `D`, and the dual module gives a weakly finite image in which `D`
     is full while `J_1 = 0`.
   - So fullness refutes nothing without maximality and `pi`.
5. **`W_max` inherits the halving (Proposition 1.2).** `W_max ≅ M_2(e_H W e_H)`, with a unital map `W -> e_H W e_H`.

## 1. Setting and `W_max`

- **The group.** `R = L_(F_3)(1,2)`, which is simple, and `G = R^x = EL_3(R)` through the three-leaf prefix code.
  `z = -1 = -I_3`.
- **The summand.** `eps_- = 2(1 - [z])` and `S_- = eps_- F_3[G]`.
- **The defect.** `N_ab = [x_ab(1)] - 1` and `D = N_23 N_12`.
- **The evaluation.** `pi : F_3[G] -> R`, `[g] -> g`, restricts to a unital surjection `S_- -> R` with
  `D -> e_23 e_12 = 0` ([MSD] Section 5, Facts).
- **The reflection stages.** `J_k` and `J_omega` are those of [WFR] Theorem 1, applied to `S_-`.

**Proposition 1.1 (`W_max`).** `J_omega = ∩{I : S_-/I weakly finite}`. So `W_max = S_-/J_omega` is the largest weakly
finite image: every homomorphism from `S_-` into a weakly finite ring factors through it. Moreover `W_max = 0` iff
`ternary-anti-central-summand-has-no-weakly-finite-image` holds.

*Proof.*
- By [WFR] Theorem 1(a),(b), `S_-/J_omega` is weakly finite, and `J_omega` lies in every kernel into a weakly finite
  ring. So `J_omega` is the intersection.
- **Size.** Images of `S_-` are indexed by ideals, which form a set. The product of the weakly finite quotients is
  weakly finite, because `AB = I_n` is checked coordinatewise. `S_-/J_omega` is the image of `S_-` in that product.
- The last sentence is [WFR] Theorem 1(c) with Corollary 1.2. QED

**Proposition 1.2 (the halving descends).** Take `e_H`, `T = e_H S_- e_H`, `S_- ≅ M_2(T)` and the unital homomorphism
`h : S_- -> T`, `h(x) = e_H Δ(x)`, from census Theorem E, where `Δ` is the diagonal endomorphism. Let `W = W_max`, and
write `ē` for the image of `e_H`. Then:
- `W ≅ M_2(ē W ē)`;
- `h` descends to a unital homomorphism `W -> ē W ē`;
- so there is a unital homomorphism `M_2(W) -> W`.

*Proof.*
- The matrix units behind `S_- ≅ M_2(T)` map to matrix units of `W` with the same sum.
- The composite `S_- -> T -> ē W ē` is unital into a corner of `W`, and corners of weakly finite rings are weakly finite
  ([WFR] Theorem 2, step 4). So its kernel contains `J_omega` ([WFR] Theorem 1(b)). QED

## 2. The defect ideal is the evaluation kernel

**Theorem 2.1.** `S_- D S_- = ker(pi|_(S_-))`, and `pi` induces `S_-/S_- D S_- ≅ R`.

*Proof.* Put `Q = S_-/S_- D S_-`, and let `rho : G -> Q^x` send `g` to the image of `eps_- [g]`. Then `Q` is spanned by
`rho(G)`, `rho(z) = -1` and `rho(D) = 0`.
1. **Squares.** `reversed-root-pair-identity-forces-root-squares-to-vanish` (group relations and units only) gives
   `N_ab^2 = 0` in `Q`.
2. **Matrix units.** [TRI] Theorem A, with `M = Q`, gives orthogonal idempotents `p_i` and `u_ij ∈ p_i Q p_j` with:
   - `rho(x_ij(1)) = 1 + u_ij`;
   - `u_ij u_jk = u_ik` and `u_ij u_ji = p_i`.

   Put `u_ii = p_i`, `p = p_1 + p_2 + p_3` and `f = 1 - p`.
3. **Block support and the corner map.**
   - [RR] Proposition 8 gives `rho(x_ij(a)) = 1 + psi_ij(a)` with `psi_ij(a) ∈ p_i Q p_j`, for every `a ∈ R`. Its proof
     is ring algebra ([GATE] Section 1, step 3).
   - The computation of [RR] Corollary 9 gives a unital ring homomorphism `C : R -> p_1 Q p_1`,
     `C(a) = psi_12(a) u_21`.
4. **Root elements through `C`.** Let `X ∈ p_i Q p_k` and `Y ∈ p_k Q p_j` with `i, k, j` distinct. Then
   `X^2 = Y^2 = YX = 0`, so `[1 + X, 1 + Y] = 1 + XY`. With `[x_ik(a), x_kj(b)] = x_ij(ab)`:
   - `psi_12(a) = psi_12(a) p_2 = C(a) u_12`;
   - `psi_13(a) = psi_12(a) u_23 = C(a) u_13`, and `psi_32(a) = u_31 psi_12(a) = u_31 C(a) u_12`;
   - `psi_23(a) = u_21 psi_13(a) = u_21 C(a) u_13`, and `psi_31(a) = psi_32(a) u_21 = u_31 C(a) u_11`;
   - `psi_21(a) = psi_23(a) u_31 = u_21 C(a) u_11`.

   So `psi_ij(a) = u_i1 C(a) u_1j` for every root.
5. **The matrix map.** `Phi : M_3(R) -> pQp`, `Phi(sum E_ij(r_ij)) = sum u_i1 C(r_ij) u_1j`.
   - It is a ring homomorphism with `Phi(I_3) = p`, because `u_1j u_k1 = δ_jk p_1` and `C(r) p_1 C(s) = C(rs)`.
   - By step 4, `rho(x_ij(a)) = f + Phi(x_ij(a))`.
   - `f Phi = Phi f = 0`, so `g -> f + Phi(g)` is multiplicative. Hence `rho(g) = f + Phi(g)` for all
     `g ∈ EL_3(R) = G`.
6. **The complement vanishes.** `z = -I_3`, so `-1 = rho(z) = f - p = -1 + 2f`. So `2f = 0`, and `f = 0`.
7. **Simplicity.**
   - `Q` is spanned by `rho(G) ⊆ Phi(M_3(R))`, so `Phi` is a unital surjection `M_3(R) -> Q`.
   - `M_3(R)` is simple because `R` is.
   - `Q != 0`, because `pi` kills `S_- D S_-` and `pi(eps_-) = 1`.
   - So `Q ≅ M_3(R)` is simple. Since `S_- D S_- ⊆ ker pi != S_-`, the two ideals are equal. QED

**Corollary 2.2 (Lemma 5.2 sharpened).** Let `W = S_-/I` be any quotient.
- `W/WDW ≅ S_-/(I + S_- D S_-)`, and this is `0` or `R`.
- It is `R` iff `I ⊆ ker pi`, i.e. iff `pi` factors through `W`. Then it fails the rank condition because `R ≅ R^2`,
  with no appeal to Theorem 2.3.4 of the `w6-upg-separate` artifact.
- `WDW = W` iff `pi(I) != 0`, and then `pi(I) = R`.

*Proof.* Ideals of `S_-` that contain `S_- D S_-` correspond to ideals of the simple ring `R`. QED

**Corollary 2.3 (visible defects).** `D` is full in `W_max` iff `pi(J_omega) != 0`. That holds iff, for some `k >= 1`:
- `pi(J_(k-1)) = 0`;
- and some pair `(A, B)` of square matrices over `S_-` with `AB - I ∈ M(J_(k-1))` has `pi(BA) != I`.

Call such a pair a *Leavitt-visible defect at stage `k`*.

*Proof.*
- The first equivalence is Corollary 2.2 with `I = J_omega`.
- Take `k` minimal with `pi(J_k) != 0`. Some generator `BA - I` of `J_k` has nonzero image.
- `pi(J_(k-1)) = 0` gives `pi(A) pi(B) = I`. QED

## 3. One-directional implications

**Statements.**
- **(F3)** `c e_- b = eps_-` is solvable in `S_-` (`ternary-anti-invariant-swap-corner-is-full`).
- **(WF_-)** `W_max = 0`.
- **(Rep3)** Every weakly finite `F_3`-representation of `G` is trivial.
- **(VIS1)** `pi(J_1(S_-)) != 0`: an exact one-sided pair over `S_-` with a Leavitt-visible defect.
- **(FULL)** `eps_- ∈ J_omega + S_- D S_-` (`ternary-defect-is-full-in-largest-weakly-finite-image`).
- **(SF3)** `J_1(S_-) != 0`, so `F_3[G]` is not stably finite.
- **(Gott3)** `G` is not surjunctive.

**Theorem 3.1.**
- (a) `Rep3 ⟹ WF_- ⟹ FULL`.
- (b) `F3 ⟹ VIS1 ⟹ FULL`.
- (c) `FULL ⟹ SF3 ⟹ Gott3`.
- (d) `¬FULL` iff `pi` factors through `W_max`. Then `W_max != 0`, so `S_-` has the rank condition, and `¬F3` and
  `¬Rep3` follow.

Parts (a), (c) and `F3 ⟹ VIS1` do not use Theorem 2.1. `VIS1 ⟹ FULL` and the equivalence in (d) do.

*Proof.*
- **(a)** `Rep3 ⟹ WF_-` is elementary ([CHAIN] Section 3): a weakly finite image of `S_-` sends `z` to `-1`. If
  `W_max = 0`, then `D` is full in it.
- **(b), `F3 ⟹ VIS1`.**
  - `a = e_- b` and `c` satisfy `ca = eps_-`, so `eps_- - ac ∈ J_1`.
  - If `pi(eps_- - ac) = 0`, then `pi(e_-) pi(bc) = 1`. So the idempotent `pi(e_-)` is right invertible, hence
    `pi(e_-) = 1`.
  - But `pi(e_-) = 2(1 + w)` with `w = s_0 t_1 + s_1 t_0`, and `2(1 + w) = 1` forces `w = 1`, while `w s_0 = s_1 != s_0`.
- **(b), `VIS1 ⟹ FULL`.** `J_1 ⊆ J_omega`, then Corollary 2.3.
- **(c)**
  - Write `eps_- = j + sum a_i D b_i` with `j ∈ J_omega`. Applying `pi` gives `pi(j) = 1`, so `J_omega != 0`.
  - So `J_1 != 0` by [WFR] Theorem 1(d).
  - `S_-` is a direct factor of `F_3[G]`, so `F_3[G]` is not stably finite, and
    `stable-finiteness-failure-refutes-surjunctivity` gives `Gott3`.
- **(d)**
  - `¬FULL` iff `pi(J_omega) = 0` (Corollary 2.3), iff `pi` factors through `W_max`. Then `W_max` maps onto `R != 0`.
  - `W_max != 0` is the rank condition on `S_-` (Theorem C), and that gives `¬F3` by census Theorem E.
  - A nonzero weakly finite image of `S_-` is a nontrivial weakly finite representation ([WFR] Theorem 3,
    (iii) ⟹ (i)). QED

**What is not claimed.** No converse.
- `FULL ⟹ F3` is not claimed. `FULL` with `W_max != 0` is a nonzero weakly finite image in which the visible defect
  appears only at a stage `k >= 2`, or at stage 1 with no corner.
- `SF3 ⟹ FULL` is not claimed. A stage-one defect may lie in `ker pi`, the invisible kind of
  `ternary-anti-central-kernel-unitization-not-directly-finite`.
- `Gott3 ⟹ SF3` is the converse of the linear-automaton criterion ([CHAIN] Section 4).
- In particular this gives no "counterexample ⟺ no representation".

**Reading.**
- Deciding [MSD] Lemma 5.2 for `W_max` is a fork. Case 1 (`FULL`) refutes Gottschalk at stage one, with a defect that
  `pi` sees. Case 2 is a weakly finite representation whose image maps onto `R`: both corner routes die, and Gottschalk
  stays open.
- In form, `FULL` lies between `WF_-` and `SF3`. It is weaker than the corner, and it names where the stage-one
  collapse must be seen.

## 4. From `D^((+)k)` to `D`

**Proposition 4.1.** There is a weakly finite `F_3`-algebra `S`, and `D ∈ S`, such that `I_1 <~ D^((+)3)` but `D` has no
nonzero idempotent minor. So "`I_1 <~ D^((+)k)` in `W`" does not in general give "`D` has a nonzero idempotent minor in
`W`".

*Construction.* Let `K = F_3(t_i : i ∈ Z)`, let `sigma(t_i) = t_(i+1)`, and let `S = K[x, x^-1; sigma]` with
`x a = sigma(a) x`. Put `D = 1 + x`.
- **Weakly finite domain.** `S` lies in the skew Laurent series ring `K((x; sigma))`, which is a division ring.
  Subrings of division rings are domains and weakly finite, since `M_n` of a division ring is artinian. This is standard
  and was not read locally.
- **`I_1 <~ D^((+)3)`.** Take `c = t_0` and `u = (t_1 - t_0)^-1`. Then `Dc - cD = (sigma(c) - c) x`, so
  `1 = D - u D c + u c D`.
- **`D` is not a unit.** The lowest and highest degrees of a product add, so the units are the monomials `a x^n`.
- **No idempotent minor.**
  - Let `e = X D Y` be an idempotent, with `X` a column and `Y` a row.
  - As in [MSD] Lemma 5.1, `g = (YX) D` satisfies `g^3 = g^2`, and `e = X D g^2 Y`.
  - In a domain this forces `g = 0` or `g = 1`.
  - If `g = 0`, then `e = 0`.
  - If `g = 1`, then `D` is left invertible. From `(D YX - 1) D = 0` it is invertible, a contradiction. QED

**The obstruction.**
- Fullness is a property of the two-sided ideal, and it survives in rings with no idempotents. An idempotent minor
  needs a nonzero idempotent in the one-sided ideal `WD` ([MSD] Lemma 5.1).
- In an artinian ring, `D` full means `D` is not in the radical. Then `DW` contains a nonzero idempotent (Brauer's
  lemma), so finite-block models never show the gap.
- A passage in `W_max` must use more than fullness, for instance a relation `D = D y D`.

## 5. Model tests

| statement | model | outcome |
|---|---|---|
| Theorem 2.1 | `GL_3(F_3) = SL_3(F_3) × <z> <= G`, with `z = -I_3` | Steps 1–5 run over `EL_3(F_3) = SL_3(F_3)`. But `det z = -1`, so `z` is not elementary and step 6 is unavailable. The complement survives: `eps_- F_3[GL_3(F_3)]/(D) = F_3 f × Phi(M_3(F_3)) ≅ F_3 × M_3(F_3)`, i.e. the character `det` and the natural module `V`, both of which kill `D`. Over `R`, `z ∈ EL_3(R)` and `f = 0`. Check: on the dual `V*`, `N_12 -> -e_21`, `N_23 -> -e_32` and `D -> e_31 != 0`. Consistent. |
| Theorem 2.1 | `UT_3(R) × <z> <= G`: positive roots only, as in the firewall of `research/artifacts/heisenberg-and-rank-four-positive-root-firewall-2026-09-12.md` | Fails there. Take a linear `lambda : R -> F_3` with `lambda(1) = 1`. On `F_3^2`, let `x_12(a) -> 1 + lambda(a) e_12`, let `x_23` and `x_13` act trivially, and let `z -> -1`. This module kills `D`, and its image `F_3[e_12]` is not simple. The proof needs lower roots (`p_i = N_ij N_ji`). Consistent. |
| Theorem 3.1(c) | `End(V*) = M_3(F_3)`, an image of `eps_- F_3[GL_3(F_3)]` | `D` is full and `J_1 = 0`. This image is not the largest one, and no evaluation that kills `D` factors through it. So (c) needs both maximality and `pi`. |
| Theorem 3.1(c), contrapositive | sofic `H` with a homomorphism to `G` matching `z` and the root pair, e.g. the locally finite `GL_3(F_3)` and `UT_3(R) × <z>` | `F_3[H]` is stably finite (Elek–Szabó), so `W_max(H) = eps_- F_3[H]`. The evaluation through `G` kills `D` and sends `eps_-` to `1`, so `D` is not full: case 2 in their own scope. So sofic sub-data cannot prove FULL. |
| FULL | HNN `H(Λ, I)`, Fock `𝒢_loc(I)`, graph-of-groups `pi_1(Y)` | Each maps to `G`, so `pi_H` exists and (c) applies to `W_max(H)`. Their rank models are weakly finite images with `D != 0`. Whether `D` is full in `W_max(H)` is not computed. The graph-of-groups node is in characteristic two, so it is off scope here. |
| Proposition 4.1 | finite blocks | Artinian, so the passage holds (Brauer). Consistent with no gap being seen there. |

## 6. U1b on `S_-`: special structure recorded

- **Halving.** `W_max ≅ M_2(ē W ē)`, with a unital `W -> ē W ē` (Proposition 1.2). So the halving map on states of
  `ternary-anti-central-unit-class-is-nonpositive` acts on states of `W_max`.
- **Faithfulness.** Perfection of `G` and simplicity of `PG` make every nonzero weakly finite image of `S_-` faithful on
  `G` ([WFR] Theorem 3, (i) ⟹ (ii)).
- **What a rank function on `W_max` must do with `D`.**
  - In case 2, `D` generates a proper ideal whose quotient is `R`, and `R` has no state.
  - In case 1, `D` is full, but that need not give an idempotent minor (Proposition 4.1).
  - Neither case forces or forbids a rank function on `W_max`.
- **No mechanism** was found for Hung–Li Question 3.4 on `S_-`.

## 7. Where it stops

- **Proved on paper, all held OPEN:** Propositions 1.1 and 1.2, Theorem 2.1, Corollaries 2.2 and 2.3, Theorem 3.1 and
  Proposition 4.1.
- **Open:**
  - `ternary-defect-is-full-in-largest-weakly-finite-image` (FULL);
  - `ternary-anti-central-defect-ideal-is-the-evaluation-kernel` (Theorem 2.1, awaiting re-derivation);
  - `anti-central-weakly-finite-images-carry-rank-functions` (U1b).
- **Next lead.** Find a Leavitt-visible defect: a pair `(A, B)` over `S_-` with `AB ≡ I` modulo a stage `J_(k-1)` that
  `pi` kills, and `pi(BA) != I`.
  - At stage 1 this is an exact one-sided pair lying over a non-invertible pair of `R`, such as `(s_0, t_0)`.
  - Its negation says every reflection stage is invisible to `pi`, i.e. the evaluation factors through `W_max`.
