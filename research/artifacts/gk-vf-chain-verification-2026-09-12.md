# Verification of the weakly finite counterexample chain

Lane `w6-vf-chain`, 2026-09-12, read at main `83204067f`.

**Scope.** Theorem C, binary Theorem B with Proposition C, Theorem W, the weakly finite reflection ideal, defect
triviality, the ternary anti-central images, the flattening results, and the triangular certificate criterion. These
are the premises behind the single-statement forms of the binary and ternary counterexample routes.

**Coverage.** At the read tip all thirteen routes of these claims already carry `w4-vf-linear-b` PASS lines (commits
`1dc81f2a2` and `820fa3ebf`; Sections 28.1, 29.4–29.5, 32, 35–37 of
`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`). This lane does two things:
- Section 1 spot-checks the hardest step of each independently, with the quantifiers checked.
- Sections 2–4 assemble the end-to-end chains from each counterexample statement to its single-statement form,
  including the external inputs. No verifier had assembled them.

## 1. Spot-checks: PASS throughout

### 1.1 Theorem C and Corollary C.2: PASS

Claims `rank-condition-rings-have-weakly-finite-images` and `anti-central-rank-condition-gives-weakly-finite-image`.
- **Retract lemma.**
  - Put `K = UẼV` with `Ẽ² = Ẽ`, `X' = [[X],[ẼV]]` and `Y' = [Y, −UẼ]`.
  - Then `Y'X' = YX − UẼ·ẼV = I_(n+1)`, so `A^(n+1)` is a retract of `A^n ⊕ ẼA^R`.
  - State form: `n + 1 <= n + s([Ẽ]) = n`.
  - Class-zero form, the one the route uses: `ẼA^R ⊕ A^r ≅ A^r`, which gives an epimorphism `A^(n+r) -> A^(n+1+r)`.
- **Maximality is applied in the quotient.** The lemma is used for idempotent matrices over `W = A/J` whose class in
  `K_0(W)` is zero. The preimage in `A` of the ideal they generate has a quotient satisfying the rank condition, so it
  equals `J`.
- **Properness.** The zero ring fails the rank condition at `n = 0`. So the maximal `J` is proper and `W != 0`.
- **Weak finiteness.** `AB = I_n` makes `BA` Murray–von Neumann equivalent to `I_n`. So `I_n − BA` has class zero in
  `K_0(W)`, and it vanishes.
- **Quantifiers.**
  - The rank condition, weak finiteness and the retract are all matrix statements, for every `n`.
  - The class-zero form needs no state and no order unit.
  - The state form needs states normalized at `[W]`. They exist by the census criterion, because `W` satisfies the
    rank condition.
- **Corollary C.2.** Over `F_3`, `1 − z -> 2·1_W != 0`, so the kernel of `G_3 -> W^x` misses `z`.

### 1.2 Binary Theorem B and Proposition C: PASS

Claims `binary-cyclic-corner-full-iff-complement-corner-has-no-state` and
`binary-complement-corner-rank-functions-pull-back-to-units`.
- **Lemma 1.1.** `D(h)[g] = Σ_j s_σ(j) h t_j = [g]D(h)`, where `σ` is the 3-cycle of `g`. So `D` commutes with `e` and
  `f`, and `ψ'` is a unital homomorphism into `T`.
- **Lemma 1.2(d).** `D(e) = e_(K_2) = e_(A_9) + f_(K_2)`. So `ψ'(f) = f − f_(K_2) = f_(K_3) + f_(K_4)`.
- **Lemma 1.2(b), (c).**
  - The `π_M` act transitively on the four lines, so `v = 3[f_(K_1)A] = 3d_1`.
  - `F^k(d_0) = d_k` gives `v = 3^k d_k`.
  - `e = E_(k+1) + Σ_(l=1..k)(E_l − E_(l+1))` gives the count `(3^k − 1)/2`.
- **Lemma 1.3.** A retraction `φ : eA -> A` satisfies `φ(y) = φ(e)y`. So `c = φ(e)` and `b = m`.
- **6 ⇒ 2.**
  - `Nv + v + q = Nv` iterates to `Nv + jv + jq = Nv`.
  - Applying `F^k` with `j = 3^k` gives `Nd_k + v + x = Nd_k`.
  - Once `(3^k − 1)/2 >= N`, we have `p = Nd_k + c`, and hence `u + x = p`.
- **Quantifiers.**
  - Statement 6 is the stable form `[T] <= 0`. It is equivalent to failure of the matrix rank condition, because an
    epimorphism of free modules splits.
  - `ψ'` is unital, so the pulled-back state is normalized at `[A]`, and it gives `[f]` the value `2/3`.
  - Proposition C(b) uses simplicity of `G` (Section 2).

### 1.3 Theorem W: PASS

Claim `binary-corner-weakly-finite-images-are-unit-representations`.
- **Lemma W.2.**
  - The stabilizer of `K_1` in `GL_2(F_3)` acts on the other three lines as `AGL_1(F_3)`. So some `M` fixes `K_1` and
    sends `K_3` to `K_2`.
  - Then `π_M e π_M^(-1) = e`. So `x = π_M f_(K_3) = f x f` lies in `T`, and `xy = f_(K_2)`.
  - Hence `q(f_(K_2)) = q(x) q(f_(K_3)) = 0`.
- **(a) ⇒ (c)** uses only size-one direct finiteness of `W`. `φ(e)` has the one-sided inverses `φ(ebc)` and `φ(bce)`, so
  `φ(e) = 1`. Then `φ(f) = u(1 + u) = 0` gives `u = 1`.
- **(b) ⇒ (a)** uses weak finiteness at every size, through Theorem C.
- **(d)** quantifies over all weakly finite rings of characteristic two. Characteristic two is exactly what extends `ρ`
  to `F_2[G]`.
- **Simplicity.** (d) ⇒ (c) needs no simplicity. (c) ⇒ (d) needs simplicity of `G`.

### 1.4 Reflection ideal, defect triviality, ternary anti-central images: PASS

Claims `weakly-finite-reflection-ideal-detects-weakly-finite-images`,
`weakly-finite-leavitt-representations-killing-defect-are-trivial` and
`ternary-weakly-finite-representations-give-anti-central-images`.
- **`J_omega`.**
  - A pair modulo `J_omega` uses finitely many entries, all in one `J_k`, so its defect lies in `J_(k+1)`.
  - Universality follows by induction on `k`.
  - Part (d): `J_1 = 0` gives `Phi(0) = 0`.
- **Defect triviality, step 4.**
  - In the weakly finite corner, `C(t_0)C(s_0) = p_1` gives `C(s_0)C(t_0) = p_1`, so `C(s_1 t_1) = 0`.
  - Then `p_1 = C(t_1) C(s_1 t_1) C(s_1) = 0`.
  - Steps 1–3 are cited from `w3-vf-linear` Section 23 and were not re-derived here. They carry only (i) ⟺ (iv) of
    Theorem 3, which is not on the equivalence chain.
- **Theorem 3, the cut.**
  - Put `f = 2(1 − u)` with `u² = 1`. Over `F_3`, `f² = 4(2 − 2u) = 8(1 − u) = f`, and `fu = −f`.
  - So `eps_+ = 2(1 + [z]) -> 2(f − f) = 0`, and the map factors through `S_-`.
  - The image is a subring of `fWf` with unit `f != 0`. It is weakly finite by padding with `1 − f`.
- **Quantifiers.** A weakly finite representation is a homomorphism into the units of an arbitrary weakly finite
  `F_3`-algebra. The notion is not restricted to matrices or rank models.

### 1.5 Flattening and the triangular criterion: PASS

Claims `separated-triangular-steps-flatten-to-minors`, `nilpotent-jordan-certificates-flatten-to-minors`,
`k0-state-extends-to-rank-function-iff-triangular-monotone` and `sylvester-rank-functions-iff-no-triangular-certificate`.
- **Lemma S.**
  - `𝓛W𝓡 = [[L_A A R_A + L_1 Z_1 R_1, L_A C R_B], [0, L_B B R_B + L_2 Z_2 R_2]]`.
  - `f` and `g` are idempotent. So compressing by `diag(f, g)` and then multiplying on the right by
    `[[f, −fDg], [0, g]]` gives `f ⊕ g`.
- **Corollary J.** `[[I,0],[−U,I]] · [[V,I],[0,U]] · [[I,0],[−V,I]] = [[0,I],[−UV,0]]`. With `V = u^j` and `U = u`, the
  corner is `u^(j+1)`.
- **Theorem R, extension step.** `h <= nx` and `n'x <= h'` give `n'h <= nn'x <= nh'`. So `phi(h)/n <= phi(h')/n'`.
- **Criterion** (spot-check of `w4-vf-linear-b` Section 28.1). Absorption gives
  `I_(q+1) <=_T I_(q+1) ⊕ X <=_T X <~ I_q`. With minors only, the same argument gives the rank condition.
- **Where they sit.** These four are premises of the Sylvester form of the gate, not of the weakly finite chain in
  Sections 2–4.

## 2. The binary chain end to end

**Verdict.** PASS for the corner equivalence. The converse from a Gottschalk counterexample is not established.

**Statements.** Put `G = L_(F_2)(1,2)^x` and `A = F_2[G]`.
- **(F2)** `c e b = 1` is solvable in `A` (`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`, OPEN).
- **(RC_T)** `T = fAf` fails the rank condition. Equivalently, `(K_0(T), [T])` has no state.
- **(WF_T)** `T` has no nonzero weakly finite image (`binary-complement-corner-has-no-weakly-finite-image`, OPEN).
- **(Rep2)** Every homomorphism from `G` into the units of a weakly finite ring of characteristic two is trivial.
- **(SF2)** Some `M_n(A)` is not directly finite (`leavitt-group-algebra-not-stably-finite`).
- **(Gott2)** `G` is not surjunctive (`leavitt-unit-group-nonsurjunctive`).

**Links.**

| link | source | passed by |
|---|---|---|
| F2 ⟺ RC_T | Theorem B | `w4-vf-linear-b` §32.3; §1.2 here |
| RC_T ⟺ WF_T | Theorem C | `w4-vf-linear-b` §29.4; §1.1 here |
| WF_T ⟺ (c) of Theorem W | Lemmas W.1, W.2 | `w4-vf-linear-b` §35; §1.3 here |
| (c) ⟹ Rep2 | simplicity of `G` (`binary-leavitt-unit-group-is-simple`) | `review-backlog-2-2026-09-12.md` §8, inheriting two Lean theorems |
| Rep2 ⟹ (c) | restrict to `G` | elementary |
| F2 ⟹ SF2 | Kaplansky failure at `n = 1`, see below | re-derived here |
| SF2 ⟹ Gott2 | `stable-finiteness-failure-refutes-surjunctivity` | `gottschalk-negative-side-verification-2026-09-12.md` |

**F2 ⟹ SF2 at `n = 1`.** `(ce)(eb) = 1`. If `(eb)(ce) = 1`, then `e` would be invertible, hence `e = 1`, and
`[g] + [g²] = 0`, which is false.

**Findings.**
- **F2 ⟺ Rep2: PASS end to end.** Only one input lies outside this scope: simplicity of `G`, used only for F2 ⟹ Rep2.
  Rep2 ⟹ F2 needs no simplicity.
- **Rep2 ⟹ Gott2: PASS, and elementary.** If `A` were stably finite, the inclusion `G -> A^x` would be a nontrivial
  weakly finite representation. So Rep2 gives SF2 directly, with no Theorem B, C, W and no simplicity, and SF2 gives
  Gott2. Theorems B, C and W are needed only to show that Rep2 loses nothing against F2.
- **Gott2 ⟹ Rep2: not established.** No node claims it (Section 4).

## 3. The ternary chain end to end

**Verdict.** PASS for the corner equivalence, conditional on simplicity of `PG` as recorded. The converse from a
Gottschalk counterexample is not established.

**Statements.** Put `G_3 = L_(F_3)(1,2)^x` and `S_- = eps_- F_3[G_3]`, and let `e_-` be the anti-invariant swap idempotent.
- **(F3)** `c e_- b = eps_-` is solvable in `S_-` (`ternary-anti-invariant-swap-corner-is-full`, OPEN).
- **(NS_-)** `(K_0(S_-), [eps_-])` has no state. Equivalently `[eps_-] <= 0`, and equivalently `S_-` fails the rank condition.
- **(WF_-)** `S_-` has no nonzero weakly finite image (`ternary-anti-central-summand-has-no-weakly-finite-image`).
- **(Rep3)** Every homomorphism from `G_3` into the units of a weakly finite `F_3`-algebra is trivial
  (`ternary-leavitt-units-have-no-weakly-finite-representation`).
- **(SF3)** Some `M_n(F_3[G_3])` is not directly finite.
- **(Gott3)** `G_3` is not surjunctive.

**Links.**

| link | source | passed by |
|---|---|---|
| F3 ⟺ NS_- | census Theorem E at `(q, d, m) = (3, 2, 2)` (`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`; converse on `anti-central-state-obstruction-equals-stable-finiteness`) | `gk-vf-linear` §§25, 11 |
| NS_- ⟺ WF_- | Theorem C | `w4-vf-linear-b` §§29.4–29.5; §1.1 here |
| Rep3 ⟹ WF_- | a weakly finite image of `S_-` sends `z` to `−1 != 1` | elementary |
| WF_- ⟹ Rep3 | Theorem 3, (i) ⟹ (iii) | `w4-vf-linear-b` §36.3; §1.4 here |
| inputs to WF_- ⟹ Rep3 | perfection; the embedding `ι`; simplicity of `PG` | see below |
| WF_- ⟹ SF3 | Corollary 1.2: `J_1(S_-) != 0`, padded by `eps_+` | `w4-vf-linear-b` §36.1 |
| SF3 ⟹ Gott3 | `stable-finiteness-failure-refutes-surjunctivity` | `gottschalk-negative-side-verification-2026-09-12.md` |

**Inputs to WF_- ⟹ Rep3.**
- **Perfection** (`leavitt-gl-equals-el-and-perfect-unit-group`): passed in `review-backlog-2-2026-09-12.md` §9.
- **The embedding `ι`** (`leavitt-units-embed-in-their-scalar-quotient`): passed by `gk-verify-pos` §24.
- **Simplicity of `PG`** (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`): passed in
  `review-boone-higman-leavitt-tensor-hosts-2026-09-12.md`, conditional on the imported criteria of Khanh
  arXiv:2609.08428v1.

**Identification checked.** At `q = 3` and `d = 2`, the census setting forces `m = 2`, the swap `w` and `e_H = e_-`. The
visible factor is `S_-`, since there `[z] = −1`, and its unit is `eps_-`. Statement 3 of the census claim is the matrix
rank condition that Theorem C uses.

**Findings.**
- **F3 ⟺ Rep3: PASS end to end.** It is conditional only on simplicity of `PG` as recorded on that node, and that input
  is used only for F3 ⟹ Rep3. The other direction runs Rep3 ⟹ WF_- (elementary), then Theorem C, then census Theorem E.
- **Rep3 ⟹ Gott3: PASS, and elementary.** It goes through the inclusion `G_3 -> F_3[G_3]^x`.
- **Gott3 ⟹ Rep3: not established.** No node claims it.

## 4. What is missing for a literal equivalence with a counterexample

**The chain in terms of the reflection stages.** Let `ω` be the augmentation ideal of `F_p[G]`, and `J_k`, `J_omega` the
reflection stages of Theorem 1 of `research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md`.
- The augmentation `F_p[G] -> F_p` is a weakly finite image, so `J_omega ⊆ ω`.
- Every homomorphism into a weakly finite ring kills `J_omega`, and `F_p[G]/J_omega` is weakly finite. So Rep_p holds
  iff `J_omega(F_p[G]) = ω`. This uses no simplicity.
- By Theorem 1(d), SF_p holds iff `J_1(F_p[G]) != 0`, and that is all a counterexample through linear automata needs.
- So the verified chain reads: fullness ⟺ Rep_p ⟺ `J_omega = ω` ⟹ `J_1 != 0` ⟹ Gott_p.

**Two links would be needed** for "a Gottschalk counterexample on `G` ⟺ Rep_p". Neither is proved or claimed anywhere.
1. **Gott_p ⟹ SF_p.** This is the converse of the linear-automaton criterion. A nonlinear counterexample need not come
   from group-ring finiteness; the route `nonsurjunctive-from-stable-finiteness-failure` says so itself.
2. **SF_p ⟹ Rep_p.** Nothing shows that a one-sided pair at stage 1 collapses `J_omega` to `ω`. A proper quotient of
   `F_p[G]` in which `G` embeds could be weakly finite while `F_p[G]` is not. Corollary 3.3 of the same artifact
   records the dual form: an overgroup whose group algebra is stably finite.

**Reading for the lead.** "Both counterexample routes are now 'the Leavitt unit group has no nontrivial weakly finite
char-p representation'" is correct as a statement about the two corner routes: each corner is full iff Rep_p. It is
not an equivalence with the existence of a Gottschalk counterexample on `G`.
- Rep_p (`J_omega = ω`) is stronger in form than SF_p (`J_1 != 0`), and SF_p already suffices.
- A nontrivial weakly finite representation would kill both corner routes. It would refute neither Gott_p nor SF_p.
