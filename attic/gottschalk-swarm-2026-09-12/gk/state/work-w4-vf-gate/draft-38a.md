
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
