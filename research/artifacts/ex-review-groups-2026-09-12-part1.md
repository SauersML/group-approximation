# EX review, groups: part 1. The simple Kazhdan LEF candidate for Pestov 9.1

Lane `ex-verify-groups`, 2026-09-12, review of landings `f375478c72`, `56bdeb8d3e`, `41e82567c8`
by `ex-kazhdan-simple-hyperlinear`. Index: `ex-review-groups-2026-09-12.md`.

Notation as in `research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`
(Part 1): `X` an infinite minimal subshift, `T` the shift, `Acal = LC(X,F_q)`, `α(f) = f∘T^(-1)`,
`R = Acal ⋊ Z`, `G = EL_3(R)`, `Z = Z(G)`, `S = G/Z`.

## 1.0 Verdicts

| item | verdict |
|---|---|
| Statement of Pestov Open Question 9.1 against the source | PASS |
| (1) Part 1 §3.1–3.2: `R` embeds unitally in `prod_ω M_(N_k)(F_q)`; seam windows; exact multiplicativity; injectivity | PASS |
| (2) Part 1 §3.3: LEF passes to `S = G/Z`; the finite centre goes to scalars | PASS |
| (3) Part 1 §1.5–1.6 and §4: every normal subgroup of `G` is central or `G` (cases (c) and (d)) | PASS |
| (4) Ershov–Jaikin-Zapirain Theorem 1.1: hypotheses and application | PASS, one wording note (§1.4) |
| `minimal-subshift-algebra-is-simple-lef-ring` (+ `-proof`) | PASS, same wording note |
| `subshift-elementary-group-is-simple-modulo-centre` (+ `-proof`) | PASS, one wording note (§1.3) |
| `lef-kazhdan-group-without-finite-quotients-exists` (+ `-proof`), its `refuted_by` edge, and the refutation of EKL2 | PASS |
| `operator-mf-group-not-weakly-quasidiagonal-exists` (+ `-proof`) | PASS, conditional on the Prop. 3.19 import, which is a `requires` edge |
| `simple-kazhdan-lef-group-from-minimal-subshift` (OPEN, held) and route `simple-kazhdan-hyperlinear-from-subshift-elementary-group` | Mathematics PASS. The combining route may be landed |

Conclusion: `S` is an infinite, finitely generated, simple group with property (T) that is LEF,
hence sofic, hence hyperlinear. This answers Pestov's Open Question 9.1 positively, in its sofic
form. The novelty check is bounded (§1.7). No step fails.

## 1.1 Statement fidelity

Pestov, arXiv:0804.3968, PDF p. 21, read from the PDF fetched on MSI on 2026-09-12:
"**Open question 9.1** (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property
(T). Can it be hyperlinear (sofic)?" It sits under "The two candidates for a counter-example are
mentioned in Questions 9.1 and 9.4." The question asks whether such a group *can* be sofic, so one
example answers it. Discrete Kazhdan groups are finitely generated, so nothing is hidden there.
The root node quotes the same sentence.

## 1.2 Check (1): the periodic ring models

Re-derived independently.
- **Seam windows.** `x_[p, p+2k) = v = x_[p', p'+2k)`, `N = p' - p >= 2k+1`, `w = x_[p,p')`, `y` the
  `N`-periodic extension. A window of `y` of length `l <= 2k+1 <= N` contains at most one index
  `≡ 0 mod N` in its interior. If it crosses one, it is `suffix_s(w) prefix_t(w)` with `s, t >= 1`,
  so `t <= 2k`. Then `prefix_t(w) = prefix_t(v)`, and the window equals `x_[p'-s, p'+t)`, a word of
  `X`. Every word of `L_(2k+1)(X)` occurs in `w`, because `N >= l(2k+1)`.
- **The model map.** Define `D_k(f)_n = f(x)` for any `x ∈ X` with `x_[-k,k] = y_[n-k,n+k]`. This is
  well defined for `f` of radius `<= k`. It is evaluation at points, so it is a ring map on such
  functions. With `P δ_n = δ_(n+1)`: `P^i D_k(g) P^(-i) = diag(ĝ(n-i))`. And
  `α^i(g)(x) = g(T^(-i)x) = Φ_g(x_[-ρ-i, ρ-i])`, which at the window centred at `n` is `ĝ(n-i)`,
  valid when `ρ + |i| <= k`. So `D_k(α^i g) = P^i D_k(g) P^(-i)` exactly, at every `n`, seam
  positions included. `ψ_k(f u^i) ψ_k(g u^j) = D(f) P^i D(g) P^j = D(f α^i(g)) P^(i+j) =
  ψ_k((f u^i)(g u^j))`. No truncation occurs, since `P^N = 1` and `y` is genuinely periodic.
- **Injectivity.** If `f_j(x) != 0` with `f_j` of radius `ρ`, the word `x_[-ρ,ρ]` occurs in `y`, so
  `D_k(f_j) != 0`. `D_k(f_j) P^j` is supported on the entries `(n+j, n)`, and these supports are
  disjoint for distinct `|j| < N/2`. So `ψ_k(r) != 0` for all large `k`, and `Ψ(r) != 0` in the
  ultraproduct.
- `M_3` of an algebraic ultraproduct is the ultraproduct of the `M_3`, and units are taken
  coordinatewise ω-almost everywhere. So `GL_3(R) -> prod_ω GL_(3N_k)(F_q)` is injective. A finitely
  generated subgroup of an ultraproduct of finite groups is LEF: a finite window's multiplication
  table and inequalities hold on an ω-large set of coordinates.

## 1.3 Check (3): normal subgroups

Re-derived step by step.
- **§1.5 towers.** `E_ab(W) E_cd(W') = χ_(T^a W ∩ T^(a-b+c) W') u^(a-b+c-d)`. For `|c-b| <= 2m` this
  vanishes unless `c = b`, because `T^a U ∩ T^(a-b+c) U = T^a(U ∩ T^(c-b) U)`. Coefficients are
  recovered from the disjoint levels, so `B_m(U) ≅ M_(2m+1)(LC(U,F_q))` with unit `χ_V`.
- **§1.6 absorption.** `(f u^i) E_ab(W) (f' u^j) = F χ_(T^(a+i)W) u^(i+a-b+j)`, with
  `F = f α^(i+a-b)(f')`. Split `W` so that `F` is constant on `T^(a+i) W_k`. The result is
  `Σ c_k E_(a+i, b-j)(W_k)`. This needs return times `> 2(m+w)`.
- **§4.1 level ideal.** `[e_12(a), e_23(b)] = e_13(ab)` and `[e_31(b), e_12(a)] = e_32(ba)`. The Weyl
  elements `e_ij(1) e_ji(-1) e_ij(1)` lie in `EL_3` and move roots with signs. So `I(N)` is a
  two-sided ideal. `R` is simple (§1.3 of the artifact, re-derived: `χ_W P χ_W = c χ_W`, finitely
  many translates cover `X`, and `1 - Π(1 - χ_(T^i W)) ∈ J`).
- **§4.2(a).** `C_g` is closed under `±` and under products via `e_ij(st) = [e_ik(s), e_kj(t)]`.
  Wording note: for `q = p^e` with `e > 1`, `Σ_L` generates only the `F_p`-subring
  `LC(X,F_p) ⋊ Z`, not `R`. The conclusion survives. `g` commutes with every `e_ij(1)`, so `g = cI_3`;
  `c` commutes with every `χ_W` and with `u`, and the centre argument of §1.4 uses only those, so
  `c ∈ F_q` and `g` is central. The fix is to add `λ χ_C`, `λ χ_C u^(±1)` (`λ ∈ F_q`) to `Σ_L`, or
  to state the centraliser step.
- **§4.2(b).** `g h g^(-1) - I` has entries `g_pi s (g^(-1))_jq`, which lie in `B_(1+w)(U)` by §1.6,
  since `2(1+w) < L`. With `X = g s E_ij g^(-1)` and `Y = -s E_ij`, `k - I = X + Y + XY` lies in
  `M_3(B_(m')(U))`, and the same holds for `k^(-1)`. So `k_V = eI + (k - I)` is invertible in the
  corner, and `κ : U -> GL_d(F_q)` is locally constant with `κ ≢ I`.
- **§4.2(c).** The same-row transvection identity, computed in the `(p, p'')` block with
  `xy = x`, `yx = 0`, `x^2 = 0`:
  `A B A^(-1) = [[1+xy, -xyx],[y, 1-yx]] = [[1+x, 0],[y, 1]]`, and multiplying by `B^(-1)` gives
  `[[1+x, 0],[0, 1]]`. So `ι_W(SL_d(F_q)) <= G`.
  - `[k, ι_W(ε)] = ι_W([κ_0, ε])` holds pointwise under `M_3(B_(m')(U)) ≅ LC(U, M_d)`, and both
    factors are `1` off the tower.
  - `ε ↦ [κ_0, ε]` into the centre is a homomorphism: `[κ_0, εε'] = [κ_0, ε][κ_0, ε']` once the
    second factor is central. Perfectness of `SL_d(F_q)` then forces `κ_0` to be scalar. So
    `N_W` is noncentral, hence all of `SL_d(F_q)` (`d >= 9`), and `e_12(χ_W) ∈ N`.
- **§4.2(d).** `k = cI_3` with `c = λ∘T^(-a)` on `T^a U` (`|a| <= m'`) and `c = 1` off `V`. Put
  `r = χ_(T^(m'+1)W) u`. Then `c r c^(-1) = c χ_(T^(m'+1)W) α(c^(-1)) u`. Here `c = 1` on
  `T^(m'+1) W`, since `1 <= m'+1-a <= 2m'+1 = L` and return times exceed `L`. And `α(c^(-1)) = λ_0^(-1)`
  there, since `T^(-1)(T^(m'+1) W) = T^(m') W`. So `[k, e_12(r)] = e_12((λ_0^(-1) - 1) r) != 1`.
- **§4.4.** Commuting with every `e_ij(1)` forces `g = cI_3`, and then `c ∈ Z(R) = F_q`. Every
  `λ I_3` with `λ ∈ F_q^x` is central in `GL_3(R)`, so `Z = G ∩ F_q^x I_3 = Λ I_3`.

The trap named in the brief, sandwich theorems that need stable-range or module-finiteness
hypotheses, is not used. The argument is self-contained and uses only the tower structure, which
exists because `X` has no periodic points.

## 1.4 Checks (2) and (4)

- **(2).** `Ψ` is `F_q`-linear and unital, so `Ψ(λ I_3) = λ I`. `Λ` is finite, so a sequence lying in
  `Λ I` ω-almost everywhere is ω-almost everywhere constant. Hence
  `prod_ω GL/ΛI ≅ (prod_ω GL)/[ΛI]`. If `Ψ(g) = [λ I]`, then `Ψ(g) = Ψ(λ I_3)` and `g = λ I_3 ∈ Z`. So
  `S` embeds in `prod_ω GL_(3N_k)(F_q)/ΛI`, and `S` is LEF.
- **(4).** `elementary-groups-over-fg-rings-have-property-t` quotes Theorem `thm:main` from the arXiv
  TeX source, lines 405–410, checked twice: "Let R be a finitely generated (associative) ring with 1
  and n >= 3. Let G = EL_n(R) ... Then G has Kazhdan's property (T)." Its citation route has
  `requires: []`. Hypotheses: `n = 3`, and `R` is a finitely generated ring with 1. Wording note: §1.2
  and item 1 of `minimal-subshift-algebra-is-simple-lef-ring` list `u`, `u^(-1)` and `χ_[a]` as ring
  generators. For `q` not prime, a primitive element of `F_q` must be added. `R` is still finitely
  generated, so (T) holds. `S` inherits (T) as a quotient.

## 1.5 The established consequences

- **`lef-kazhdan-group-without-finite-quotients-exists`: PASS.** The proof route needs only simplicity
  of `R`. `e_12(R) ∩ N = e_12(I(N))` has finite index in the infinite group `(R, +)`, so `I(N) != 0`,
  hence `I(N) = R` and `N = G`. The requires are all established: the two imports have
  `requires: []` routes, and `lef-implies-operator-mf-proof` requires `countable-group-mf-conventions`,
  which is ESTABLISHED in FRONTIER.
- **EKL2**, as printed in `exact-kazhdan-radical-kernel-cannot-be-lef`: "a countable LEF
  property-(T) group with no nontrivial finite quotient is trivial." It is stated for LEF, with no
  MF convention, and `G` refutes it. EKL1, the mapping-torus statement, is untouched and has no live
  route. Its proof route is invalidated by the established
  `mf-to-weak-qd-citation-has-unproved-lifting-step`.
- **MF convention of `mf-kazhdan-group-without-finite-quotients-is-trivial`**: operator MF in the
  norm-matrix-corona sense. This is Dadarlat's MF-group definition, arXiv:2007.12655v2, p. 1,
  conditions (1) `||φ_n(st) - φ_n(s)φ_n(t)|| -> 0` and (2) `limsup ||φ_n(s) - 1|| > 0`, read from
  the PDF. LEF gives exactly this through left regular representations (`lef-implies-operator-mf`).
  The `refuted_by` edge is correct.
- **`operator-mf-group-not-weakly-quasidiagonal-exists`.** p. 2 prints "It is clear from definitions
  that MF ⇒ weak quasidiagonality". Weak quasidiagonality there uses unital completely positive
  definite maps satisfying (1) and (2). Proposition 3.19, p. 10, verbatim: "(Ozawa-Thom). If an
  infinite property (T) group G is weakly quasidiagonal, then G has an infinite residually finite
  quotient." `G` has no nontrivial finite quotient, so it has no infinite residually finite quotient.
  Granting 3.19, `G` is MF and not weakly quasidiagonal. The node states this dependence through its
  `requires: [weak-qd-kazhdan-quotientless-group-is-trivial]`. PASS. The precise form of the finding
  is that the printed arrow and Proposition 3.19 cannot both hold.

## 1.6 Nodes resting on the refuted implication

No ESTABLISHED claim was found that rests on `mf-kazhdan-group-without-finite-quotients-is-trivial`,
`simple-kazhdan-groups-have-full-mf-radical` or `exact-kazhdan-radical-kernel-cannot-be-lef`. Every
`requires` naming them, found by grep at tip `edb8c69cc`, is listed below.
- `non-mf-hyperbolic-from-kazhdan-quotientless` (route) requires the refuted claim, so it is dead
  and never fires. Target `non-mf-hyperbolic-group` is OPEN. Retire it, or add an obstruction.
- `hyperbolic-rf-question-equals-non-mf-question-proof` (route) requires the refuted claim, so it is
  dead. The claim's Attempts call the premise "an open sufficient premise", which is stale: it is
  refuted. Statement (4) of the four-way target gets no support from this route.
- `kazhdan-hyperbolic-group-without-finite-quotients` (OPEN claim). The existence question is
  untouched. Its prose "is non-MF by Ozawa–Thom" (distinct_from) and "By
  `mf-kazhdan-group-without-finite-quotients-is-trivial`, such a `Q` is not MF" is now unfounded.
- `fp-simple-full-mf-radical-via-titz-witzel` (route) requires
  `simple-kazhdan-groups-have-full-mf-radical`, whose only route is invalidated and which `S`
  refutes once `simple-kazhdan-lef-group-from-minimal-subshift` is established. The route is dead.
  Its body's closing "∎ ... uses only claims that were established" is stale. Target
  `fp-simple-full-mf-radical-group` stays ESTABLISHED through
  `fp-simple-full-mf-radical-via-leavitt-unit-group`, whose requires include the established
  `binary-leavitt-all-ranks-full-mf-radical`.
- `titz-witzel-exact-kazhdan-mf-radical-over-z-proof` and
  `titz-witzel-mapping-tori-are-virtually-products-proof` require the same claim, so they are dead.
  Both targets are OPEN, so there is no false establishment. `titz-witzel-soficity-is-one-finite-csp`
  cites it in prose.
- `torsion-free-kazhdan-alternating-mother-limit-gate` (claim). Its only route requires
  `exact-kazhdan-radical-kernel-cannot-be-lef`, which is not established, so the claim is not
  established. Its body asserts that no simple limit can occur, "by
  `exact-kazhdan-radical-kernel-cannot-be-lef`". That reason is gone, since LEF Kazhdan groups without
  finite quotients exist. Only the first sentence (the torsion-free Kazhdan mother with unbounded
  alternating quotients) is independent of it.
- `simple-kazhdan-groups-have-full-mf-radical` (OPEN). Once the combining route is landed it should
  carry `refuted_by: [simple-kazhdan-lef-group-from-minimal-subshift]`, since `S` is MF, being LEF.

## 1.7 Novelty and credit (bounded)

- Web searches, two queries at 22:40 CDT (simple Kazhdan sofic, Pestov 9.1; elementary matrices,
  simple ring, LEF), found no answer to 9.1. Results describe it as open. `ex-open-status` lists
  the root as OPEN. This is not a literature survey.
- Credit note: approximating a minimal subshift by periodic return words is the mechanism of
  Grigorchuk–Medynets' LEF theorem for topological full groups of minimal subshifts. The ring version
  here is the same idea. Part 2 §8.1's "This construction is due to this lane" should credit that
  mechanism and restrict the claim to the application: `EL_3` over the crossed-product ring, the
  (T) input and root detection.
