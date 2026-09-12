# Swarm 3 and 4 adversarial review (2026-09-12)

Reviewer lane `swarm4-reviewer`.

**Scope.** Claims first landed on main after 2026-09-12 15:00 CDT by the swarm 3 and swarm 4 lanes of
session `01PWzwKNBr2dwjX4pucBuXff`.
- Claims landed earlier belong to `review-backlog` and `review-backlog-2`.
- Claims from the w3 and gk lanes of the Gottschalk session are covered in
  `research/artifacts/w3-vf-*-verification-2026-09-12.md` and `gk-vf-*-verification-2026-09-12.md`.

Each section covers one claim and gives the verdict (PASS, FAIL or GAP) with the specifics. Sections are
landed one batch at a time.

## 1. `subgroup-cosets-are-independent-over-division-closure` (f00694d22): PASS

Checked against `subgroup-cosets-independence-proof`.
- **Denominators.** `U(H)` is the Ore localization of `N(H)` at its non-zero-divisors, so finitely many
  elements have a common left denominator `b`. The inclusion `N(H) <= N(G)` sends non-zero-divisors to
  non-zero-divisors, so clearing `b` inside `U(G)` is legitimate.
- **Supports.** `N(G)` commutes with right translations. So `c δ_x` is the right translate of
  `c δ_e ∈ l^2(H)`, and it lies in `l^2(Hx)`. Distinct right cosets give orthogonal subspaces, and `δ_e`
  is separating for `N(G)`, so each `c_i = 0`.
- **Free module.** `d·(hx) = (dh)·x` with `dh ∈ D_H`, so the span is `Σ_x D_H x`, and the lemma makes it
  free.
- The statement is standard, as the node says, and it uses no hidden hypothesis.

## 2. `vertex-division-closure-escapes-edge-coset-span` (f00694d22): PASS on the statement, three slips in the route corrected forward

**The statement holds.** `(1+s)^(-1)` lies in `D_A` but not in `span_(D_C)(A)`, for any `s` normalizing
`C` with infinite order in `N_A(C)/C`.

**Slip 1, step 1 (justification only).**
- The route identifies `l^2(P)` with `l^2(C) ⊗ l^2(Z)` by `c s^k ↦ δ_c ⊗ δ_k`. Under that map `λ(s)` is
  `U_σ ⊗ shift`, not `1 ⊗ shift`, unless `s` centralizes `C`.
- The conclusion survives. `l^2(A)` is the orthogonal sum of the `l^2(<s>g)` over the right cosets of
  `<s>`, and `λ(s)` is the bilateral shift on each.
- So `1 + λ(s)` is multiplication by `1 + z` on `L^2(T) ⊗ l^2(<s>\A)`. It is injective with dense range,
  so it is invertible in `U(A)`.

**Slip 2, step 3 (unjustified, not needed).**
- The route asserts that `D_C` has no zero divisors. That is not justified: the claim assumes neither
  torsion-freeness nor Strong Atiyah for `C`, and for finite `C` the division closure is `K[C]` itself.
- Step 4 does not need it. Suppose `(1+s) y = 1` with `y = Σ_(k=m..M) y_k s^k` and `y_m ≠ 0 ≠ y_M`.
  - The degree-`m` coefficient of the product is `y_m`, so `m = 0`.
  - The degree-`(M+1)` coefficient is `σ(y_M)`, so `M + 1 = 0`.
  - That contradicts `m <= M`.
- Only the extreme coefficients of `1 + s` enter, and both are `1`.

**Slip 3, the closing remark (false as stated).**
- The remark says the argument runs verbatim for any element of `K[P]` that is supported on at least two
  `C`-cosets and invertible in `U(P)`.
- Counterexample: `A = P = Z/2 × Z`, `C = Z/2 = <ε>`, `s` a generator of `Z`, `e = (1 + ε)/2`.
  - `x = e + (1 - e)s` is supported on `C` and `Cs`.
  - `x·(e + (1 - e)s^(-1)) = 1` in `K[P]`, so `x^(-1)` lies in `span_(D_C)(P)`.
- The remark is correct when the extreme coefficients are non-zero-divisors of `D_C`. That includes
  torsion-free `C` satisfying Strong Atiyah, where `D_C` is a division ring, and that is the only case the
  Atiyah region uses.

**Scope of the "Consequence" section.** The sentence that tree methods "cannot decide injectivity of φ"
describes methods; it is not a theorem. The node already calls it an obstruction to a method, and no
route consumes it.

**Cairn.** The route text is corrected in the same landing as this section. No status changes: the claim
stays ESTABLISHED and `kazhdan-edge-coproduct-rank-is-inner-rank` stays OPEN.

## 3. `log-depth-rate-rounding-is-equivalent-to-unit-type` (77f18d45b): PASS

Checked `log-depth-rate-unit-type-equivalence-proof` against the exact statements of its four inputs at
c42aa26e7.
- **Quantifiers match.** The route applies these inputs to an arbitrary rounding, and each is stated for
  every (H1) rounding and every unitary representative of `σ_n(A)`, so no special choice is hidden:
  - items 1 and 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`;
  - item 1 of `compressor-transport-exactifies-under-vertex-rounding`;
  - item 3 of `nonunit-root-mass-log-depth-scale-bound`.
- **(c) ⟹ (b).**
  - `{χ : χ|A_nu ≠ 1} = {depth_nu >= 1}`, so `nonunit-projection-bounded-by-root-spectral-mass` gives
    `τ(1 - P_n) <= r(r-1)[μ_n(depth_nu = 1) + μ_n(depth_nu > 1)]`.
  - Item 5 of the shallow claim sends the first term to 0, and (c) sends the second to 0.
  - Replacing the non-unit constituents by trivial ones moves each generator by at most
    `2τ(1 - P_n)^(1/2)`. So the result is still an (H1) rounding, and it is of unit type.
- **(b) ⟹ (a) and (b) ⟹ (c).** A unit-type rounding factors through `St_r(A_u)`. Every root character
  then has trivial non-unit component, so `D(π_n) = 0` and the deep mass is 0.
- **Reading.** This is an equivalence of three existence statements for one `σ`, and the consequences
  are stated at that level. As the node says, it establishes none of (a), (b) and (c). Its content is
  that neither the rate target nor the deep-mass target is a weaker intermediate goal.

## 4. `laurent-extension-agrees-iff-inverse-defects-commute` (451992736): PASS, one compressed justification

Checked against `laurent-extension-agrees-iff-inverse-defects-commute-proof`.
- **Item 1.**
  - Set `U = σ(e_23(h))`, `V = ρ'(x_23(h))`, and `a = π(e_12(f))` with `f ∈ x_i R_+`. Both commutators
    equal `π(e_13(fh))`, because `ρ'` restricts to `π` on `St_r(R_+)`. So `U a^* U^* = V a^* V^*`, and
    `V^* U` commutes with `a`. The `e_31(x_i R_+)` case is the same.
  - For `r = 3` the roots commuting with `x_23` are `e_13`, `e_21` and `e_23`, and
    `[e_31(x_i f), e_12(x_i)] = e_32(x_i^2 f)`. So `H_i` contains every `e_jk(x_i^2 R_+)`.
  - At finite level `x_i` is a unit of `A_n`, so `x_i^2 R_+ -> A_n` is onto.
- **Item 2, "if".**
  - The Kazhdan projection for `Ad π_n` gives `π(Γ)' ∩ M = ∏_U π_n(Γ)'`. So `W_i` commutes with
    `V = (ρ'_n(x_23(h)))_U`, although `V` is not in `π(Γ)`. This is where property (T) enters, and it is
    used correctly.
  - `σ(e_21(h)) = [V W_i, b] = ρ'(x_21(h))`. The induction over negative exponents goes through a third
    index.
- **Item 3.** If `m_n <= m` along `U`, then `x_i^(m!) - 1` dies in `U`-many `A_n`. So
  `σ(e_12(x_i^(m!) - 1)) = 1`, which contradicts the regular trace. Correct.
- **Item 4 (compressed but correct).**
  - The route says the canonical extension of `ρ_n|Γ` is `ρ_n ∘ q` "by uniqueness of the ring extension".
  - The full reason is artifact Lemma 6.1: `ρ_n(e_jk(f))` depends only on `f` mod the root ideal `J`,
    and `R_+/I = L/J` because `x_i^(-1)` is a power of `x_i` in the finite ring. So `ρ'_n = ρ_n ∘ q` on
    generators, and `W_i = 1`.
  - Lemma 6.1 itself checks: root images are elementary abelian `p`-subgroups of `U(N)`, so they are
    finite, and `[e_13(g), e_32(f)] = e_12(gf)` makes the kernel an ideal.

**Route `log-depth-rate-rounding-via-laurent-vertex-rounding` (bf4f51694): PASS.**
- By Lemma 6.1 a Laurent rounding restricts to a unit-type rounding of the polynomial vertex, with `D = 0`.
- Each `s ∈ F_Γ` is a fixed word in `F_Δ`, so (H1) carries over.

## 5. `stw01-modular-test-pair-algebra-is-universal-order-pair` (b884c50b5): PASS

Checked `stw01-modular-test-pair-algebra-is-universal-order-pair-proof` step by step.
- **(OP) for the pair.** `h - h^2 = e_1 p (e_2 + e_3) p e_1 = k + e_1 p e_3 p e_1 >= k >= 0`.
- **Dilation.**
  - Put `S = (1-a)^(1/2) a^(1/2)`. Then `S^*S = a - a^2 >= b`, and Douglas' lemma gives `b^(1/2) = CS`
    with `||C|| <= 1`.
  - `d = (1-a)^(1/2) C^*C (1-a)^(1/2)` satisfies `0 <= d <= 1 - a`, and `a^(1/2) d a^(1/2) = S^*C^*CS = b`.
  - `c = (a^(1/2), d^(1/2), (1-a-d)^(1/2))^T` has `c^*c = 1`. So `r = cc^*` is a projection, with
    `r_11 = a` and `r_12 r_21 = b`.
- **Norms.** `ρ(P(h,k)) = P(a,b) ⊕ P(0,0)1 ⊕ P(0,0)1`, so `||P(h_0,k_0)||_U <= ||φ(P(h_0,k_0))||_Q`. So
  `φ` is isometric on a dense *-subalgebra, and it is injective.
- **Surjection `U -> Q`.** Send `h_0` to `Σ λ_i e_i` with distinct `λ_i ∈ (0,1)`, and `k_0` to `m p` with
  `m = min λ_i(1-λ_i) > 0`. These satisfy (OP), and the image contains every `e_i` and `p`.
- **Route `stw01-modular-single-pair-via-universal-order-pair`: PASS.** A bounded 2-quasitrace composed
  with a unital *-homomorphism is a bounded 2-quasitrace.
- **`stw01-universal-order-pair-quasitrace-additivity`.** Correctly left OPEN. Its "equivalent to Problem
  I" sentence also depends on the existing route `stw01-problem-i-via-modular-single-pair`, which is
  outside this review.

## 6. `mf-min-tensor-exact-stably-finite-is-stably-finite` (43a6971d4): PASS

Checked against `mf-min-tensor-exact-stably-finite-proof` and artifact §2.
- **Corona embedding.** Steps 1–6 of the Blackadar–Kirchberg argument use only exactness of `C`. The
  further map `∏M_(k_n)(C)/⊕M_(k_n)(C) -> ∏M_(k_n)(C̃)/⊕M_(k_n)(C̃)` is injective, because
  `⊕M_(k_n)(C̃) ∩ ∏M_(k_n)(C) = ⊕M_(k_n)(C)`.
- **Straightening.**
  - If `v^*v = 1` in the quotient, then every lift has `||V_n^*V_n - 1|| -> 0`.
  - The polar part `W_n` is an isometry in a finite block, so it is unitary, and so `vv^* = 1`.
  - `M_m` of the corona is again a corona of finite blocks.
- **Passing to the subalgebra.** In the unital case, `w + (1-e) ⊗ 1_m` is an isometry of `M_m(D)`. In the
  non-unital case, `B + C1_D ≅ B̃`.
- **Faithful trace on the unitization.**
  - `τ̃(y^*x^*xy) = τ̃(x yy^* x^*) <= ||y||^2 τ̃(x^*x)` uses traciality, so `τ̃(x^*x) = 0` kills `x` in the
    GNS representation.
  - That representation is faithful on `C` because `τ` is faithful.
  - `π(1) ∉ π(C)` because `C` has no unit.
- **The refutation matches the certificate.** The original statement of
  `nuclear-factor-with-infinite-mf-tensor-exists` asks for a separable MF `A` and a separable nuclear `C`
  with a faithful tracial state such that `A ⊗_min C` is not stably finite. The theorem excludes exactly
  that.
- No UCT input is used, and the UCT problem is untouched, as the node says. The result is very likely
  known.

## 7. `bc-kun-thom-gap-label-is-congruence-eigenvalue-limit` (867c6795a): PASS, one wiring note

Checked against `bc-kun-thom-gap-label-limit-proof`.
- **Moments.** On a finite quotient, the normalized trace of the regular representation is the identity
  coefficient of the image of `a^m`. That coefficient equals `(a^m)(1)` once `N_(p')` avoids
  `(supp a)^m \ {1}`.
- **Convergence.** All `μ_(p')` live on `[-||a||_1, ||a||_1]`, so moment convergence is weak convergence.
  A gap around `c` makes `c` a continuity point, and Portmanteau gives the limit. The left side is
  `μ((-∞,c))` by continuous functional calculus across the gap.
- **Normalization.** The `τ` versus `τ̄` correction to artifact §4 is consistent with the displayed
  identities.
- **Wiring note.** The route uses the avoidance Lemma C behind `kun-thom-actor-algebraic-idempotents-pass-trace-test`,
  which is ESTABLISHED, but it declares `requires: []`. This is not a false establishment, but the
  dependency is invisible in the graph.

## 8. `component-space-sizes-miss-leavitt-cover-defect` (46d30ed16): PASS on the derivation, conditional on one unreviewed input

Checked `component-space-sizes-miss-cover-defect-proof` steps 1–9.
- **Step 1 is the load-bearing step.** `D^G <= D^Γ <= D^(tΓt^-1) <= D^M` is correct for `M` normal and
  `tΓt^-1 <= Γ`. The equality of the ends is `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`,
  and items 1–4 rest entirely on it.
  - That claim has no review verdict yet. `review-backlog` flagged it as an unreviewed import, and it is
    on `review-backlog-2`'s priority list.
- **Steps 2–5.** A realizer `x` has `[x, γ] ∈ M_s`, so it normalizes `Γ_s` and preserves `D^Γ`.
  Conjugating realizer sets by `s` does not change `Act`, because `Ad(s)` is the identity on `D^Γ`.
  Realizers of host twists are `σ(z) m c`, so they act as `Ad(C_s)`.
- **Step 7.**
  - `C_G(N) = 1` gives `Z(N) = 1` and `R^x ↪ Out(N)`.
  - If `φ'` fixes `M_s` pointwise, then `n'_γ` centralizes `γ M_s γ^-1 = M_s`. So `n'_γ = 1`, and
    `Out_M(Γ_s) ↪ Out(N)`.
  - The image centralizes `EL_α(R)`, since `φ Ad(γ) φ^-1 = Ad(n_γ γ)`.
- **Step 8.** `[φ|_(M_s)]` would be the class of `û z û^-1`. Commuting with every `ḡ` forces
  `[û z û^-1, g] ∈ N . C_G(N) = N`, which contradicts Theorem 3(c). So the witness class lies outside
  `eps_u(Out_M(Γ_s))`, and the compression of `Q_s(p)` is strict at every corner.
- **Step 9 and scope.** Both are correct. This is an obstruction to a method, and it claims nothing about
  soficity.
