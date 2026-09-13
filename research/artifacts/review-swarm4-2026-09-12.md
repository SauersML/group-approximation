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

## 9. `leavitt-tensor-powers-are-not-left-coherent` (4ee11a356): PASS

This claim refutes `leavitt-tensor-powers-are-left-coherent`. That claim was the open input of the
coherence route to `K_1 = K_2 = 0` for three or more Leavitt factors, so every step was checked.
- **Step 1 (strong grading).**
  - `(y_1⊗1)(x_1⊗1) = 1` and `Σ(x_i⊗1)(y_i⊗1) = 1` put `1` in `A_(-1)A_1` and in `A_1A_(-1)`.
  - Take homogeneous generators `a_i` of `ann_A(f)`. Then `ann_T(f) = Σ A_(-d_i) a_i`.
  - From `1 = Σ p_k q_k`, `A_(-d) = Σ_k T q_k`.
  - So left coherence of `A` makes `ann_T(f)` finitely generated.
- **Step 2 (the Bernoulli shift).**
  - `uv = vu = 1`.
  - The shift formula uses `y_i x_γ = δ_(iγ_1) x_(γ')` and `y_δ x_j = δ_(δ_1 j) y_(δ')` under the stated
    convention `y_β = y_(β_m)⋯y_(β_1)`.
  - Every tensor position moves down by one.
- **Step 3.** `u^n e = σ^n(e) u^n` gives `g f = Σ_n (g_n - g_(n-1)) σ^n(e) u^n`. `T` is free over `T_0` on
  the `u^n`, which gives `(*)`.
- **Steps 4–6.**
  - On `V_x`, `Θ e^(p)_(ab) Θ^(-1) = e^(p-1)_(ab)`.
  - An annihilator of width `w` is constant on blocks, the runs with `x_(-n) = 1`, so it vanishes on
    blocks longer than `w`.
  - For `c u^j g`, the blocks of `τ^(-j)x` are the blocks of `x` translated by `-j`. So a finite
    generating set of width `<= W` kills `ξ_x` on every block longer than `W`.
- **Step 7.** `g^[ℓ] = Σ_(n=0..ℓ) P_ℓ u^n` satisfies `(*)`: the differences are `±P_ℓ` at `n = 0` and
  `n = ℓ+1`, and `P_ℓ` carries `e_22` at positions `0` and `-ℓ-1`. On the `x` with block `[0, ℓ]`,
  `P_ℓ ξ_x = ξ_x`.
- **Step 9 (`d >= 3`).**
  - The node's argument works. The grading by the first two factors is strong over `T ⊗ R`, and
    `V_x ⊗_k R` satisfies (a), (b) and Step 7.
  - An independent second argument also works. `ann_(A⊗R)(f⊗1) = ann_A(f) ⊗ R`, because `-⊗_k R` is
    exact. Expanding finitely many generators in a `k`-basis of `R` yields finitely many elements of
    `ann_A(f)` that generate it.
  - Either way, coherence of `L^(⊗d)` would make `ann_T(f)` finitely generated.
- **Right coherence.** `x_i ↔ y_i` in every factor is an anti-automorphism.
- **Not checked here.** The by-product that `C(X,k) ⋊ Z` for the full two-shift is not coherent.
- **Consequences in Cairn.**
  - The invalidations of `leavitt-tensor-powers-k-theory-via-coherence` and
    `prime-field-leavitt-powers-k-theory-via-coherence` are sound.
  - `K_1 = K_2 = 0` for `d >= 3` stays OPEN and now needs a direct computation of the twisted Nil groups.

## 10. `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` and `deligne-lattice-embeds-in-no-rover-nekrashevych-group` (16c1601f5): PASS

- **Marking set.** `f∘β_(u_i w) = β_(v_i h_i(w)) ∘ h_i|_w`, so only the finitely many proper prefixes of code
  words leave `M`. So `M` is commensurated.
- **Transfixing.** Property (T) gives (FH), hence (FW), and so a `G`-invariant `M'` with `M Δ M'` finite.
- **Finite cover.**
  - A ball below level `N` lies strictly inside its level-`N` prefix ball.
  - Only finitely many members of `I` contain a given level-`N` ball.
  - So `P` is finite, `G`-invariant, and covers `X^ω`.
- **Embedding.**
  - On the kernel `G_0` of `G -> Sym(P)`, `g∘φ = φ∘ρ_φ(g)` defines homomorphisms to `H`.
  - They separate points, because the images cover `X^ω`. So `G_0 ↪ H^P`.
  - `H <= Aut(T_d)` is residually finite.
- **Deligne's lattice.**
  - A central `Z`-extension of a finitely presented group is finitely presented, by the standard argument.
  - The word-problem algorithm is correct: decide in `Sp_4(Z)`, then enumerate consequences `w = z^c`.
  - Property (T) and non-residual-finiteness are classical (Bekka–de la Harpe–Valette §1.7; Deligne
    1978). Their quotes were not re-extracted.
- **Invalidation.** `boone-higman-via-rover-nekrashevych-hosts` requires
  `decidable-groups-embed-in-rover-nekrashevych-hosts`, and the lattice refutes that claim.
  `boone-higman-conjecture` is untouched, as the node says.

## 11. `stable-permutation-hnn-of-type-a-actor-is-type-a` (6b70fc6bf): PASS

- **Pair orbits.** Every `L`-orbit of pairs is a union of `Γ`-orbits.
- **Stabilizers.**
  - `P\T` has vertex set `Γ\L/P`, which indexes the `Γ`-orbits on `L.x`, and edge set `D_2\L/P`.
  - Both are finite, because `Γ`, `D_1` and `D_2 = πD_1π^(-1)` have finitely many orbits on `X`.
  - The vertex groups `g Stab_Γ(g^(-1)x) g^(-1)` are finitely generated, so `P` is finitely generated.
- **(b).** The Britton pinch argument for `<A, t> = A*_φ` is the standard HNN subgroup theorem.
- **(c).**
  - `ρ(γ t^m) = 1` iff `π^m = ρ(γ)^(-1)`.
  - In the non-injective case `u = γ_0^(-1) t^n` centralizes `Γ`, so `Γ × <u>` has index `n`. It embeds in
    `Γ × Γ` when `Γ` has an element of infinite order.
- **Scope.** The three "where it stops" items are correctly stated, and they carry the open part of the
  permanence.

## 12. `unimodular-averaging-loses-determinant-integrality` (41a03cfe5): PASS, one framing remark

- **Finite example.** `B = [[2,1],[1,3]]` has determinant `5` and trace `5`. With the uniform root,
  `det = 5^(1/2)` and `N_1 = 5/2`.
- **Ergodic example.**
  - `K = |1+z|^2` has `det K = exp(2m(1+z)) = 1`.
  - `det(T + εM_g^2) = 4^p det(K + ε)`.
  - `T + ε <= T + εM_g^2 <= T + 4ε`, so monotone convergence gives `det T = 4^p`.
  - `N_1 = 2E g_0^2 = 2(1 + 3p)`.
- **Framing.**
  - Fuglede–Kadison determinants of integral group-ring elements are already non-integers: over `Z[Z]` they
    are Mahler measures, such as Lehmer's.
  - The new content is that averaging makes the moments `N_1` non-integers and gives the determinant a
    continuum of values in `(1,4)`.
  - The bullets are accurate as worded. The title reads more strongly than they do.
- **Not checked here.** The "not a counterexample" sentence, that both networks obey every Serre inequality,
  is asserted in the node, not derived.

## 13. `bc-kun-thom-gap-labels-on-bc-subgroups-pass-trace-test` (86c407b21): PASS

- **Setup.** By the coset decomposition, `C*_r H ⊂ C*_r G` is a unital subalgebra with the same norm.
  Spectral permanence keeps `c` in a gap, and the canonical traces agree.
- **Trace theorem.** Lück's theorem puts `τ(χ)` in `Λ^H ⊆ Λ^G = Z[1/P]` whenever `A_FIN` is surjective for
  `H`. Higson–Kasparov gives surjectivity for a-T-menable `H`.
- **The listed supports are a-T-menable.**
  - Borel subgroups are solvable.
  - Lamplighters are amenable.
  - `E_2(F_q[x^(±1)])` is `S`-arithmetic for `S = {0, ∞}`, so it acts properly on the product of two
    Bruhat–Tits trees.
  - `SL_2(Z)` acts properly on a tree.
- The quotes of (I1) and (I2) were not re-extracted.

## 14. `toms-doubling-ah-trace-simplex-is-poulsen` (2f4fa5e60): PASS on the abstract theorem; application to Toms's systems not checked

- **Extreme traces.** Suppose `μ_N({x_N}) -> 1`. The dual connecting maps contract total variation, so any
  convex summand agrees with the trace at every stage.
- **Branch traces.** (D) makes `α_N δ_(y_N) + (1-α_N)ν` the restriction of `δ_(d_N(y_N))`. So branch traces
  are Cauchy, with a summable tail.
- **Density.** (F) realizes every leaf labelling at depth `N - m'`, and uniform empirical measures are weak*
  dense. Lindenstrauss–Olsen–Sternfeld then gives the Poulsen simplex.
- **Not checked.** That Toms's two systems (arXiv:2606.12188v2) satisfy (D), (F) and summable contamination.

## 15. `strict-comparison-bundle-certificate-vanishes` (2f4fa5e60): PASS, conditional on its prerequisite

- `Q - vv^*` is a projection that vanishes on every limit trace. The uniform 2-norm on `A^ω` is attained
  along limit traces, so `vv^* = Q`.
- Lifting `v` to contractions and cutting by `Q` and `P` gives `W`.
- This rests on `strict-comparison-compares-ultrapower-projections`, which was not reviewed here.

## 16. `component-measure-size-separates-compressor-images` (d95872c38): correctly REFUTED

Its `refuted_by` is `component-space-sizes-miss-leavitt-cover-defect` (§8). Items 1–3 of that claim are
exactly its three refutation bullets. So it inherits the §8 dependency on
`kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`.

## 17. `fpbs-tree-projected-reversible-letter-nonunimodular` (0ddef0de2): PASS

Priority review, requested by the coordinator: three named checks and a must-fail test. Read against
`fpbs-reversible-letter-nonunimodular-proof`, steps 1–7.

**Check 1: `L` acts by automorphisms of the whole Cayley graph.**
- **Labels.**
  - `G_A` preserves `p`. The `s_0`-edges lie over `e` and `f`, and each other letter lies over its own
    triangle edges, so labels are preserved.
  - An `o`-edge of `A` joins distinct vertices, so `o`-orientations are preserved.
  - `s_0`-lines follow the palindromic pattern `u w x w u`, so `s_0`-orientations can flip.
- **Vertical edges, including `(1,1)`.** `Ψ_(φ,k)` adds the same `h_φ(g) + k` to both ends.
- **Horizontal edges, for any height sets.**
  - For `s_0`, `D(ε) = D_(s_0) + τ(ε)` in both traversal directions, because `-D_(s_0) = D_(s_0) - c`.
  - For an `o`-letter, `φ` keeps orientation, so `D(φε) = D(ε)` and `τ = 0`.
  - `τ(ε) + τ(ε̄)` is `-c` on `s_0`-edges and `0` otherwise. So `δ_φ` is antisymmetric and has a potential
    on the tree.
  - An edge with height change `d ∈ D(ε)` maps to height change `d + δ_φ(ε) ∈ D(φε)`. The sets `D_o` are
    arbitrary and never enter.
- **Group.** `δ_(φψ)(ε) = δ_ψ(ε) + δ_φ(ψε)`, and `k ∈ Z` absorbs the constant in the potential.

**Check 2: closed and quasi-transitive.**
- A pointwise limit of `Ψ_(φ_j,k_j)` projects to a pointwise limit `φ ∈ G_A`.
  - `h_(φ_j)(g) - h_(φ_j)(1)` is eventually fixed by `φ` on the geodesic `[1, g]`.
  - The shift at `(1,0)` is eventually constant, so the limit is some `Ψ_(φ,k)`.
- The `L`-orbits are the sets `(G_A-orbit) × Z`, so there are three.

**Check 3: nonunimodular in Hutchcroft's sense.**
- **Source.** arXiv:1711.02590. First checked 2026-09-12 against the ar5iv HTML rendering through WebFetch,
  while the MSI auth breaker was set.
  - Re-checked the same day against the v3 PDF text extracted on MSI with `pdftotext`
    (`/scratch.global/sauer354/rev4-pdf/h.txt`): Theorem 1.2 at lines 130–131 and the definition at lines
    144–151. The wording is identical.
  - The definition takes `Stab_x y` to be the orbit of `y` under `Stab_x`, and it puts no closedness
    hypothesis on `Γ`.
  - Both quotes agree word for word with the TeX quotes in
    `fpbs-hyperbolic-and-nonunimodular-nonuniqueness-citation`.
  - Theorem 1.2: "Let G be a connected, locally finite graph, and suppose that Aut(G) has a quasi-transitive
    nonunimodular subgroup. Then p_c(G) < p_u(G)."
  - Definition: "Γ is said to be unimodular if |Stab_v u| = |Stab_u v| for every u,v ∈ V in the same orbit
    of Γ".
- **Stabilizers project isomorphically.**
  - If `φ` fixes `g` and `g'`, it fixes each edge of the geodesic between them, orientation included, so
    `δ_φ = 0` there.
  - So `|Stab_x y| = [(G_A)_(y_0) : (G_A)_(y_0) ∩ (G_A)_(y_1)]`.
  - Stabilizer elements that send `y_1` to the same vertex give the same height, by the same argument.
- **Counting.**
  - `(G_A)_(y_0)` fixes `z`, the unique outgoing `o`-neighbour, and then `y_1`, the unique `e`-neighbour of a
    vertex over `w`. The orbit has size `1`.
  - `(G_A)_(y_1)` is transitive on the two `e`-neighbours of `y_1`, by the extension lemma. Their
    `o`-predecessors are distinct, since otherwise the tree would contain a 4-cycle. The orbit has size `2`.
- **Same orbit.** `x = (y_0, 0)` and `y = Ψ_(φ,0)(x)` lie in one `L`-orbit by construction, as the
  definition requires. So `L` is nonunimodular.
- **Cross-check.** This is the Bass–Kulkarni criterion: the index product around `u -o-> w -e-> u` is
  `(1/1)(1/2) ≠ 1`.

**Must-fail tests.**
- **`n = 1`, amenable.**
  - Every closed quasi-transitive subgroup of `Aut(Cay(Z × Z))` is unimodular (Soardi–Woess), and
    `p_c = p_u` there.
  - The construction degenerates: `O = ∅`, `A` is the path `u – w – x`, and the covering tree is a line.
  - `G_A` is the infinite dihedral group generated by the reflections at `u` and at `x`. For `y_1 = y_0 + 4`
    both stabilizer orbits have size `2`, so `G_A` is unimodular.
  - The proof uses `n >= 2` exactly at the `o`-edge of the counting step.
- **Asymmetric letter.**
  - `D_(s_0) = {0,1,3}` admits no `c` with `c - D = D`, so a reversed `s_0`-edge cannot be compensated, and
    step 4 fails.
  - The node's control run gives positive bad-edge counts for every shift in `[-4,4]`. Larger shifts fail
    trivially, since the set has diameter 3.
- **Unit indices.** With index `1:1` on the `s_0`-edges, `Y = T`, and `G_A` is the group of translations by
  `F_n`. That group is discrete and unimodular. The `2:1` indices are what produce the modular ratio.

**Scope remarks.**
- The root `fpbs-tree-projected-cayley-graphs-strict-thresholds` says in `distinct_from` that the remaining
  graphs are "outside" Hutchcroft's theorem.
  - That is proved only where the whole automorphism group is discrete, since a discrete group is
    unimodular. Artifact §3 of the letter-exchange lane (§22) claims this for one rigid example; that claim
    was not checked here.
  - Hutchcroft makes the same point (PDF lines 169–172): "Theorem 1.2 does not apply to every Cayley graph
    of the direct product of Zd with a non-Abelian free group. Indeed, there are even Cayley graphs of the
    free group on two generators whose automorphism groups are discrete".
  - For the other remaining graphs, what is known is only that no nonunimodular subgroup has been found, as
    the root's Attempts say.
- Novelty was checked only against Cairn. `{(a,0),(a,1),(b,0),(1,1)}` was the smallest open example recorded
  in Cairn, one case of Choi–Seo Q1.3, which stays open.
- The lift-check script was not re-run, because MSI was unavailable.

## 18. RNORM realizer claims (548bdf1fd): four PASS, one conditional

These four claims narrow the unbounded-realizer case of `relative-normalization-modulo-kazhdan-kernel`.

### 18.1 `inner-realizers-are-at-least-half-the-sofic-radius`: PASS

- **Nontrivial kernel commutator.** `h = w^-1 g ≠ 1`, because `w ∈ N` and `g ∉ N`. `C_G(N) = 1` gives some
  `s` with `[h, s] ≠ 1`. The word `d = w^-1 v_s w s^-1` represents `h s h^-1 s^-1`.
- **Fixed points.** Set `y = W s_B^-1 x` and `a = (Wc)^-1 y`.
  - Suppose `y ∉ E_n`, `a ∈ A` and `s_B a ∈ A`. Since `c` commutes with `s_B`,
    `v_s(s~) y = σ_n(g) s_B a = W s_B W^-1 y`, and so `d(s~) x = x`.
  - The maps `x -> y -> a` are bijections of `B`, so the three failure counts add to at most
    `e_B + 2ε|B|`.
- **Radius.** A nontrivial `d` fixing `x` is a violating pair of length `|d| <= 2|w| + L_g + 1`, so
  `ρ_n(x) < |d|`. For fixed `r` there are finitely many word pairs, which gives `|{ρ_n < r}| = o(|X_n|)`.

### 18.2 `kernel-block-realizers-need-no-centralizer-factor`: PASS

- **Commuting products.** Blockwise commuting products give `[Π, C] = 1`, and `σ(N) <= Π`.
- **Central extension.** `θ̄ : Q -> C/(C ∩ Π)` lifts through `E' = {(q, e) : θ̄(q) = e(C ∩ Π)}`.
  - `E'` is a central extension of `Q` by `A_0 = E_0 ∩ Π`, which is central because `Π` commutes with `C`.
  - `H^2(Q; A_0) = Hom(H_2 Q, A_0) ⊕ Ext(H_1 Q, A_0) = 0`, so a homomorphic section `ψ : Q -> S_U` exists.
    Only trivial sofic morphisms exist, so `θ̄ = 1`.
- **Instance.** The inputs `binary-leavitt-unit-group-integrally-acyclic` and
  `leavitt-unit-group-has-only-trivial-sofic-morphisms` were not re-reviewed.

### 18.3 `kernel-block-realizers-exist-after-small-re-edit`: PASS, conditional on block invariance

- **Few blocks.** A block of size `k` gives every point radius `< k`, because the ball of radius `k` in an
  infinite `N` has more than `k` elements. So blocks carry `o(|X_n|)` count, and three-point re-edits cost
  `o(|X_n|)`.
- **Primitivity.** A 3-cycle preserving a block system has its support in one part: if `a` and `b` lie in
  different parts, some `d ≠ a` in `P_a` is fixed or sent to `a`.
  - Chaining the `τ_(i,B)` puts `a, s~_1 a, …, s~_m a` in one part.
  - That part is `Π_B`-invariant, which contradicts transitivity.
- **Jordan's theorem.** It gives `Π+_B >= Alt(B)`. A parity-corrected extension of `σ_n(g)|_B` lies in
  `Alt(B)`.
- **Dependency.** Step 6 uses `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`, which has
  no verdict yet (see §8).

### 18.4 `leavitt-cover-regular-realizer-models-iff-residually-finite`: PASS

- **1 ⟹ 2.** `NK_n = G`, so each finite quotient is one block, the Cayley graph of `N/(N ∩ K_n)`. Its
  expansion is uniform by property (T) of `N`, and every `σ_n(g)` lies in the regular group `Π_B`.
- **2 ⟹ 1.**
  - §18.2 on `Y_n` removes the centralizers.
  - In a regular group, an element with a fixed point is trivial. So relators fail only on whole blocks of
    total mass `o(|X_n|)`, and `t -> p_B(t)` defines exact homomorphisms `r_B : G -> Π_B` on the rest.
  - A block with `r_B(g) = 1` consists of fixed points of an approximation of `σ_n(g)`, so mass
    `δ|X_n|` forces some `r_B(g) ≠ 1`.
- **Reading.** The claim is correct as scoped. On regular blocks, excluding realized models is the same
  as proving the cover not residually finite. Off regular blocks, §18.3 says realized models exist
  whenever the cover is sofic.

## 19. Ozawa's SL(3,Z) block algebra (9a4114d4a): three PASS; the open claims are correctly stated

### 19.1 `kazhdan-block-algebras-contain-their-block-ideal`: PASS

- **Isolation.**
  - `σ ≺ π` gives `1 ⊂ σ ⊗ σ̄ ≺ π ⊗ σ̄`. Property (T) then gives a nonzero intertwiner, so `σ ⊂ π`.
  - Suppose `σ` lies in the closure of a set `S` of other irreducibles. Then `σ ⊂ ⊕S`, and projecting to
    a coordinate makes `σ` equivalent to a member of `S`, a contradiction. So `σ_j` is an open point.
- **Blocks.** The ideal of the open point has one-point spectrum and a faithful `n_j`-dimensional
  irreducible representation, so it is `M_(n_j)`. Every `σ_i` with `i ≠ j` kills it, so it is the
  coordinate block.
- **Quasitraces on `I`.** With `P_m ∈ I` central, `a = aP_m + a(1-P_m)`, and
  `σ(a(1-P_m)) <= ||σ|| ||a(1-P_m)|| -> 0`. Quasitraces on finite-dimensional corners are traces.
- The extension step uses `stw01-extensions-preserve-qt-linearity`, which was not re-reviewed.

### 19.2 `sl3z-ozawa-block-corona-has-unique-trace`: PASS, conditional on Bekka's theorem as imported

- **Limit trace.**
  - `tr σ_k(g) = (Fix_(p_k)(g) - 1)/(p_k^2 + p_k)`.
  - A non-scalar `3×3` matrix fixes at most `p + 2` projective points, because in the worst case its
    eigenvectors fill a plane and a line.
  - A nontrivial `g ∈ SL(3,Z)` is scalar mod `p` for only finitely many `p`.
- **Uniqueness.** An extreme trace of `A` is an extreme trace of `C*(Γ)` vanishing on the kernel, so a
  finite factor trace. By Bekka it is finite-dimensional, which §19.1 excludes, or it is `δ_e`.
- **Nonzero kernel.** The vector states at `[1:0:0]` converge to `1_P`, so `λ_(Γ/P) ≺ ρ_∞`. If `K = 0`,
  restricting to `P` gives `1_P ≺ λ_P`, which contradicts non-amenability of `P ⊃ SL(2,Z)`.
- **No traces on `K`.**
  - The norm-preserving extension `φ` of a bounded trace on `K` satisfies
    `φ(y^*y) = lim τ(y e_λ^2 y^*) <= φ(yy^*)`. By symmetry `φ` is a trace.
  - So `φ = cτ_0`, and `τ_0` vanishes on `K = N_(τ_0)`.
- **Import corrected at 85a9696d7, and the correction checked.**
  - The lane re-read Bekka (arXiv:math/0609102v2). The theorem is virtual: a finite factor representation
    is finite-dimensional, or its restriction to some finite-index `Λ` extends to `L(Λ)`.
  - The added orthogonality step is correct:
    - pass to the normal core of `Λ`;
    - `Λ` is ICC, so `φ|_Λ = δ_e`;
    - a nontrivial `g ∈ SL(3,Z)` has infinite `Λ`-conjugacy class, because a finite-index centralizer
      contains powers of every `E_ij(1)`;
    - distinct conjugates `g_i` have `g_j^-1 g_i ∈ Λ \ {e}`, so the vectors `π(g_i)ξ` are orthonormal;
    - Bessel's inequality gives `m|φ(g)|^2 <= 1` for every `m`, so `φ = δ_e`.
  - The same commit rewrites artifact Lemma 4.1 without dimension functions:
    `⊕_m (a-ε)_+ ≲ e_11 ⊗ 1` gives `m σ((a-ε)_+) <= σ(1)`. That is also correct.

### 19.3 `sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible`: PASS

- **(2) ⟹ (1).** `σ|_K = 0` gives `K ⊂ N_σ`, so `σ` descends to a quotient of `C*_r(SL(3,Z))`. That
  quotient is exact, because countable linear groups are exact, and Haagerup's theorem makes the
  descended quasitrace a trace.
- **(1) ⟹ (2).** A trace equals `σ(1)τ_0`, which vanishes on `K`.
- **Sufficient conditions.**
  - Exact `K`: apply Haagerup on `C*(K,1)`, then the extension lemma of §19.2.
  - Infinitesimal `a`: `m d_σ((a-ε)_+) <= σ(1)` forces `d_σ = 0`. Then `σ(x) <= σ(y) + ||x-y|| σ(1)` for
    positive `x, y` passes to the limit.

**Open claims.** `sl3z-ozawa-block-algebra-quasitraces-are-traces` and
`sl3z-ozawa-block-algebra-has-nontracial-quasitrace` are correctly OPEN. The `refuted_by` edge between them
names an OPEN claim, so it does not fire.

## 20. `finite-index-edge-hnn-embeds-in-fp-simple-group` and `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups` (b1a8b9632, corrected 4bbd55680): PASS

- **Import.**
  - Theorem 10.5 checked word for word against the arXiv:2408.05673v2 PDF text extracted on MSI on
    2026-09-12, line 1309: "Let G be a graph of groups such that all vertex groups are of type Fn and all
    edge groups have finite index in the vertex groups. Assume that G acts faithfully on its Bass–Serre
    tree. Then G embeds in a simple group of type Fn."
  - Theorem B, Theorem C and the definition of `BS_G` agree with the arXiv HTML, checked through WebFetch.
- **Hypotheses for the one-loop graph of groups.**
  - `A` is of type `F_2`, and both edge inclusions have finite index.
  - The kernel of the tree action is `∩_g gAg^-1`, the largest normal subgroup of `K` inside `A`. So
    faithfulness is exactly the stated hypothesis.
  - Theorem B applies as well: the action is cocompact and locally finite, and its edge stabilizers are
    conjugates of `C_2`, which is finitely presented.
- **(L1), (L2), (L4).** Correct.
  - A vertex stabilizer acts on finite balls through finite groups whose kernels intersect trivially.
  - A finitely presented residually finite group has solvable word problem.
  - Todd–Coxeter decides membership in finite-index subgroups.
- **(L3): false as landed, correct as corrected.**
  - As landed, it said an infinite-index edge "cannot be embedded stable letter to stable letter" into an
    extension with finite-index edges. That is false.
  - As corrected, `f(C_2) = s f(C_1) s^-1 <= B ∩ sBs^-1 = D_2` by Britton's lemma, and
    `A/(A ∩ D_i) ↪ B/D_i` bounds the index.
  - The example checks:
    - `u = b^-1 s` centralizes `F(a,b)`;
    - the projection sends `a, s` to the basis `a, b`, so `<a, s>` is free;
    - `F(a,b)` is normal, so it lies in the kernel.
  - The matching edits to `bh-embeddability-survives-decidable-edge-hnn` and to item 2 of
    `stable-permutation-hnn-of-type-a-actor-is-type-a` are consistent.
- **Impact.** The claim specializes Bux–Llosa Isenrich–Wu to one-vertex graphs of groups and records where
  the method stops. It adds no Boone–Higman class beyond theirs.

## 21. `thompson-v-sofic-iff-not-permutation-stable` and `cuntz-groupoid-admits-no-folner-sequence` (e03d940c3): PASS

- **Not sofic ⟹ stable.**
  - `χ(g) = lim_ω |Fix φ_n(g)|/k_n` is a class function. It is positive definite by
    `Σ c_i c̄_j |Fix(σ_j^-1 σ_i)| = Σ_(x,y) |Σ_i c_i [σ_i x = y]|^2`, up to `o(k_n)`.
  - By `thompson-v-character-simplex`, `χ = tτ_reg + (1-t)τ_triv`.
  - If `t > 0` along some `ω`, every `g ≠ e` moves a `t`-fraction of points, and tensor powers amplify the
    separation, so `V` would be sofic. So under (1), `t = 0` along every `ω`, and the trivial
    homomorphisms are Hamming-close.
- **Weakly locally stable ⟹ not sofic.** A sofic, weakly locally stable group is LEF (Bradford,
  Lemma 2.15), and `V` is not LEF. The remaining implications are definitional.
- **Reading.** Only the two-point character simplex and non-LEF are used. No property is decided. The
  content is that Bradford's "evidence that V is stable" is exactly evidence that `V` is not sofic.
- **Flexible stability (added at a47626583): correct.**
  - `V` is infinite and simple, so every action of `V` on a finite set is trivial.
  - A flexible correction on `Y_n >= X_n` with `|Y_n \ X_n| = o(|X_n|)` therefore makes each `φ_n(g)` fix all
    but `o(|X_n|)` points, and that rules out separating almost-homomorphisms.
  - The two directions give: not sofic ⟹ stable ⟹ flexibly stable ⟹ no sofic approximation.
- **Cuntz groupoid.**
  - The layer-cake identity gives `Σ_s ||s.m - m||_1 >= c_S ||m||_1`, which is where the `1/|S|` comes
    from.
  - `r_*` of counting measure intertwines `B_s` with `s`.
  - The sets `KF_u` partition `KF` by source.
  - Ma's definitions (arXiv:2110.11548) were not re-read here.

## 22. `fpbs-tree-projected-letter-exchange-nonunimodular` (4c08f019b): PASS

The same three checks as §17.
- **Index sums.**
  - At `u`: tail `e1` (index 2); heads `e4`, `e5` (index 1 each).
  - At `w`: tails `e2`, `e5`; heads `e1`, `e3`.
  - At `x`: tails `e3`, `e4`; head `e2` (index 2).
  - So every vertex of `Y` has two outgoing and two incoming exchange edges, and they can be labelled `s`
    and `t` outward.
- **Lift.**
  - Each edge of `A` joins distinct vertices, so `G_A` keeps every orientation and can only exchange `s`
    with `t`.
  - Take `D_t = D_s + c` and `τ = ±c` on `t`-edges. Then `D(ε) - τ(ε)` is `D_s` along an exchange edge and
    `-D_s` against one, so it is `G_A`-invariant, and the potential argument of §17 applies.
  - The reduction `t -> t^-1` for `D_t = c - D_s` is correct.
- **Counting.**
  - `(G_A)_(y_0)` fixes `z` (unique `e2`-successor) and then `y_1` (unique `e3`-successor). Orbit size `1`.
  - `(G_A)_(y_1)` fixes `z` (unique `e3`-predecessor), and the extension lemma swaps the two
    `e2`-predecessors of `z`. Orbit size `2`.
  - Both `y_0` and `y_1` lie over `w`.
  - The Bass–Kulkarni equations are inconsistent: `e1` gives `N(w) = 2N(u)`, `e2` gives `N(x) = N(u)`, and
    `e3` demands `N(x) = N(w)`.
- **Example.** `{(a,0),(a,2),(a,7),(b,1),(b,6),(b,8)}` has `D_b = 8 - D_a`, and it generates `F_2 × Z`
  through `(1,2)` and `(1,5)`.
- **Not checked.** The claim in artifact §3 that the whole automorphism group is discrete for the rigid set
  `{(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}`.

## 23. `thompson-f-binomial-pairs-have-common-multiples` (b3c0966d2): PASS

- **Exactness over `K`.** The image of `Z[H]^2 -> Z[H]` is the augmentation ideal, which is free abelian.
  So the relation sequence stays exact after tensoring with `K`.
- **`N ≠ 1`.** Otherwise `<a, c>` would be free of rank 2, which Brin–Squier excludes.
- **Common multiples.**
  - A basis element of `N/[N,N]` gives `(u, v) ≠ 0` with `u(a-1) + v(c-1) = 0`, and `u ≠ 0` because `K[F]`
    is a domain.
  - The involution `g -> g^-1` turns the common left multiple into a common right multiple, since
    `(1 - a^-1)R = (1 - a)R`.
- **Items 2 and 3.** They follow from `t(1 - t^-1ht) = (1 - h)t`, and the domain property keeps the product
  nonzero.

## 24. `char-zero-algebra-unit-hosts-exclude-unipotents` (fb8f58e9b): PASS, one wording remark

- **Step 2.** If `(1+ν)^q` were central, then `q log(1+ν)` would be central, so `ν` would be central. So `u`
  has infinite order modulo `C`.
- **Step 4.** `ν = c^-1 u - 1 ∈ B`, and for `p >= k`, `(1+ν)^p ∈ 1 + pB`. So `u^p` is killed by the
  reduction mod `p`, but it is nontrivial in `G`.
- **Step 5.** Simplicity forces `[g_i, b] ∈ pB` for infinitely many `p`. By (D) `G~` is then abelian, and a
  group of prime order `q` would put `u^q` in `C`.
- **(D).** For free `Z[1/m]`-modules, a coordinate divisible by infinitely many primes is 0. For
  `M_n(B_0)`, the Nullstellensatz gives `f : B_0 -> L`, `L` a number field, and `p^([L:Q])` divides the
  numerator of `N(f(b))` for only finitely many `p`.
- **Wording.** The title says "contain no unipotents". What is excluded is a non-central scalar multiple of
  a unipotent, as the body states.

## 25. `aut-f4-has-property-t` (95788b924): PASS as a citation

- **Consistent with the literature.**
  - Nitsche's computer-assisted proof for `Aut(F_4)`.
  - Kaluba–Nowak–Ozawa for `n = 5`, and Kaluba–Kielak–Nowak for `n >= 6`.
  - Property (T) passes to quotients.
- **Caveats.** The node lists the right ones: unrefereed, and the certificate was not rerun. The quotes were
  not re-extracted here.

## 26. Mapping class groups and Out(F_n) (ce98de0fc): the four established claims PASS

### 26.1 `outer-covering-lifts-are-virtual-sections`: PASS

- **Unique roots.** If `N` is torsion-free and every nontrivial centralizer is cyclic, then `x^k = y^k ≠ 1`
  puts `x` and `y` in `C(x^k) = <z>`, and torsion-freeness gives `x = y`.
- **(i).**
  - Let `θ` fix a finite-index `H` pointwise. Each `γ` has some `γ^k ∈ H` with `k >= 1`, by pigeonhole on
    cosets. Unique roots then give `θ(γ) = γ`.
  - So the extension is unique, and uniqueness makes `σ` a homomorphism.
- **(ii).**
  - On the kernel `L′` of the permutation action on `P`, every representative fixes `p̃`. `F_*` depends only
    on the class rel `P`.
  - A covering representative gives `f′(x) = x` and `f′_* π_* = π_* F_*`. So `f′_*` extends `λ̄(f)` from
    `H = π_* π_1(Σ̃, p̃)`.
  - By (i), all admissible `f′` induce the same automorphism. Based Dehn–Nielsen–Baer then makes `[f′]` in
    `Mod(Σ, x)` well defined.
  - Products of covering representatives cover the products, so `σ` is a homomorphism, and forgetting `x`
    returns `f`.
- **Converse.** Take the trivial cover and `P = {x}`.

### 26.2 `closed-mcgs-have-no-covering-lift-to-marked-covers`: PASS, conditional on Chen–Salter

- **Route.** §26.1(ii), then Theorem A of Chen–Salter. Injectivity of `λ` is never used.
- **Scope.** The notes are right: unbranched covers only, genus 3 not covered, and non-covering embeddings
  not excluded.
- **Dead route.** `closed-mcg-bh-via-covering-lift-to-marked-cover` has `requires: []` and dies only through
  `invalidates:`. So it fires if the invalidator ever loses its proof route. At landing the invalidator's
  route requires only §26.1 and the Chen–Salter import, both with working routes.

### 26.3 `birman-exact-sequence-does-not-virtually-split`: PASS as a citation

- It agrees with the literature: Chen–Salter, arXiv:1804.11235, Theorem A, for `g >= 4`.
- **Genus 2 splits virtually.**
  - By Birman–Hilden, every class has a representative commuting with the hyperelliptic involution, unique
    up to symmetric isotopy.
  - On the finite-index pure subgroup, those representatives fix each Weierstrass point.
- The quote was not re-extracted here.

### 26.4 `punctured-surface-mcgs-satisfy-permutational-boone-higman`: PASS as a citation

- The case summary matches the shape of their argument:
  - Dehn–Nielsen–Baer into `Aut(F_n)` for two or more punctures;
  - the double cover for one puncture;
  - capping boundary components;
  - the hyperelliptic quotient in genus 2.
- The quotes were not re-extracted here.

### 26.5 The open roots and premises: correctly stated

- **Named open cases.** `closed-surface-mapping-class-groups-satisfy-boone-higman` and
  `out-free-groups-satisfy-boone-higman` are the open parts of BBMZ Problem 5.3(2) and 5.3(3).
  - The item wording and the open status agree with the verbatim BBMZ list on main
    (`research/artifacts/boone-higman-frontier-2026-09-12.md`, lines 96–97 and 117–118): closed surfaces
    of genus `>= 3`, and `Out(F_n)` for `n >= 3`.
  - Their routes require OPEN premises, so neither root is established.
- **`out-free-groups-virtually-embed-in-aut-free-groups`.** Correctly OPEN.
  - Attempt 2 is right: restriction to a characteristic `K` gives `Aut(F_n)/K ↪ Out(K)`, since by §26.1(i)
    the kernel is `Inn(K)`.
  - The node honestly records that the literature status of virtual splitting of
    `Aut(F_n) -> Out(F_n)` for `n >= 3` was not determined. This review did not determine it either.
- **`closed-mcgs-virtually-embed-in-punctured-mcgs`.** Correctly OPEN.
  - Attempt 2's reading of Aramayona–Souto is right. A closed surface has no punctures to forget and no
    boundary to delete, and it is a subsurface only of itself. So the full group has no nontrivial map to a
    bordered or punctured target of genus `<= 2g-1`.
  - Finite-index subgroups are untouched, as the node says.

## 27. The 16:40–16:42 landings (8eaac4437, cbc0cacb1, a442c4975, 34e7a8c0b, 272475ab8): eleven established claims PASS

### 27.1 `rsg-kazhdan-rf-obstruction-implies-hyperbolic-rf`: PASS, conditional on its imports

- **A quotientless hyperbolic group.** By Kapovich–Wise there is a nontrivial hyperbolic group with no
  nontrivial finite quotient. It is non-elementary, since infinite elementary groups are residually finite.
- **Trivial finite radicals in `H = G_1 * K`.**
  - Edge stabilizers of the Bass–Serre tree are trivial. So a nontrivial finite subgroup normalized by `G_1`
    fixes exactly one vertex, `G_1` fixes that vertex too, and the subgroup is a finite normal subgroup of
    `G_1`, which is trivial.
  - So `E_H(G_1) = E_H(K) = E(H) = 1`.
- **Common quotient.** In the characterization of `olshanskii-g-subgroup-quotient-theorem`, `K(X) = X`
  when `E(X) = 1`. So both factors are G-subgroups, and they surject onto one non-elementary hyperbolic `Q`.
- **Properties of `Q`.** `Q` has (T) as a quotient of `K`. A finite quotient of `Q` restricts to one of
  `G_1`, so `Q` has none. `Q` is infinite, so it is not residually finite.
- **Host.** BBMZ Theorem 1.4 (§27.3) puts `Q` in a contracting rational similarity group.
- **Imports.** `kapovich-wise-rf-iff-finite-quotients`, `torsion-free-hyperbolic-kazhdan-partner-exists`
  and `olshanskii-g-subgroup-quotient-theorem` have been on main since 2026-09-11. They are outside this
  review.
- **Reading.** This limits what an obstruction method can reach. It says nothing about residual finiteness
  of hyperbolic groups in either direction, as the node says.

### 27.2 `fw-subgroups-of-eventually-similar-groups-virtually-embed`: PASS

The route (§§1–6) was read in full. It is the argument of §10 with the self-similar group replaced by a
groupoid, and the changes check:
- The classes `φ∘H` are well defined because `H` is a groupoid, and `[β_v∘n] = [β_v]`.
- Out-degree `>= 2` makes deep cones strictly smaller, so `P` is finite and its images cover `X`.
- `g∘φ_p = φ_p∘n` forces `n` into the vertex group `H_(s(p))`.
- **Part 3.** A synchronous vertex group permutes the level-`k` paths for each `k`. An element in every
  kernel fixes every point, so the vertex group is residually finite.
- **Scope.** The rational similarity group discussion correctly places the break at non-surjective nuclear
  maps.

### 27.3 `hyperbolic-groups-embed-in-contracting-rsgs`: PASS as a citation

It agrees with BBMZ, arXiv:2309.06224: hyperbolic groups embed in full contracting rational similarity
groups, the first step of their Boone–Higman theorem. The TeX quote was not re-extracted here.

### 27.4 `leavitt-tensor-powers-are-twisted-crossed-products`: PASS, one wording remark

- **Crossed product.**
  - `u_j u_j' = u_j' u_j = 1`, and `u_j` has degree `e_j - e_(j+1)`.
  - `A_v = u^λ A_(c e_d)`, so `A = ⊕_λ u^λ C`.
  - Conjugation by homogeneous units preserves `C`.
  - `ω(λ,μ)` is a degree-zero unit, so it lies in `C^×`, and the multiplication formula checks.
- **Sanity check at `d = 2`.** `L ⊗ L = C[t, t^-1; α]` with `C = L_0 ⊗ L` regular supercoherent and
  K-trivial (§27.5). Waldhausen's theorem then gives `K_*(L ⊗ L) = 0`, which is the known Ara–Cortiñas case.
- **Wording.** "The cocycle is not trivial" is shown only for the chosen units, through `u_1 u_2 ≠ u_2 u_1`.
  Cohomological nontriviality is not proved, and nothing uses it.
- **Scope.** `K_*(L^(⊗d)) = 0` for `d >= 3` is not established, as the node says. Iterating Waldhausen
  fails after one step, because the intermediate ring `C ∗ Z` is again not coherent.

### 27.5 `leavitt-crossed-product-coefficient-ring-is-k-trivial`: PASS

- **Colimit.** `L_0` is the union of the `M_(2^m)(k)` along `a ↦ a ⊗ 1_2`. So
  `C = colim M_(2^(m(d-1)))(L)` along free extensions.
- **Semihereditary.** `L` is hereditary. A finitely generated left ideal is `C ⊗_(C_m) I_m` with `I_m`
  projective, by flatness.
- **Regular supercoherent.** Finitely generated ideals and finite resolutions come from some stage and
  survive base change.
- **K-theory.** `K_n` commutes with filtered colimits and with matrices. `K_n(L_k(1,2)) = 0` for regular `k`,
  because multiplication by `1 - 2` on `K_*(k)` is invertible.

### 27.6 `rational-units-rescale-to-integral-units`: PASS

- **Gauss's lemma.** `u'v' = N ∈ Z`. A prime `p` dividing `N` would give a zero divisor in `F_p[G]`.
- **Transfer.** The units with one-element support are the `λg`, so nontriviality transfers in both
  directions.
- **Promislow group.** It is torsion-free and virtually `Z^3`, and Kropholler–Linnell–Moody covers
  torsion-free elementary amenable groups.
- The two new roots are correctly OPEN, and the route from `Q` to `Z` checks.

### 27.7 `coherent-flat-group-algebra-hosts-force-fp-infinity`: PASS, conditional on Chase and Bieri–Eckmann

- **Reduction.** Flatness and the summand pass to `K[H]` through the free extension `K[H] ⊂ K[S]`.
- **FP_∞.**
  - Flat base change gives `Tor^(K[S])_k(ΠB, K) = Tor^B_k(ΠB, M)`, which vanishes because `ΠB` is flat
    (Chase).
  - The summand then kills `Tor^(K[S])_k(ΠK[S], K)`, and the Bieri–Eckmann criterion applies.
- **Part 2.** Shapiro through the flat extension, and coinduction when `K[S]` is a bimodule summand.
- **`Z wr Z`.** The spectral sequence has two columns, so `H_0(Z; Λ^2 K^(Z)) ↪ H_2`. Shift orbits on the
  `e_i ∧ e_j` are indexed by `j - i`, so the coinvariants are infinite-dimensional.

### 27.8 `nekrashevych-completions-contain-their-coefficients`: PASS

- **(1).** `Ψ` is a unital homomorphism, so the set where it agrees with the inclusion is a subalgebra.
- **(2).**
  - `α_(n+1) φ_n = φ_(n+1) α_n`, and `α` identifies `B_∞` with the corner `E_11 B_∞ E_11`.
  - In the corner skew Laurent ring, `t_- t_+ = p_0`, `t_+ t_- = [p]_0` and `t_+ c t_- = α(c)`.
  - The defining relation maps to `ψ(b) = [b]_0`.
- **(3) and strong grading.** Both check.

### 27.9 `saturated-invariant-ideals-block-completion-simplicity`: PASS

`ψ(I) ⊆ M_d(I)`, and saturation makes `ψ̄` injective. `O_ψ/J = O_ψ̄` together with §27.8(2) gives
`J ∩ B = I`.

### 27.10 `simple-monomial-completions-kill-the-tree-action-kernel`: PASS

- `N` is closed under restriction, so the recursion descends to `P/N`.
- The boundary representation on `K[X^ω]` satisfies `g = Σ_x s_(π_g x) g|_x s_x^*` on basis words. So
  `O_ψ̄ ≠ 0`, and `J` is proper.
- A subgroup without finite quotients acts trivially on every level, so it lies in `N`.

### 27.11 `fpbs-relative-gap-along-any-subgroup-separates`: PASS

- **`p_u(I;G) <= p_u(G)`.** Long-range order on `Γ` at some `p′ ∈ [p_u, p)` restricts to `I` and increases
  with `p`. Hutchcroft–Pan with `H = I` then gives uniqueness along `I`.
- **(2 ⟹ 1).** Left multiplication by `h ∈ I` preserves the law and `I`. So no cluster meets `I` infinitely
  often at `p`, and monotonicity gives `p <= p_c(I;G)`.
- **(1 ⟹ 2).** Uses `fpbs-hp-relative-sharpness`, an established import on main.
- **Import.** `fpbs-hp-uniqueness-and-long-range-order` (Hutchcroft–Pan, Theorem 1.4) was not re-extracted
  here.
- The OPEN claims of 272475ab8 are correctly OPEN: Choi–Seo Question 1.2, the Juschenko–Nagnibeda question,
  and the residual class.

## 28. Cairn state on MSI

`cairn why` ran as a detached job at tip 44c847dd5 (16:44). It finished with its DONE sentinel.
- **REFUTED:** `leavitt-tensor-powers-are-left-coherent`, `decidable-groups-embed-in-rover-nekrashevych-hosts`,
  `nuclear-factor-with-infinite-mf-tensor-exists`.
- **INVALIDATED routes:** `leavitt-tensor-powers-k-theory-via-coherence`,
  `prime-field-leavitt-powers-k-theory-via-coherence`, `boone-higman-via-rover-nekrashevych-hosts`.
- **ESTABLISHED:** `fpbs-tree-projected-reversible-letter-nonunimodular`,
  `fpbs-tree-projected-letter-exchange-nonunimodular`, `sl3z-ozawa-block-corona-has-unique-trace`,
  `thompson-v-sofic-iff-not-permutation-stable`, `finite-index-edge-hnn-embeds-in-fp-simple-group`.
- **OPEN:** `boone-higman-conjecture`, `char-two-linear-groups-satisfy-boone-higman`,
  `leavitt-tensor-powers-have-trivial-k-theory`, `fpbs-tree-projected-cayley-graphs-strict-thresholds`,
  `nuclear-algebra-without-uct-exists`, `relative-normalization-modulo-kazhdan-kernel`, `nonsofic-hyperbolic-group`,
  `non-hyperlinear-group`, `kazhdan-edge-coproduct-rank-is-inner-rank`, `stw99-problem-i-quasitraces-are-traces`,
  `thompson-v-not-sofic`.

So the refutations and invalidations reviewed in §§6, 9 and 10 took effect as their nodes say, and no root
checked here was falsely established.

## Scope from 16:43

For commits after 8987f4ea6, `swarm5-reviewer` covers Thompson groups and full groups, Strong Atiyah,
Baum–Connes and Kadison–Kaplansky, quasitraces, weak soficity, and Gottschalk and direct finiteness. This
artifact continues with the other topics.

## 29. Artin groups, tree torsion, UCT ascent and the Iwahori census (16:45–16:50)

### 29.1 `c-tilde-artin-groups-satisfy-permutational-boone-higman` (21dfc8888): PASS; a new case of BBMZ Problem 5.3(13)

- **Identification** (`c-tilde-artin-groups-are-punctured-plane-braid-groups`, citation of Allcock).
  - `x ↦ 2cos(2πx)` is the quotient by `<x ↦ x+1, x ↦ -x>`. It is free off `½Z` and lands in `C - {±2}`.
  - For coordinates avoiding `½Z`, `x_j ± x_k ∉ Z` says exactly that the images differ.
  - So `V_0/(Z^n : 2^n) = Conf_n(C - {±2})`. The π_1 statement for affine types is Nguyễn's, cited through
    Allcock.
- **Embedding.**
  - Fadell–Neuwirth: `Conf_(n+2)(C) -> Conf_2(C)` is a bundle with fibre `Conf_n(P)`, and `S_n` acts
    fibrewise and freely.
  - `Conf_2(C) ≅ C × C^×` is aspherical, so `π_1 UConf_n(P)` injects into `π_1(E)`.
  - `E -> UConf_(n+2)(C)` is a covering of degree `[S_(n+2) : S_n] = (n+2)(n+1)`. So `A(C̃_n) <= B_(n+2)`,
    in agreement with Charney–Crisp.
- **Boone–Higman.**
  - `B_m <= Aut(F_m)` (Artin representation).
  - `Aut(F_m)` satisfies PBH by BFFHZ Theorem A, and PBH passes to subgroups.
  - Zaremsky Corollary B gives the finitely presented simple envelope.
- **Status of the problem.** BFFHZ v2 (April 2025) and BBMZ v3 Remark 5.4 (May 2025) both list the Euclidean
  types other than `Ã_n`, `C̃_2` and `G̃_2` as open, which includes `C̃_n` for `n >= 3`. The consequence
  follows from published results in a few lines, and the lane's novelty search was bounded (arXiv abstracts
  through 2609.01868). It is a genuine new case, but a light one, and priority should be claimed only after a
  fuller search.

### 29.2 `spherical-artin-groups-are-linear-over-q-x-y` and `admissibly-oriented-artin-groups-split-over-free-groups` (21dfc8888): PASS as citations

- Crisp's embedding into products of types A, D and E, together with faithfulness of the Krammer–Digne–
  Cohen–Wales representations over `Q(x,y)`, gives faithful block sums. This is consistent with the
  literature. The statements were read through Paris's survey.
- Jankiewicz's Theorem 4.3 is quoted with its scope. Finite index of the edge group is not claimed, and that
  is correct.
- `spherical-artin-groups-satisfy-boone-higman` and `admissibly-oriented-artin-groups-satisfy-boone-higman`
  are correctly OPEN.

### 29.3 `regular-tree-torsion-orders-have-primes-at-most-degree` (08a7771c7): PASS

The orders of the level images divide `|Aut(B_n)| = (d!)^(1+⋯+d^(n-1))`. They form a divisibility chain
bounded by `m`, so they stabilize, and faithfulness gives `m = m_N`.

### 29.4 `cycle-transposition-lef-group-has-no-regular-tree-action` (08a7771c7): PASS

- **Word problem.**
  - For `n >= 4l+5`, a point with `|x̃| >= l+2` stays at residues in `[2, n-2]`, so `τ` never acts and
    `w_n(x) = x + e(w)`.
  - A point with `|x̃| <= l+1` stays in `[-2l-1, 2l+1]`, where `0` and `1` are the only preimages of their
    residues.
  - So `w = 1` iff (a), (b) and (c) hold, which is polynomial.
- **One-coordinate elements.**
  - `c_k = [τ, σ^k τ σ^-k]` is supported on `{n : n | k ± 1}`, and `g_p = [c_(p+1), c_(p-1)]` is supported
    at `n = p` only.
  - In coordinate `p` the two 3-cycles overlap in two points, so they do not commute.
- **Alt(p).** `π_p` is injective on the normal closure. `π_p(Γ) = Sym(p)` (a `p`-cycle and an adjacent
  transposition), so the normal closure is `Alt(p)`.
- **Consequences.** Items 4–5 follow from §29.3 and `|Alt(p)| > d!` for `p > d`.
- `rf-higman-embedding-for-decidable-groups` is correctly OPEN. Its quote of Kharlampovich–Myasnikov–Sapir
  was not re-extracted here.

### 29.5 `o2-zp-cartan-fixing-iff-rokhlin-uct-ascent` (8f6d0119c): PASS, conditional on Barlak–Li and Izumi

- **`Asc_p ⟹ D_p`.**
  - The crossed product by an outer action is a unital Kirchberg algebra.
  - Izumi makes `α` approximately representable, so `α̂` is Rokhlin.
  - Takai gives `B ⋊ Z_p ≅ M_p(O_2) ≅ O_2`.
- **`D_p ⟹ Asc_p`.**
  - Approximate representability, lifted through `C^β`, gives strong approximate innerness.
  - **Outerness.** If `β_1 = Ad(v)` with `v^p = 1`, then `z = v^* w` has order `p`. It commutes with `C` and
    with `w`, and its zeroth Fourier coefficient vanishes. So it is a non-scalar central unitary in
    `C ⋊ Z_p ≅ B ⊗ M_p`, which contradicts simplicity.
  - Cartan-fixing then gives the UCT for `B ⊗ M_p`, and so for `B`.
- **Reading.** It is a restatement, and it proves no case, as the node says.
- `izumi-rokhlin-approximately-representable-duality`: PASS as a citation.

### 29.6 `sl3-z2-iwahori-index-8-torsion-free-misses-level-4` (6bb076985): PASS on the reduction; census output not rerun

- **Index and quotient.** `[I:W] = [U : W̄][K_1 : K]`. `V = K_1/K_2` is the trace-zero `3×3` matrices over
  `F_2`, of order `2^8`, and `S = K/K_2` is `W̄`-invariant.
- **Involutions.** A rank-2 idempotent `ē` lifts to an idempotent `e` over `Z_2`. `I - 2e` is an involution
  of determinant `1` in the coset `I + 2ē + K_2`. So `S` must avoid all `28 = 7·4` rank-2 idempotents.
- **Small codimension.** A hyperplane avoiding them would contain an avoiding codimension-2 subspace.
- **Census.** No codimension-2 subspace avoids the idempotents, and none of the 1500 avoiding codimension-3
  subspaces is `U`-invariant. This is recorded in `experiments/strong-atiyah-sl3z/iwahori_level4_census.out`
  and was not rerun here.
- `sl3-z2-iwahori-has-torsion-free-subgroup-of-index-8` is correctly OPEN.

### 29.7 `fpbs-sphere-fibre-operator-iff-critical-fibre-l2` (4a1570fd4): PASS

Checked against artifact Theorem A.
- **(a) ⟹ (b).**
  - Right multiplication by `g_q` maps `Γ_q` onto `Γ_(q_0)`, and Harris–FKG with translation invariance
    gives `σ_p(q) <= p^-L σ_p(q_0)`.
  - `σ_p(q_0) <= N(σ_(p,R_0)) <= θ`, because `N(f) >= f(q_0)`.
  - The sphere cut gives `N(C_(p,R_0)) <= θ N(σ_p)`. `N(σ_p) <= χ_p < ∞` below `p_c`, so the bound absorbs.
  - The pointwise increasing limit passes to `p_c`, since `N` is lower semicontinuous.
- **(b) ⟹ (c).**
  - Averaging the sphere cut over `r ∈ [0, m]` uses `Σ_r σ_(p,r) <= σ_p`, since the spheres are disjoint.
  - With `n + 1 >= e N_p` each block gains a factor `1/e`, and `n < e N_p` gives the stated rate.
- **(c) ⟹ (a).** A sphere of large radius.
- **L2 gap.** It rests on the fibre-summed operator import (F4) and Hutchcroft's openness (F5), both on main.
- **Reading.** The equivalence settles nothing about whether the conditions hold, as the node says. Over
  amenable kernels with rapid-decay quotients, the two premises are shown to be as hard as critical L2
  boundedness.

### 29.8 KL length-six residue shapes (a63352293, 2cf7bde45): two PASS, conditional on the weight-test import

**`kl-three-coincidence-residue-words-inject-with-room-for-loops`.**
- **(WT1).** `Σθ = 3 + α + (1-α) = 4 = n - 2`.
- **(WT2).**
  - `h >= 2` gives weight `>= 2`.
  - Pure loop cycles give `α k_y >= 2` or `(1-α) k_x >= 2`.
  - `m = 1, h = l = 1` is exactly (C1). `m = 1, h = 0` is exactly (C2).
  - For `m >= 2`, at least `m - 1` light–light junctions on each side carry nonzero powers, so the weight is
    `>= 2`.
- The curvature step is inherited from `kl-four-same-sign-corner-words-weight-proof`.

**`kl-involution-loop-residue-with-interior-light-label-injects`.**
- **Claim A.**
  - `m = 1, h = l = 1`: `W = 1 + (|i|+|j|)/2`. (I1) and (I3) exclude the trivial labels with `|i| + |j| <= 2`,
    so admissible cycles have `W >= 5/2`.
  - `h = 0, l = 2`: `W = 1` is excluded by (I2), and `W = 3/2` has a nontrivial label.
  - `m = 2, h = 1`: `W = 2` forces the single pattern whose label is excluded by (I4).
- **Transfer count.**
  - Each receiving region pairs a heavy corner (`c_0` or `c_3`, heavy in both shapes) with a loop corner,
    and the pairs are disjoint. So `W(A) >= 3k/2`.
  - `k >= 2` gives `κ <= 2π - kπ <= 0`, and `k = 1` gives `κ <= 0` by Claim A2.
  - The boundary region stays `<= 2π`, and the total `<= 2π < 4π` is a contradiction.
- **Not checked.** The face tracing that assigns the regions across each loop-square arc was checked only
  against the corner order `c_0, …, c_5`. It was not redrawn.

**Import gap.** Both proofs rest on the Ahmad–Al-Mulla–Edjvet restatement of the Bogley–Pride weight test and
on standard picture calculus. The lanes record this themselves, and it was not re-read here.

## 30. `vertex-rounding-deep-nonunit-root-mass-vanishes` (66253a5d8, 3396c3df5, efe6ca919): PASS

This is the highest-impact item in this artifact. It closes the fifth premise of
`theorem-e-vertex-unit-type-via-deep-root-mass`, so unit-type rounding of the Theorem E vertex now follows from
(H1) alone. The whole of `research/artifacts/nh-deep-mass-2026-09-12.md` §§1–5 was checked against the exact
statements of the four premises at 200b50c18.

- **Premises used within scope.**
  - Item 1 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`: finite Steinberg images, with
    `R_+ -> B_n` onto.
  - Item 1 of `vertex-rounding-non-unit-mass-at-origin`: intermediate places carry trace `<= 12η_n`.
  - Item 3 of `nonunit-component-root-mass-is-log-scale-folner`: `η_n` per `d`-adic scale.
  - Items 1 and 3 of `compressor-transport-exactifies-under-vertex-rounding`. These hold for every compressor
    with all entries `>= 1`, so for `A^k` and for `B^k = P A^k P^-1` with `k` fixed. `A = L L^T` gives
    `det A = 1`. Each `Ad M` maps `Γ` into `Γ` by fixed words, so `δ_n -> 0` for each fixed `M`.
- **Lemma 1, exact invariance.**
  - `h_31(u)` is a genuine element of `St_r(B_n)`, hence of `π_n(Γ)`. Conjugation by it scales `x_12(f)` by
    `u^(±1)`, so `μ_n` is invariant under `χ -> χ(u·)`. This is exact, not approximate.
  - Invariance under the finite group `U_0` gives the orbit disintegration.
  - `Sh` is orbit-invariant because `u x^a A_0 = x^a A_0`.
- **Lemma 2.**
  - (a) `φ_M(x^(cw) R_+) ⊆ x^(cMw) R_+`.
  - (b) The event is `u ∈ ker Λ`. `λ_0` factors through the local ring `A_0`, so a relation among the
    `h_j = x^(cMw) y^j` gives `g R_+ ⊆ ker λ_0`, so `g ∈ J(χ_0)`. `y` is nilpotent there, so
    `h_(j_0) ∈ J(χ_0)`, which contradicts `j_0 <= ℓ`.
  - The rank count over `A_0` with residue field `F_q` gives `2q^-(ℓ+1)` over units. A uniform element of the
    group pushes forward to the uniform measure on the orbit.
- **Lemma 3.**
  - `|E_k e_i|_j <= Cθ^k <= γ_k ℓ_i v_j`.
  - `{t : ⌊tv⌋ ∈ Sh} = [0, s)`, by right-continuity of `⌊tv⌋` and down-closedness.
  - `s >= depth` because `v <= 1`.
  - Both inequalities for `c_i` check, the lower one because an integer vector below `x` lies below `⌊x⌋`.
- **Parameters.** The order is `L`, then `k` (with `log((1+γ_k)/(1-γ_k)) < β/4`), then `K`, all independent
  of `n`.
  - `c_i >= L` follows from `ε < 1`.
  - `c_i - L >= (1-ε)s/((1+γ_k)ℓ_iΛ)` from `s >= K`.
  - `c^(1) >= ⌊(K-1)/N⌋` from `M1 <= N·1`.
  - Three uses of Lemma 2(b) give `6q^-(L+1)`.
  - Transported origin characters stay at the origin, since `φ_M(x_i)` is nilpotent in `R_+/J`, and unit
    components stay unit type (item 1 of the Følner claim).
- **Ratio and counting.**
  - For `M_+`, `ρ > β - β/4 - β/4`. For `M_-`, the mirror bound uses `ℓ_B = Pℓ_A`, and the Perron vector of
    `min(i,j)` increases, since `λ(v_d - v_1) = Σ(j-1)v_j > 0`.
  - `E_+` and `E_-` are disjoint, and both lie in `{depth >= K′}` with `2 <= K′ <= K`. So
    `μ_n(E_+) + μ_n(E_-) <= μ_n(depth >= K) + μ_n(K′ <= depth < K)`.
  - Combined with `μ_n(E_±) >= μ_n(depth >= K) - 6q^-(L+1) - η_n^±`, this gives
    `μ_n(depth >= K) <= μ_n(K′ <= depth < K) + 12q^-(L+1) + η_n^+ + η_n^-`, and the displayed conclusion follows.
- **Limit.** For fixed `L`, every term except `12q^-(L+1)` tends to 0 along `U`. So the limit is `<= 12q^-(L+1)`
  for every `L`, hence 0.
- **Not re-derived.** The Milnor §9 conjugation formula for `h_31(u)` was used as stated, and it agrees with
  conjugation by `diag(u^-1, 1, u)` in `GL_r`.

**Reading.**
- Together with §3 and item 5 of the shallow claim, every (H1) rounding of a trace-preserving representation of
  the Theorem E actor becomes unit type after its non-unit constituents are trivialized.
- `theorem-e-vertex-rounds-to-unit-type-representations` and `non-hyperlinear-group` stay OPEN. What remains is
  (H1), `hs-stable-vertex-rounding-for-every-model`, a flexible Hilbert–Schmidt stability statement for the
  higher-rank Kazhdan group `EL_r(F_q[x_1..x_d])`, together with the other premises of the Theorem A endgame.
- Strict HS stability is impossible there (Becker–Lubotzky), and flexible HS stability of such groups is open.

## 31. Type [A_2] actions, one-relator groups and HS stability (12bd1722d, b3a43bc19, 677c04019)

### 31.1 `a2-action-with-non-finitely-presented-image`: PASS; it answers FFWZ Question 5.8

- **`normalizer-extension-of-type-a-actor-is-a2-cover` checks.**
  - `Π(γ,w) = γφ(w)` is a homomorphism, and the semidirect product has a finite presentation.
  - The projection of a point stabilizer to `F_m` contains the kernel of the action on the finitely many
    `Γ`-orbits. Its kernel `Stab_Γ(x)` is finitely generated.
  - `ΓQ/Γ ≅ Q/(Q ∩ Γ)` is a quotient of `ΓQ` by the normal closure of finitely many elements.
- **`Q ∩ Γ = 1`** (not spelled out in the node).
  - On a brick, an element of `SV_V` changes prefixes in only finitely many coordinates.
  - If `δ_w` agreed with a branch `h_v τ_g h_u^-1` on `B(u)`, then `w(κ(s)) = κ(g^-1 s)` for all `κ ∈ B(u)`
    and all `s` outside a finite set, which forces `w = 1`.
  - `w ↦ δ_w` is injective, so `Q ≅ Z wr Z`, which is not finitely presented (Baumslag). The kernel is
    `ker φ`.
- **`twisted-btb-clopen-action-is-type-a`, checked in outline.**
  - Clopen sets are brick unions, and splitting a brick raises the count by one.
  - `SV_G` is transitive on brick partitions with the same number of pieces.
  - Orbits of tuples are classified by the pattern of nonempty atoms.
  - The stabilizer is `D(U) × D(U^c)`.
  - The atom-matching step (5) was not re-read line by line.
- **Item 3.** That the simple quotient of `SV_(G~)` is not finitely presented rests on
  `abstract-btb-simple-quotient-fp-gate`, which was not reviewed here.

### 31.2 `a2-kernel-removal-forces-recursive-kernel`: PASS

- **(a).** Membership in each stabilizer is decidable, because it and the finitely many nontrivial double
  cosets are complementary r.e. sets. The kernel is co-r.e.
- **(b).** A sharp embedding gives `G/K ↪ G′/K′`, which is finitely presented. So `K` is r.e., hence recursive.
- **(c).** The transvections `r_a` give `α_w(x_1) = x_1 w(x_2)`, and `α_w ∈ K` iff `w(g) = 1` for every
  `g ∈ Γ`. That is many-one reduction from the mixed identities, and `A/K` is not recursively presented when
  they are not recursive.
- `a2-pairs-embed-in-a2-pairs-with-fng-kernels` (FFWZ Question 5.9) is correctly OPEN.

### 31.3 One-relator groups: four PASS

- **`baumslag-gersten-base-is-elliptic-in-every-tree-action`: PASS.**
  - `ℓ(a) = nℓ(a)` makes `a` elliptic.
  - Case A uses the fixed-set projection.
  - In case B the nested fixed trees have a unique common end `ξ`, and `β_ξ` vanishes on `N` and on `b`. So
    every element of `B` is elliptic, and by Serre `B` fixes a vertex, which must lie in `∩T_j`.
  - In the midpoint case, the pointwise stabilizer of the edge contains `<a^2, b^2> ≅ BS(1, n^2)`.
- **`magnus-moldavanskii-hierarchy-with-decidable-edges`: PASS as a citation**, through the Linton–Nyberg-Brodda
  survey.
- **`magnus-hnn-permanence-forces-one-relator-boone-higman`: PASS as a conditional theorem.**
  - Step 2: the rewritten relator is cyclically reduced and shorter, and Tietze moves give `H*_β ≅ G`.
  - Step 3: `<b> ≅ Z` by the Freiheitssatz, `σ_x(r_3) = αγ - γα = 0`, and at most `n-1` letters other than `x`
    remain.
  - The node itself says that on the data the induction uses, the premise is equivalent to the conclusion.
    So this is a reformulation with one extra hypothesis, not progress on the one-relator problem by itself.
- **`virtually-free-by-cyclic-groups-satisfy-boone-higman` and `free-generalized-bs-groups-have-type-a-overgroups`:
  PASS.**
  - BLIW Remark 12.7 plus closure of `B_A` under finite-index overgroups.
  - For `k <= 1`, `K <= F(x,y) ⋊_ψ Z ∈ BS_(F_2)`.
  - No novelty is claimed, correctly.
- `one-relator-groups-satisfy-boone-higman` and `bh-embeddability-survives-magnus-subgroup-hnn` are correctly OPEN.

### 31.4 HS stability: two PASS

- **`injective-limit-trace-flexible-hs-repair-is-strict`: PASS, conditional on Jung's (1) ⟹ (2) and on Connes.**
  - Step 1 moves the limit trace onto the flexible corrections, with error `2(1 - d/D)`.
  - Step 3 pads `σ_(k(n))` to dimension exactly `d_n`, with trace error `<= 2 d_n^-1/2`, because
    `e_(k(n)) <= d_n^1/2`.
  - Both matrix models are microstates of `X` along `ω`. Tubularity in every size `k = d_n` then conjugates
    them.
- **`amenable-flexible-hs-stability-is-strict-hs-stability`: PASS.**
  - Flexible corrections make `τ` a limit of finite-dimensional characters, so `τ` is trivial on `Rad_fd`.
  - `L_τ(Γ) = π_τ(Q)''` is injective for amenable `Q`.
  - The contradiction with `η_n >= c` along `ω` checks.
- **Reading.** A group separating flexible from strict HS stability needs a non-amenable maximal almost periodic
  quotient. `flexibly-but-not-strictly-hs-stable-group-exists` is correctly OPEN.

### 31.5 Cairn state of the non-hyperlinear chain

`cairn why` at d6a3a0d44 (detached MSI job):
- `theorem-e-vertex-rounds-to-unit-type-representations` is OPEN.
- Its route `theorem-e-vertex-unit-type-via-deep-root-mass` has every premise in hand except
  `hs-stable-vertex-rounding-for-every-model`, which is (H1).
- `non-hyperlinear-group` is OPEN.
- The same run printed `requires is mandatory` errors for two route files of other lanes:
  `leavitt-ternary-frame-tree-uniformization-proof` and `locally-finite-hnn-regular-rank-model-proof`.

## 32. K-theory of Leavitt tensor powers through Farrell–Jones, and linear Boone–Higman in positive characteristic (2b19d1c07, d34e26446)

**What this settles in Cairn.** The cascade establishes two claims:
- `positive-char-linear-groups-satisfy-boone-higman`: every finitely generated linear group over a field of
  positive characteristic embeds in a finitely presented simple group;
- `char-two-linear-groups-satisfy-boone-higman`.

Both depend on the unrefereed Khanh criteria.

### 32.1 `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`: PASS, conditional on four standard imports

- **Bartels–Reich form.**
  - `(c u^λ)(c′ u^μ) = c α_λ(c′) τ_(λ,μ) u^(λ+μ)`.
  - `α_g α_h = Ad(τ_(g,h)) α_(gh)` and the cocycle identity follow from associativity, and `u^0 = 1`
    normalizes.
- **Cyclic pieces.** `u^(mλ)(u^λ)^-m` is a unit of degree 0, so it lies in `C^×`. The restricted crossed
  product is the skew Laurent ring `C_φ[t, t^-1]`, and its module category does not depend on the section.
- **Laurent regular coherence.**
  - Localize centrally at monomials. Finitely presented modules descend by clearing monomial denominators, and
    finite projective resolutions survive flat base change. The anti-automorphism handles sides.
  - This step is needed: Bartels–Lück need `C[Z^m]` for every `m`, and they record that Laurent inheritance of
    regular coherence is open for general rings.
- **Nil vanishing.** Bartels–Lück for `A = C_⊕`, translated to rings through their rings-versus-categories
  corollary and Lück–Steimle's idempotent completion. The mapping torus of a self-map of a contractible spectrum
  is contractible.
- **Assembly source.** An `Or`-spectrum homology theory that vanishes on every orbit vanishes on every `Λ`-CW
  complex, by skeleta, the five lemma and the colimit.
- **Sanity check.** At `d = 2` this recovers Ara–Cortiñas.
- **Independent check.** It agrees with `research/artifacts/leavitt-fj-crossed-product-check-2026-09-12.md`
  (PASS, no gap). The imports were read from arXiv TeX sources by the lanes and were not re-extracted here.

### 32.2 The Boone–Higman cascade: PASS on the wiring

- **`prime-field-leavitt-powers-k-theory-via-all-degree-vanishing`.** Quillen and non-connective K-theory agree
  in degrees `>= 1`.
- **`leavitt-power-projective-e-fp-from-trivial-k-theory`.**
  - `R_(d-1)` is central simple and finitely presented.
  - `M_m(R_d) ≅ R_d`, because `M_m(L(1,2)) ≅ L(1,2)` for every `m`.
  - The centre of `E_m` is finite, so the quotient stays finitely presented.
- **`positive-char-linear-groups-via-leavitt-projective-elementary`.** The embedding claim (review-backlog §16,
  PASS) together with finite presentation at `d+1` factors.
- **`char-two-linear-groups-via-leavitt-tensor-powers`.** The host claims passed in
  `review-boone-higman-leavitt-tensor-hosts-2026-09-12`.
- **Trust surfaces.**
  - Khanh, arXiv:2609.08428v1: unrefereed. Its statements were checked, and reviewer-2 read the proofs, but it
    has not been refereed.
  - Bartels–Farrell–Lück, Bartels–Reich, Bartels–Lück and Lück–Steimle, as quoted.
  - The part-4 simplicity argument is on paper, not in Lean.
  - `boone-higman-conjecture` is untouched.
- **Novelty.** The frontier artifact on main records no published positive-characteristic linear class, and the
  BBMZ list has no item for it. So this is a new class, not an answer to a posed question. It covers the finitely
  presented metabelian groups of Problem 5.3(7) that are linear in positive characteristic.
- **Cairn state (MSI, tip f5e532502).**
  - ESTABLISHED: `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`,
    `leavitt-tensor-powers-have-trivial-k-theory`, `prime-field-leavitt-tensor-powers-have-trivial-k-theory`,
    `leavitt-power-projective-elementary-groups-finitely-presented`, `char-two-linear-groups-satisfy-boone-higman`
    and `positive-char-linear-groups-satisfy-boone-higman`.
  - `boone-higman-conjecture` is OPEN.
  - The derivation tree of `positive-char-linear-groups-satisfy-boone-higman` bottoms out in citation nodes for
    Khanh, Ara–Cortiñas, the centre of `L`, Bartels–Farrell–Lück, Bartels–Reich and Bartels–Lück, and in the
    direct proofs of the crossed-product decomposition and the Hochschild dimension bound.

## 33. Guba's Question 1 (survey Question 3.20) and twisted binomials in K[F] (4f3e5243a, fd68ee7ab): PASS

Priority review, requested by the coordinator.

**Fidelity.** Checked against the arXiv:2201.02308 TeX source extracted on MSI (`eqgrring.tex`,
`\begin{que}\label{x1b}`), verbatim: "Let $R=K[F]$ be a group ring of $F$ over a field $K$. Is it true that for any
element $b\in R$, the equation $(1-x_1)u=bv$ has a non-zero solution in $R$?" The claim's quote agrees word for word.
- **Field.** `K` is arbitrary.
- **Side.** `1 - x_1` multiplies on the left, so the question asks for a common right multiple. `K[F]` is a domain,
  so for `b ≠ 0` a nonzero solution means exactly `(1 - x_1)R ∩ bR ≠ 0`.
- **Generators.** Guba's `x_i` come from `<x_0, x_1, … | x_j x_i = x_i x_(j+1), i < j>`, with
  `x_n = x_0^-(n-1) x_1 x_0^(n-1)`. His paper uses no PL model.
- **Status.** The abstract says "The corresponding fact for $1-x_1$ instead of $1-x_0$ remains open."

**Conventions.**
- **Which realization.** The CFP maps under right-to-left composition satisfy Guba's relations: the supports give
  `x_1^-1 x_2 x_1 = x_3`, and the lane's `pl_check.py` checks the rest.
- **Why the choice does not matter.** The argument uses only three kinds of fact: supports of elements, the
  subgroups `F_[p,1]`, and isomorphisms between those subgroups. Inversion leaves all three unchanged, so the proof
  holds for either composition convention.
- **Guba's automorphism.** `α : x_0 ↦ x_0^-1, x_1 ↦ x_1 x_0^-1` is used only for the mirror form.

**Proof of `thompson-f-one-minus-x1-is-ore-with-every-element`.**
- **Step 1.** `ψ_g = Ad(ρ)∘Ad(t)` maps `F_[p_g,1]` onto `F` and sends `g` to `x_0^(±1)`. On `[1/2,3/4]`,
  `ρ x_1 ρ^-1(s) = 2 x_1((s+1)/2) - 1 = s/2`. Guba's Theorem 2 transfers, and `(1 - x_0^-1)R = (1 - x_0)R`.
- **Step 2.** With `p_1 <= … <= p_m`, `R_(j+1) ⊆ R_j`. A nonzero `w` in the inner intersection lies in `R_j`. Guba
  at `g_j` gives `wz ≠ 0` in `(1 - g_j)R_j`, and right ideals absorb `z`.
- **Step 3.** `t(1 - t^-1 h t) = (1 - h)t` puts `bv` in `(1 - h)R`, and `bv ≠ 0` because `K[F]` is a domain.
- **The imported Theorem 2.** Checked against the TeX source: Theorem `x0b`, proved through Theorem `bphi`.
- **The lane's own proof of Theorem 2.** Its dimension count also checks. Inserting a letter into a normal form
  raises only the inserted index, by at most the length, and `(N+1)|A|` outgrows `(4^(D+1)/3)|A|`.

**`thompson-f-twisted-x0-binomial-is-ore-with-every-element` and `thompson-f-rescaled-x0-binomials-have-common-multiples`: PASS.**
- **Weighted coset test.** On a coset, `(x_0 - μ)R` becomes `(t - μ)K[t^(±1)]`. So membership is vanishing at
  `μ = -1/λ`, and `x_0^k y - μ^k y` lies in the ideal.
- **Families.**
  - Sort the bumps by right endpoint.
  - Conjugates of the next bump by elements supported in `[P_j, q_j]` fix `q_(j+1)`, so they share that right
    endpoint.
  - Lemma D nests them innermost first.
  - Lemma A: `K[F]` is free over `K[H]` on right coset representatives, so common multiples descend.
- **Members.** Under right-to-left composition, the support of `x_1 x_0^-1` was rechecked by hand: `(0, 3/4)`,
  identity on `[3/4, 1]`.
- **Item 5.**
  - A form with two nonzero coefficients is a unit times `1 + λg` with `g ∈ O_1`.
  - Over `F_2`, the only form with three nonzero coefficients is `x_0 + x_1 + x_2`. Equal forms can share one
    unknown, so (a) covers every system, and `Q_k` over `F_2` is settled.
  - Over other fields, systems with two distinct full trinomials stay open, as the node says.
- **b3c0966d2.** Already PASS in §23.

**Novelty (bounded).**
- The survey arXiv:2305.07113v4 (October 2023) still lists the question, so it was open then.
- Semantic Scholar lists two citing records of arXiv:2201.02308: that survey, and one titled "R. Thompson's group F
  and its group algebras", whose author and year were not returned. Semantic Scholar rate-limited this review
  (HTTP 429), so that record was not inspected. Priority should not be claimed until it has been read.
- Two arXiv searches found no such paper. A title search for "group F and its group algebras" returned nothing. An
  all-fields search for "Thompson's group F" together with "group algebras" returned three unrelated 2023–2024
  papers: Aiello 2405.17275, Krishnan 2309.05626, and Hong–Szymański 2303.10363. So that citing record is probably
  not on arXiv.
- The lane's arXiv title and abstract searches found no later answer. This review's arXiv API queries returned no
  entries, which settles nothing.

**Reading.**
- This answers a published question in the positive.
- It does not touch amenability of `F`. `C_+` and `O_1` contain only one-bump elements, and a non-Ore pair must
  avoid the product class of item 3 of the rescaled-binomial claim.

## 34. UCT permanence, central relative thresholds, relative PBH products and Sp(n,1) torsion (d2ed3c4b6, 45edbd4de, 36402f028, c48a38ab6)

### 34.1 `gardella-rokhlin-actions-preserve-uct` (d2ed3c4b6): PASS as a citation

- It agrees with Gardella, arXiv:1408.1946, Theorem 3.13: a Rokhlin action of a compact group on a separable simple
  nuclear UCT algebra has UCT fixed-point algebra and crossed product.
- The bridge between definitions (Hirshberg–Winter, Izumi, Barlak–Li Definition 2.6) is stated for finite groups and
  unital algebras, as needed.
- The "passes down, asks whether it passes up" reading is consistent with §29.5.
- The quote was not re-extracted here.

### 34.2 `fpbs-central-amenable-relative-threshold-is-pu` (45edbd4de): PASS

- **Monotonicity.** For `I <= J`, an `I`-infinite cluster is `J`-infinite, so `p_c(J;G) <= p_c(I;G)`.
- **`J = AC` is amenable and wq-normal.**
  - `J` is a quotient of `A × C`, so it is amenable.
  - Take any `J <= I′ < Γ` and `g ∉ I′`. Then `g I′ g^-1 ∩ I′ ⊇ C`, which is infinite.
  - This uses the intermediate-subgroup definition recorded in `fpbs-hp-wq-normal-uniqueness-transfer`.
- **Squeeze.** `p_u = p_c(J;G) <= p_c(A;G) <= p_u`. The last inequality is §27.11.
- **Reading.** Correctly scoped as an obstruction to a method: on central extensions, a relative gap along a
  subgroup is no easier than `p_c < p_u`.

### 34.3 `relative-pbh-closed-under-finite-direct-products` (36402f028): PASS

- **Type [A_2].**
  - `Stab_G(s) = Stab_(G_1)(s) × G_2` is finitely generated.
  - The four blocks of `S × S` have finitely many orbits.
  - The kernel is `K_1 × K_2`, because both `S_i` are nonempty.
- **Sharp embeddings and removability.** Both pass coordinatewise. The normal closure of `F_1 × 1` in
  `G_1′ × G_2′` is `K_1′ × 1`.
- **Route `bh-product-closure-via-a2-kernel-removal`.** It checks as a conditional:
  - `j(S_1×S_2) ∩ K′ = j((S_1×S_2) ∩ K) = 1`;
  - `G′/K′` is finitely presented and acts faithfully with type (A);
  - Zaremsky's Corollary B applies.
- `boone-higman-closed-under-finite-direct-products` is correctly OPEN.

### 34.4 Sp(n,1) torsion and pro-p kernels (c48a38ab6): four PASS, one correctly OPEN

- **`sp21-congruence-tower-p-torsion-grows-at-least-linearly`: PASS.**
  - For uniform `U`, `U_m = P_(m+1)(U)`, so `[U_m,U_m] <= P_(2m+2) = U_(2m+1)`. Then
    `|U_m^ab| >= |U_m : U_(2m+1)| = p^(D(m+1)) = p^D [Δ:Δ_m]`.
  - (T) makes `H_1(Δ_m;Z)` finite, with p-part `P_m^ab`, which maps onto `U_m^ab` with kernel the image of `N`.
- **`sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel`: PASS.**
  - If `d(Φ^i(P)) = D`, the map of Frattini quotients onto `U^(p^i)/U^(p^(i+1))` is an isomorphism, so
    `N ∩ Φ^i(P) ⊆ Φ^(i+1)(P)`.
  - Stabilization and `∩_i Φ^i(P) = 1`, valid for finitely generated pro-p groups, embed `N` in a finite quotient.
- **`sp21-gs-certificate-shape-at-uniform-levels`: PASS, with (iii) conditional on Lazard.**
  - (ii) The presentation complex has `χ = 1 - |X| + |R| = 1 - d + dim H^2(K;F_p)`, and `H^2(Δ) -> H^2(K)` is
    injective.
  - (iv) A lift `s : Δ -> E` whose image misses `F_p` would be a complement, forcing `c̄ = 0`. So `s` is onto and not
    congruence.
- **`sp21-pro-p-kernel-invisible-to-local-linear-reps`: PASS, conditional on (SR) and (V) in the residue-characteristic
  `p` case.**
  - Positive characteristic: finite images.
  - Residue characteristic `ℓ ≠ p`: a pro-p subgroup meets the open pro-ℓ congruence subgroup trivially, so the
    image is finite.
  - Residue characteristic `p`: Theorem A (review-backlog-2 §14) runs on the graph `P_2`. It uses only finite rank,
    density of `Δ` and the surjection `pr_1`, and `ker pr_1 ≅ ρ(N)`.
- **`kazhdan-group-with-golod-shafarevich-mod-p-cohomology`: correctly OPEN.** `dim H^2 >= d` from the Ext term, so a
  certificate needs `d > 4`.

## 35. The Leavitt pair and (H1), and rank rounding over fields (5c0603721, 9919a5637, 8a6eff4cc)

### 35.1 `leavitt-pair-vertex-rounding-is-nonhyperlinearity`: PASS; it corrects the scope of (H1)

- **Identification.** `GL_n(R) = EL_n(R)` and `M_k(R) ≅ R` identify both `Γ` and `G_L` with `Q = R^×`. `Q` is simple,
  infinite and not residually finite, so every finite-dimensional unitary representation is trivial.
- **3 ⟹ 1.** A trace-preserving `σ` is a hyperlinear embedding, so if `Q` is not hyperlinear, (H1) holds vacuously.
- **1 ⟹ 2.** Rounding representations are trivial, while `||σ(s) - 1||_2 = √2` for every `s ≠ 1` in the Kazhdan set.
- **Consequence for the chain.** `hs-stable-vertex-rounding-for-every-model`, read over every infranormal non-normal
  Kazhdan pair, already implies that `Q` is not hyperlinear. Consumers must instantiate (H1) at the Theorem E pair.
  The 9919a5637 note records exactly that. With §30, (H1) at the Theorem E pair is the one open existence input of the
  non-hyperlinear chain.
- `kun-thom-wreath-embeds-in-leavitt-unit-group` is correctly OPEN.

### 35.2 `kazhdan-rank-rounding-fails-over-every-field`: PASS

- **Invariant subspaces.** The matrix units `E_ij ⊗ x^k` generate `M_3(A)`, so the invariant subspaces are the
  `I^3` with `I = gA`.
- **Almost invariance.** `W = S_m^3` gains at most one dimension under each generator.
- **Distance.** With `e = deg g`, `dim(S_m ∩ gA) = max(0, m-e)`, so
  `d(W, I^3) = 3[m + N - e - 2max(0, m-e)] >= 3min(m, N-m)`.
- **Irreducibility.** Eisenstein makes `A` a field for `f = x^N - 2`.
- **Commutator bound.** The truncation projections commute with the generators up to rank 2.
- **Input.** Ershov–Jaikin-Zapirain supplies (T) for `EL_3(Z[t])`.
- **Reading.** Correctly scoped: property (T) gives no rank-metric rounding over any field, and what is missing is
  Hilbert structure.
- **The win–win pair.** `c-linear-sofic-groups-kill-rigid-compression-defects` and
  `c-linear-sofic-group-carries-nontrivial-rigid-defect` are correctly OPEN, and they refute each other. Exactly one
  of the routes `non-linear-sofic-via-c-rank-row-defect` (existence of a non-linear-sofic group) and
  `linear-sofic-nonsofic-via-c-rank-row-defect` (Arzhantseva–Paunescu Question 8.5) has a true prerequisite.

## 36. `birman-sequence-genus-three-does-not-virtually-split` (8a632b1e1, 53f80e1e6): Lemmas A–D PASS, Section 3 transfer PLAUSIBLE

**What is claimed.** An adaptation of Chen–Salter (arXiv:1804.11235v1, Theorem A, `g >= 4`) to genus 3, at the
level of the mapping class group. If true, it is a new theorem. The lane made no novelty search.

**Where Chen–Salter need `g >= 4`, checked against the PDF text extracted on MSI.** The explicit uses are exactly
(G1)–(G4) of the artifact:
- line 292/338: the Torelli centralizer `Z^(2g-3)` beats the bound 3;
- line 274: Lemma 2.9(2) needs both sides of genus `>= 2`;
- line 451: Lemma 2.16 needs the same;
- line 468: Section 3 needs a separating curve with `p, q >= 2`.

No other occurrence of a genus bound was found.

**The replacements check.**
- **Lemma A.**
  - Step 2 works at the mapping-class-group level. A pants decomposition through `a` and `b` gives `Z^6` of twist
    powers commuting with `x`, and `σ` is injective. An empty CRS forces a pseudo-Anosov with virtually cyclic
    centralizer. A CRS `{b′}` or `{b′,b″}` with a pseudo-Anosov on the genus-2 component has centralizer rank `<= 3`.
  - Step 3: McCarthy gives `ψ^j = φ^i` in `Mod(C̃)`. Forgetting `∗` gives `T_δ^(rj) = 1` in `Mod(S^)`, which is
    false, because `x^k` is a boundary multitwist of `S`.
- **Lemma B.** The same three steps work for a separating curve bounding a one-holed torus.
- **Lemma C.**
  - Both `T̃` and `R̃` miss `∗`, so (F) makes `ρ_(T̃)(σ(h))` trivial for `h` in the genus-2 disk-pushing group.
    `ρ_P` is trivial (thrice-punctured sphere). The cutting sequence gives `σ(D″) ⊆ Mod(R̃) × <T_(c_T)>`.
  - The central extension `D″` of a finite-index subgroup of `π_1(Σ_2)` has nonzero rational Euler class, since
    restriction is injective on `H^2(-;Q)`. The five-term sequence kills the centre in `H_1(D″;Q)`, so `ν` vanishes
    on it, against `ν(T_c^(kN)) ≠ 0`.
  - Only the genus-2 side is used, which is exactly why Chen–Salter's two-sided Lemma 2.15 is not needed.
- **Lemma D.** Commuting single lifts are disjoint. Nesting would make `c_1` and `c_2` isotopic after forgetting
  `∗`. So `∗` avoids one of the two tori.

**What was not verified line by line: Chen–Salter Section 3 with `p = 2` over `Mod` instead of Torelli.**
- A grep of the extracted text shows Section 3 using Torelli as the ambient group:
  - `I(Σ_(p,1,∗))` is defined as a full preimage;
  - the action `λ : I(Σ_(p,∗)) -> Aut(H)`;
  - diagram (6).
- The cohomological §3.4 works with rational cohomology of surface groups.
- The grep found no use of the trivial action of Torelli on homology. But the transfer of §§3.1–3.4 to finite-index
  subgroups of `Mod`, with `σ(Mod(R) ∩ L)` supported on `R̃` by Lemma D and (F), was not re-derived here.
- Chen–Salter's argument descends from Mess's 1990 preprint, which contained an error.

**Verdict.**
- Lemmas A–D and the replacement logic: PASS.
- Section 3 transfer: PLAUSIBLE, not verified.
- Before this is reported as a theorem, someone should check Chen–Salter §§3.1–3.4 line by line over `Mod`, and run
  a novelty search.
- `genus-three-mcg-has-no-covering-lift-to-marked-covers` inherits the same status.
- `closed-surface-mapping-class-groups-satisfy-boone-higman` stays OPEN either way.

## 37. Metabelian Boone–Higman, Problem 5.3(7) (38595d4da): eight PASS

- **`fg-metabelian-groups-embed-in-products-of-coprimary-quotients`: PASS.**
  - P. Hall makes `G′` a Noetherian `ZQ`-module. Lasker–Noether gives coprimary quotients.
  - `P_i ∩ Z` is `pZ`, giving exponent a power of `p`, or `0`, giving a torsion-free quotient.
  - Remeslennikov and Wehrfritz give linearity. Factors of equal characteristic merge by a block sum over a common
    field.
  - **Mixing is unavoidable.** A finitely generated soluble linear group in characteristic `p` has virtually
    unipotent derived subgroup, hence torsion, so `Z wr Z` is not linear there. A finitely generated linear group in
    characteristic 0 is virtually torsion-free, so `Z/p wr Z` is not linear there.
- **`function-field-soluble-groups-embed-in-fp-self-similar-groups`: PASS.**
  - Kolchin–Mal'cev triangularization over a finite extension `K′`, then `S`-integers with `|S| >= 3`.
  - `[[b,v],[0,λ]] ↦ (y ↦ λ^-1(by + v))` identifies `B_(n+1)(O_S)/O_S^×` with `A_S`.
  - Bux plus the finitely generated central `S`-units give finite presentation.
  - Zaremsky's Example 4.7 with `x` a nonzero nonunit of the Dedekind domain `O_S` (finite residue fields, Krull
    intersection) gives self-similarity.
- **`principal-ideal-affine-groups-are-self-similar` and `function-field-borel-groups-are-fp-for-three-places`: PASS as
  citations.** Both routine deductions check: mutual stability passes to subgroups because right scaling by `x`
  commutes with left matrix multiplication, and `B_n = B^SL_n ⋊ O_S^×`.
- **`rover-nekrashevych-groups-are-highly-transitive`: PASS.**
  - This is BFFHZ Remark 3.5.
  - The elementary check: cone counts are invariant mod `d-1`, and `c(P) = 1-k = c(P′)` lets the complements be
    matched.
  - A nontrivial normal subgroup is dense in `Sym(O)`: its closure is a closed normal subgroup of `Sym(O)`, and those
    are only `1` and `Sym(O)`.
- **`fp-simple-highly-transitive-groups-satisfy-pbh`: PASS as a citation** of BFFHZ Theorem C.
- **`fp-self-similar-subgroups-satisfy-permutational-boone-higman`: PASS.**
  - Zaremsky's envelope `[V_(d′)(G), V_(d′)(G)]` is highly transitive, so Theorem C (iii) ⟹ (i) applies to all its
    subgroups.
  - Part (b) is restriction of scalars into `Z[1/m]^N ⋊ GL_N(Z[1/m])`.
- **`global-field-soluble-linear-products-satisfy-boone-higman`: PASS.**
  - This is a combination of the above with closure of `B_A` under finite-index overgroups and products.
  - Instances: Baumslag's `B_p`, already covered by Kochloukova–Sidki with Zaremsky, and mixed products such as
    `B_2 × B_3 × BS(1,6)`, which are finitely presented metabelian groups covered by no earlier envelope.
  - A light but genuine set of new instances of Problem 5.3(7). No priority is claimed, correctly.
- **`fp-metabelian-groups-satisfy-boone-higman`: correctly OPEN.** The reduction to (P) is exact.
- **`baumslag-char-zero-metabelian-group-is-not-self-similar`: PASS.**
  - Step 0: a faithful state-closed action has trivial joint core.
  - Step 1:
    - an abelian subgroup meeting `R` lies in `R`, because `x` and `1+x` are multiplicatively independent;
    - normal subgroups meet `R` in nonzero ideals, because `Z[P] -> R` is onto;
    - finite-index restriction is birational (`x ∈ Q(x^m, (1+x)^m)`), which gives a conductor.
  - Step 2, case (a):
    - `g^m = x^a(1+x)^b`, and the only rational roots of unity are `±1`;
    - Mason–Stothers bounds `deg(-g) <= 1`, and the Möbius maps give `|Aut R| = 6`;
    - `λ ∈ R` by dividing out the primes of `N`, using that `R/pR` is a domain.
  - Step 3: `J = ∩_σ σ(J_1)` is a nonzero `Aut(R)`-stable ideal inside every `H_i`, mapped into itself by every `f_i`.
  - This is an obstruction to applying Zaremsky's Theorem 1.1 to `B` itself, and it excludes nothing else.

## 38. Leavitt cover residual finiteness, Kazhdan sectors, and Cartan subalgebras (b6b6b4058, 4f6f914eb, 2558a1877)

### 38.1 `acyclic-quotientless-extension-completion-is-kernel-completion` and `leavitt-kazhdan-cover-rf-iff-kernel-rf`: PASS

- **Splitting.**
  - `G -> Out(N/K)` has finite image and factors through `Q`, so it is trivial. So `C·(N/K) = G/K` and
    `C ∩ N/K = Z(N/K)`.
  - The central extension `1 -> Z -> C -> Q -> 1` splits because `H^2(Q; Z) = 0` for perfect `Q` with `H_2 Q = 0`.
  - `S = [C,C]` is characteristic, so `G/K = S × N/K`.
- **Finite quotients.** They are the `N/K`. Finitely many `G`-conjugates give admissible subgroups, since `N` is
  finitely generated.
- **Sharpness.** A perfect central extension by a finite quotient of `H_2 Q` shows the Schur multiplier hypothesis is
  needed.
- **Instance.**
  - `R^×` is integrally acyclic and infinite simple.
  - If `N` is residually finite, then `g ∈ R_f(G)` centralizes `N`, since `[g,N] ⊆ R_f(G) ∩ N = R_f(N) = 1`.
  - So `N` is cyclic, because centralizers in torsion-free hyperbolic groups are cyclic, and then `G` is virtually
    cyclic. That contradicts `G ↠ R^× ⊇ Z^2`.
- **Reading.** Correctly scoped: on this cover, Gromov's question is exactly residual finiteness of the kernel.

### 38.2 `kazhdan-kernel-isotypic-sectors-extend-within-kernel-closure`: PASS

- **Types are fixed.** Wang finiteness of `Irr_d(N)`. `Q` acts on a finite set, so trivially.
- **Inner outer part.** Schur splitting `π(g)|_(H_ρ) = U(g) ⊗ W(g)`. `Q -> N(K)/K` lands in a compact Lie group,
  hence in a finitely generated linear group, hence it is residually finite and so trivial.
- **Bounded multiplicity.** On a type I commutant `⊕_(k <= m) M_k(Z_k)`, evaluating at characters gives projective
  representations `Q -> PU(k)`, which are trivial. The ratio `λ_g(χ)/λ_g(χ′)` is a homomorphism `Q -> T`, also trivial.
- **Sharpness.** The examples (finite quotients; infinite multiplicity) check.

### 38.3 `bounded-multiplicity-kazhdan-sectors-miss-leavitt-cover-defect`: PASS, conditional on block invariance

- On `H_b` every `σ(g)` lies in the strong closure of `T·σ(N)`.
- Realizer sets `x M_s C_s` are invariant under conjugation by `σ(N)`, because `x` normalizes `M_s` and `C_s` commutes
  with `σ(Γ̂) ⊇ σ(N)`. So compressed and host twists have the same `S_b`.
- It depends on `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`, like §8. It is an obstruction to a
  method, correctly scoped, and the "what survives" paragraph names the unbounded-multiplicity sectors.

### 38.4 UCT and Cartan subalgebras (2558a1877): three PASS, one correctly OPEN

- **`li-simple-finite-nuclear-dimension-cartan-iff-uct`: PASS as a citation** of Li, arXiv:1802.01190, Corollary 1.4.
- **`uct-cartan-trivial-k-kirchberg-uct-iff-cartan`: PASS.**
  - With `K_* = 0` the UCT gives `KK(A,A) = 0`, and Kirchberg–Phillips gives `A ≅ O_2`.
  - `D_2 ⊆ O_2` is Cartan.
  - Barlak–Li: a Cartan subalgebra in a separable nuclear algebra gives the UCT.
- **`uct-cartan-nontrivial-m2-bundle-over-s4-has-no-cartan`: PASS.**
  - Conditional expectations onto masas of `M_2` are unique, and fibre dimension 2 is forced everywhere.
  - The masa field is continuous, so it gives a line subbundle of the `SO(3)`-bundle `V`.
  - On `S^4`, `H^1(S^4; Z/2) = H^2(S^4; Z) = 0` trivializes `L` and `L^⊥`, contradicting the nonzero clutching class.
  - `A ⊗ K ≅ C(S^4) ⊗ K`, because `H^3(S^4; Z) = 0`.
  - It is known (Li–Renault), and the masa-with-expectation strengthening is correctly credited as elementary.
- **`uct-cartan-trivial-k-kirchberg-without-cartan-exists`: correctly OPEN.** It is exactly the UCT problem in
  Kirchberg's test class.

## 39. Percolation thresholds, virtual sections of Aut(F_n) -> Out(F_n), and Toms–Winter division (17:27–17:41)

### 39.1 Percolation (1455b5b89, df535c054, 6c78684d0): six PASS, one correctly OPEN

- **`fpbs-expanding-factor-product-strict-thresholds`: PASS.** The chain checks:
  - `p_c(X) <= p_c(G) <= 1/(1+h)` (Benjamini–Schramm);
  - `||A_X|| <= ||A_G|| + d_K`;
  - walk counting gives `p_(2->2) >= 1/||A_X||`;
  - uniqueness bounds the two-point function below, which makes `T_p` unbounded above `p_u`.
- **`fpbs-mohar-adjacency-norm-cheeger-bound` and `fpbs-regular-tiling-edge-isoperimetric-constant`: PASS as citations.**
  They are Lyons–Peres Theorem 6.7 and Häggström–Jonasson–Lyons Theorem 4.1, and the normalization `Φ_E = h/d` checks.
- **`fpbs-surface-group-times-zk-product-sets-strict-thresholds`: PASS.**
  - `h² = 16g² - 16g` gives `||A_G|| <= 4√g`.
  - At `g = 3, k = 1`, `1 + √96 - 4√3 ≈ 3.87 > 2`.
  - For `k <= g-2` the criterion reduces to `(√g - 1)² > 0`.
  - At `g = 2` it fails.
  - New perturbative instances of strict thresholds on product generating sets of `Γ_g × Z^k`. No novelty is claimed,
    correctly.
- **`fpbs-generating-set-threshold-comparison`: PASS.**
  - Uniforms are indexed by uses, so `ξ` is Bernoulli(`φ(p)`) on `G′`.
  - Padding makes `ω` Bernoulli(`p`), because `∏(1 - c_j) >= (1-c)^M = 1-p`.
  - `ξ`-clusters nest in `ω`-clusters.
  - Hutchcroft–Pan transfers uniqueness.
  - The reading, that a gap transfers only with margin `(p_u/M)^L`, is correctly scoped.
- **`fpbs-generating-sets-connected-by-product-moves`: PASS.** Removal in decreasing word length always has both
  factors present, and neither factor is the removed element or its inverse (lengths differ).
  `fpbs-gap-survives-product-generator-moves` is correctly OPEN, and equivalent to Choi–Seo Question 1.2.
- **`fpbs-twisted-level-percolation-disconnected-at-low-density`: PASS, conditional on Osin Lemma 2.27 and relative
  hyperbolicity along `E(t)`.**
  - `E(t) = <t>` meets `N` trivially, and `m ↦ φ^-m(x)` is injective. So each edge has at most `2|S|` witnesses, a
    self-avoiding path needs `>= l/2` independent pairs, and a path is open with probability `<= (2|S|)^l δ^(l/2)`.
  - The `H`-components lie in the distinct cosets `s w_i^-1 H`, so they are isolated. Osin's bound then gives
    `l^1`-control of the exponents by `K(l+1)`.
  - The two-point sum is `< 1` for small `δ`, and ergodicity makes disconnection almost sure.
  - This correctly refutes `fpbs-twisted-level-percolation-connected` and invalidates the twisted-level route to fixed
    price. `fpbs-hyperbolic-3-manifold-groups-fixed-price-one` stays OPEN.
- **`osin-isolated-components-bounded-by-relative-area`: PASS as a citation.**

### 39.2 Virtual sections of `Aut(F_n) -> Out(F_n)` (67f49fd18): two PASS

- **`aut-out-free-abelianized-extension-splits-rationally`: PASS.**
  - The Fox Jacobian determinant is a crossed homomorphism.
  - For `ι_g`, `det(tI + uv^T) = t^(n-1)(t + v^T u) = t^(n-1)`, since `v^T u = 1 - t` by the fundamental formula. So
    `h(ι_g) = (n-1)[g]` and `(n-1)c = 0`.
  - Rows 0 and 1 of the Lyndon–Hochschild–Serre spectral sequence agree for `F_n` and `F_n^ab`, and `d_2` is cup
    product with `c`, which vanishes rationally.
  - The reading is correct: no rational cohomological argument with coefficients pulled back from `Out(F_n)` excludes
    a virtual section.
- **`free-splitting-fa-lifts-choose-a-side`: PASS.**
  - `π^-1(J_B)` acts on the Bass–Serre tree of `<p> * B` without inversions.
  - FA gives a fixed vertex. A fixed `<p>`-vertex plus finite abelianization gives (S), and otherwise the fixed tree is
    one `B`-vertex, which is (N).
  - The hypothesis holds for `n >= 5` through property (T) of `Aut(F_(n-1))`.
  - `out-free-groups-virtually-embed-in-aut-free-groups` stays OPEN.

### 39.3 Toms–Winter: tracial support projections and division (ce56c9923): two PASS, three correctly OPEN

- **`ultrapower-comparison-with-rank-density-divides-projections`: PASS.**
  - RD_b gives `e′` with `σ(e′) = σ(p)/n`.
  - PC places `n - 1` orthogonal copies of `e′` under `p`.
  - The remainder has the profile of `e′`. It differs from a copy by a projection that vanishes on every limit trace,
    and such a projection is zero in the uniform tracial ultrapower. Matrix units follow.
- **`uniform-gamma-iff-tracial-support-projections-and-division`: PASS, conditional on CETW Theorem 4.6 and Vaccaro
  arXiv:2604.24682v2 Proposition 1.6.**
  - Lemma A identifies TSP with `γ_A(a) = 0` through diagonal sequences.
  - (b) lifts divided support projections to tracial almost divisibility.
  - The imports were read by the lane and not re-extracted here.
- **`comparison-forces-tracial-support-projections`, `tracial-comparison-gives-gamma-on-lfnd-rank-density-locus` and
  `gamma-failure-invisible-to-projection-comparison`: correctly OPEN.** Their equivalence wiring checks.

## 40. A retraction, virtual sections, the margin class, and the earlier landings (17:41–21:15)

Tip at writing: 82a4dbf6c.
- **Scope.** Unchanged: ESTABLISHED claims from `01PWzwKNBr2dwjX4pucBuXff` lanes.
- **Out of scope.** Landings since c0ffe2f06 from sessions `01UM7` (swarm 7) and `012d8`. One of them sits on the
  non-hyperlinear chain and is checked in passing in 40.5.

### 40.1 Retraction: `free-splitting-fa-lifts-choose-a-side` FAILS as stated, and the §39.2 PASS is withdrawn

- **Counterexamples.** §39.2 passed this claim, which was wrong on scope. `review-swarm6-groups-2026-09-12.md` §2
  (b09aa6e6e) refutes "exactly one of (S), (N)" twice:
  - `Γ = 1`;
  - `Γ = ⟨[id ∗ β]⟩ ≅ Z/2`, with `β` swapping `b_1, b_2`.
- **The Z/2 example, rechecked.** `id ∗ β` fixes `pB`, `⟨p⟩`, `1B` and `b_3⟨p⟩`, joined by the edges `p`, `1`, `b_3`.
  So the fixed tree contains a path of length 3, and it is neither a star nor a vertex.
- **The missing hypothesis.**
  - §39.2 read step 4 of the route ("for all `β` in a finite-index subgroup of `Aut(B)`") as automatic. It needs
    `[J_B : Λ] < ∞`.
  - With that hypothesis the route is correct, and the node's downstream use (finite-index `Γ`, `n >= 5`) satisfies it.
- **The node is not yet corrected.**
  - At 82a4dbf6c the Setting still says "Assume `Λ` has property FA and finite abelianization", with no finite-index
    condition.
  - This is despite b09aa6e6e §2 saying the Setting "now requires" one.
  - A reviewer lane is narrowing that Setting, so this lane does not touch the node, to avoid a same-path collision.

### 40.2 `free-splitting-compatible-aut-lifts-are-virtual-sections` (0b1b22a2c): PASS

- **Adjacency.**
  - Let `u, v` be the vertices stabilized by `φ(A)` and `φ(C)`.
  - Edge stabilizers are trivial. So a nontrivial element of `G_u` sends the branch at `u` containing `v` into the other
    branches at `u`, and symmetrically for `G_v`.
  - An alternating word therefore moves an interior vertex `w` of `[u,v]`, and `⟨G_u, G_v⟩ ∩ G_w = 1`. But
    `⟨G_u, G_v⟩ = φ(G) = G` and `G_w ≠ 1`.
- **Well-definedness.**
  - Both factors are nontrivial, so `N_G(A) = A` and `N_G(C) = C`, and a vertex is determined by its stabilizer.
  - `A ∩ C = 1`, so the joining edge `e_φ` is a unique group element.
  - `φψ(A)` and `φψ(C)` are conjugated by `φ(e_ψ)e_φ`, which gives `e_(φψ) = φ(e_ψ)e_φ`.
- **Normalization and the `C`-vertex section.**
  - `b′ = g^{-1}ρ(γ)(g)b` and `ι_(b′)^{-1}ρ′(γ)|_A = ι_b^{-1}ρ(γ)|_A` were recomputed by substitution.
  - `λ(γ)λ(δ) = ι_(ρ(γ)(e_δ)e_γ)^{-1}ρ(γδ)|_A = λ(γδ)`.
  - `λ(γ)(A) = A` because `ρ(γ)(A) = e_γAe_γ^{-1}`.
- **(c), (d) and the consequence.**
  - A type-preserving action has no inversions, so FA gives a fixed vertex.
  - In (d), `a_γA` is canonical because `N_G(A) = A`, and a point stabilizer of a finite orbit has finite index.
  - (T) for `Aut(F_n)`, `n >= 4`, passes to `Out(F_n)` and its finite-index subgroups, and (T) gives FA.
- **Bullet 6 of `out-free-groups-virtually-embed-in-aut-free-groups`.**
  - `β ↦ [β ∗ id_⟨t⟩]` is injective. An inner representative fixing `t` is `ι_(t^k)`, which preserves `F_m` only for
    `k = 0`.
  - The atoroidal remark holds: a periodic class of a lift to a finite-index subgroup is periodic in `F_n`.
  - Carette arXiv:1301.4446 Corollary 3.2 was not re-extracted. The node stays OPEN.

### 40.3 Benjamini–Schramm margin class (04acd6e6a, artifact only): PASS

The artifact is `research/artifacts/fpbs-single-product-move-2026-09-12.md`. Its Cairn nodes are not on main yet.
- **Criterion.**
  - Lemma 3.2, `p_u >= 1/||A_S||`, is walk counting plus Harris–FKG under uniqueness.
  - Lemma 3.3 is `<A_S 1_F, 1_F> = d|F| − |∂_E F|`.
- **Moves.**
  - Add gains `R(t) + R(t^{-1})`, of norm at most 2, and boundaries only grow.
  - Remove lowers `A_S` entrywise (Lemma 4.1) and loses at most `2|F|` boundary edges.
  - So one move lowers the margin by at most 2. A Nielsen replacement `s ↦ st` is two moves.
- **Reach.**
  - `ρ(S_0)^2 = ||m(S_0)^2|| >= τ(m(S_0)^2) = 1/|S_0|` gives `|S_0| > ε^{-2}`.
  - Then `m(S) >= |S_0|(1 − 2ε) − 2`.
  - The remark `ρ(S) <= 2ε` needs `1 + 2ε <= ε|S_0|`, which holds.
- **Calibration, recomputed.** `F_5` gives 3; `F_4` gives `7 − 2√7 ≈ 1.71`; `F_3` gives `5 − 2√5 ≈ 0.53`; `F_2` gives
  `3 − 2√3 < 0`.
- **Theorem 6.1.**
  - The equivalence with the goal uses `fpbs-hp-relative-burton-keane` and
    `fpbs-generating-sets-connected-by-product-moves` (§39.1 PASS).
  - The Thom arXiv:1306.1767v1 Theorem 1 quote was not re-extracted.
- **Stale node.**
  - `fpbs-simple-generating-set-with-gap-exists` (OPEN) calls small spectral radius for simple generating sets of every
    nonamenable group open.
  - If the Thom quote is accurate, Proposition 5.1 answers that, and Proposition 3.4 then proves the node.
  - Not edited here, because the product-move lane is landing adjacent nodes.
  - Review `fpbs-spectral-margin-survives-product-generator-moves` and `fpbs-large-margin-generating-sets-exist` when
    they land.

### 40.4 Landings reviewed before the break

- **`el3-of-infinite-rank-rings-not-linear-over-number-fields`: PASS.**
  - Distortion forces virtually unipotent images, and Kronecker's theorem applies.
  - The logarithm then maps into a finite-dimensional `Q`-space, contradicting infinite additive rank.
- **`el3-z-t-embeds-in-no-host-with-number-field-local-groups` (2bc488e31): PASS, conditional on
  `fw-subgroups-of-eventually-similar-groups-virtually-embed` and `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`.**
  (T) gives FW, the FW subgroup virtually embeds in a product of local vertex groups, and the previous claim excludes
  number-field local groups.
- **`elementary-groups-over-fg-rings-have-property-t` (2bc488e31): PASS as a citation.** Ershov–Jaikin-Zapirain:
  `EL_n(R)` has (T) for `n >= 3` and finitely generated `R`.
- **`gardam-support-pair-has-no-rational-units` (928464921): PASS, computational.**
  - Singular `slimgb` over `Q` gives the elimination ideal `⟨u_7^4 + 1, u_10^4 + 1⟩`.
  - `x^4 = −1` has no real root, and no 2-adic root because `−1` is not a square in `Q_2`.
  - The z3 subset step has no certificate.
- **Jones index.**
  - **The original (939a37611, eb8fd6e76) FAILED.** It presented the gap below 2 as content. The Pimsner–Popa free gap
    `Ind(E) ∈ {1} ∪ [2, ∞]` is automatic:
    - take `h = a − E(a)`, scaled and signed so that `1 ∈ spec h ⊂ [−1, 1]`;
    - then `y = 1 + h >= 0` has `E(y) = 1`, and `1 ∈ spec h` forces `λ <= 1/2`.
  - **The correction (a2cb567b8, 74268da31, 799a3611d, 0afa68066) PASSES.**
    - `jones-index-blind-on-unbounded-defect-sector` now says the gap is automatic and that a bound below 2 is the
      defect statement itself.
    - The lane corrected claim, proof, artifact and hub at 20:43, so no separate
      `pimsner-popa-index-below-two-is-trivial` node was written.
    - `relative-normalization-modulo-kazhdan-kernel` stays OPEN.
- **`strict-comparison-with-rank-density-gives-support-projections`: PASS.** The estimate
  `|d_τ((q − 1/2)_+) − τ(q)| <= 2τ(q − q^2)` holds pointwise on the spectrum, since `|1_(t > 1/2) − t| <= 2t(1 − t)`
  on `[0,1]`.
- **`toms-winter-holds-on-tlfnd-rank-density-locus`: PASS, subsumed by known results; forward edit in this commit.**
  - Strict comparison and RD_b make the rank map surjective. Edwards writes `f` as an increasing sup of continuous affine
    `f_n`, and RD_b in `M_(k_n)(A)` gives near projections whose ranks are within `3η_n` of `f_n`.
  - So Lin (arXiv:2301.09250v2, Theorem 1.1) gives stable rank one, Vaccaro (arXiv:2604.24682) gives uniform Gamma, and
    CETW Theorem A gives Z-stability.
  - The node's Scope now records this and asserts no novelty.
  - The Lin and Vaccaro statements were taken from the graph's citation nodes and not re-extracted.
- **`comparison-forces-tracial-support-projections`: correctly OPEN.** It is a frontier hole that feeds only
  `lfnd-locus-gamma-via-support-projections`.
- **`fpbs-line-independent-twisted-levels-disconnected`: PASS, conditional on Osin Theorem 2.27**
  (`osin-isolated-components-bounded-by-relative-area`).
  - Witness injectivity gives at least `l/2` distinct rows, so a witness of length `l` has probability at most
    `δ^(l/2)`.
  - The 0–1 law holds because the `N`-action on the i.i.d. rows is mixing, hence ergodic.
  - `fpbs-cross-line-correlated-transport-set-generates` is correctly OPEN.

### 40.5 In passing: `theorem-e-congruence-projections-vanish-at-regular-trace` (1d9a1ceda, session `01UM7`)

Items 1, 2 and 4 check. Item 3 was checked in outline only.
1. For `m` distinct `k_i ∈ K`, put `X = Σ_i σ(k_i)` and `T = X^*X/m`. Then `τ(T) = 1` and `Tp = mp`, so
   `τ(p) <= 1/m`.
2. The moments of `Σ_s Re σ(s)/|S|` equal those of `λ_Γ`, whose spectrum lies below `1 − κ^2/(2|S|)`.
   - An `ε`-almost invariant subspace forces eigenvalues `>= 1 − ε^2/2`.
   - For `ε < κ/√|S|` the closed interval `[1 − ε^2/2, 1]` has `λ_Γ`-spectral measure 0, so portmanteau gives
     `lim_U dim/n = 0`.
4. For words in `F`, `|tr π_n(g) − tr σ_n(g)| <= ||π_n(g) − σ_n(g)||_2`. A Kazhdan set generates the group, so
   `tr π_n(g) → δ_e(g)` for every `g`.

`c6067895f` (session `01PWzw`) only adds an Attempts bullet to `hs-stable-vertex-rounding-for-every-model`, which is
correctly OPEN.

### 40.6 Graph queries (`cairn why` at 7397fc447, on MSI; route lists rechecked at 0a977f4e8)

- **`jones-index-blind-on-unbounded-defect-sector`:** ESTABLISHED, with a complete derivation.
- **`relative-normalization-modulo-kazhdan-kernel`: an OPEN frontier hole.**
  - Both routes are dead by invalidation: `component-space-sizes-miss-leavitt-cover-defect` and
    `conjugation-invariant-sizes-miss-relative-defect`.
  - **Cascade.** If established, it reaches `nonsofic-hyperbolic-group` through three steps:
    1. `relative-defect-via-relative-normalization`, with `relative-defect-normalization-dichotomy`, gives
       `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`.
    2. `nonsofic-hyperbolic-via-relative-rigid-defect` also needs
       `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`.
    3. The count of further consumers is not rechecked here.
  - The cascade to `hyperbolic-groups-virtually-torsion-free` has the right sign, because that root is a decision
    question closed by `hyperbolic-vtf-decided-by-counterexample`.
- **`nonsofic-hyperbolic-group`: OPEN.**
  - Five routes target it. `nonsofic-hyperbolic-via-kun-thom-centralizer` is marked dead by
    `kun-thom-centralizer-normality-automatic-in-hyperbolic`.
  - Four are open: cocycle stability, the Cheeger threshold, HS-stable Kazhdan hyperbolic groups, and the relative
    rigid defect.
  - An earlier draft of this section said three.
- **`toms-winter-holds-on-tlfnd-rank-density-locus`:** ESTABLISHED. Its route has five `requires:`, and the query
  reported all of them established.
  `stw99-problem-xviii-toms-winter-conjecture` is OPEN only through `stw99-xxvi-xxvii-imply-xviii`, and the locus claim
  does not feed it.
- **`fpbs-hyperbolic-3-manifold-groups-fixed-price-one`:** OPEN.
  - The correlated-transport route waits only on `fpbs-cross-line-correlated-transport-set-generates`.
  - The normal-subgroup route waits on `fpbs-normal-subgroup-bounded-cost-fixed-price-one`.
- **`fpbs-twisted-level-percolation-connected`:** REFUTED by `fpbs-twisted-level-percolation-disconnected-at-low-density`.
- **Warnings.** Each query printed 10–12 graph warnings. They belong to the steward's `cairn check` and were not
  investigated here.

## 41. `sl3z-atiyah-denominator-24` (3d4faea64, attempts in 5f0b48758, session `01UM7`)

Nodes read at 0a977f4e8:
- `sl3z-strong-atiyah-iff-discrete-iwahori-denominator-8` and its route `sl3z-strong-atiyah-iwahori-denominator-8-proof`;
- `sl3-zp-open-subgroup-lcm-index-bounds-for-strong-atiyah` and its route `sl3-zp-open-subgroup-lcm-index-bounds-proof`;
- Attempts 4–6 of `sl3z-satisfies-strong-atiyah`.

Linnell–Schick (arXiv:math/0403229v5) pages 1–10 were read from the PDF. Notation: `G = SL_3(Z)`.

### 41.1 `sl3z-strong-atiyah-iff-discrete-iwahori-denominator-8`: PASS, conditional on `p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`

The import is swarm 5 §9b (conclusion correct). Its use here is in scope. `Gamma(3)` and `Gamma(4)` have closures
`I + 3M_3(Z_3)` and `I + 4M_3(Z_2)`, which are torsion-free, so every subgroup of either has integer ranks.

- **Index 21.** `G -> SL_3(F_2)` is onto, `|SL_3(F_2)| = 7 * 6 * 4 = 168`, and `|U| = 8`.
- **Finite subgroups of `K_I`.**
  - Minkowski: finite `F <= GL_3(Q)` has order dividing 48. For `F <= G`, `-I` has determinant `-1`, so
    `F x {+-I} <= GL_3(Z)` and `|F|` divides 24.
  - An element of order 3 in `K_I` maps to 1 in `U`, so it is `I + 2X`. Its square `I + 4(X + X^2)` is then a nontrivial
    torsion element of `Gamma(4)`. By Cauchy the finite subgroups are 2-groups, of order dividing 8.
  - `D_8 = <r, s>` checks on `e_1, e_2, e_3`: `r` has order 4, `s = diag(1,-1,-1)`, and `srs = r^(-1)`.
  - Reduction mod 2 is not injective on `D_8`, since `r^2`, `s` and `sr^2` are sign matrices. The image is still a
    2-group, so the conjugation argument applies, and `lcm(K_I) = 8`.
- **Item 2.**
  - `Gamma(2) <= K_I` maps onto `SL_3(F_3)` through `SL_3(Z/6) = SL_3(F_2) x SL_3(F_3)`, so
    `[K_I : K_I cap Gamma(3)] = 5616`.
  - `[K_I : Gamma(4)] = 43008/21 = 2048`, with `|SL_3(Z/4)| = 168 * 2^8`.
  - `gcd(5616, 2048) = 16`.
- **Rank transfer, and the direction of the denominators.**
  - Restriction to a finite-index `H` divides by the index, `rk_G(A) = rk_H(res A)/[G:H]`. It multiplies denominators.
  - Induction from any `H` keeps ranks, `rk_G(B) = rk_H(B)` for `B` over `C[H]`. It carries denominators across unchanged.
  - The forward implication uses induction: `rk_{K_I}(B) = rk_G(B) in (1/24)Z cap (1/16)Z = (1/8)Z`.
  - The converse uses restriction twice: `(1/168)Z cap (1/5616)Z = (1/24)Z`.
  - Both use `(1/a)Z cap (1/b)Z = (1/gcd(a,b))Z`. Each transfer is used in the right direction.
- **`K''`.**
  - `[G : K''] = 5616/16 = 351` and `[K'' : Gamma(3)] = 16`.
  - `Gamma(3)` is torsion-free, so finite subgroups inject into a group of order 16, and `D_8` injects mod 3.
  - Converse: `gcd(8 * 351, 43008) = gcd(2^3 3^3 13, 2^11 3 7) = 24`.
- **"No finite-index subgroup does better" is proved, not asserted.** The route's Sharpness paragraph is a proof.
  - `D_8` acts on `G/H`. Stabilizers are 2-subgroups of conjugates of `H`, of order dividing `2^b` with
    `b = v_2(lcm H)`, so every orbit has size divisible by `2^(3-b)`.
  - Hence `v_2(lcm H) + v_2([G:H]) >= 3` for every finite-index `H`.
  - Any gcd of denominators `lcm(H_i)[G:H_i]` therefore has 2-part at least 8, which is the 2-part of 24.
  - This is unconditional. Under Strong Atiyah for `G` it also follows from the projection `(1/8) sum_{d in D_8} d`, of
    rank `1/8`.
- **Scope of the Linnell–Schick Lemma 2.4 citation.**
  - The lemma (pages 6–7) needs `H` normal of finite index with `lcm(H) < infinity`, and the rank condition with a factor
    `L` for the preimages of all Sylow subgroups of `G/H`.
  - Here `H = Gamma(4)`, `lcm(H) = 1`, `L = 1`, and `G/H = SL_3(Z/4)` has order `2^11 3 7`.
  - The Sylow 2-preimage is `K_I`.
  - The Sylow 3-preimage `P_3` has ranks in `(1/3)Z`, from `Gamma(4)` at index 3, and `lcm(P_3) = 3`.
  - The Sylow 7-preimage `P_7` has ranks in `(1/7)Z cap (1/5616)Z = Z`, from `Gamma(4)` and `Gamma(3)`, and `lcm(P_7) = 1`.
  - So the lemma gives exactly the converse implication. The forward implication is induction, and the lemma is not cited
    for it.
  - The route's gcd proof is self-contained. The citation is attribution, and it matches the source.
- **Nits (wording, no status change).**
  - "The preimages of the Sylow 3- and 7-subgroups already have ranks in `(1/3)Z` and `Z`, by the index bound against
    `Gamma(3)`." In fact `(1/3)Z` comes from `Gamma(4)` at index 3, and `Z` needs `Gamma(4)` at index 7 together with
    `Gamma(3)`.
  - "Strong Atiyah for `H` gives `SL_3(Z)` only the denominator `lcm(H) [G:H]`" describes what restriction yields. What is
    proved is the valuation inequality.
- **Subsumption scan.** No other node at the tip establishes the `K_I` or `K''` equivalence.
  - `strong-atiyah-kazhdan-groups-2026-09-12.md` records only the odd-prime bound and the index-168 reduction.
  - `sl3z-strong-atiyah-via-iwahori-index-8` is the refuted torsion-free version.
  - The converse direction is Lemma 2.4, and the route credits it.
- **Display check.**
  - Both claims display ESTABLISHED by their routes.
  - The required nodes display ESTABLISHED: `p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah` as a literature
    import, and `sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48` by its route.

### 41.2 `sl3-zp-open-subgroup-lcm-index-bounds-for-strong-atiyah`: PASS; the consequence is conditional on the index-48 claim

- **Item 1.**
  - `v_2(p^3 (p^2 - 1)(p^3 - 1)) >= 3 + 1` for odd `p`.
  - The Sylow 2-subgroup lifts, because the reduction kernel is pro-`p` (profinite Schur–Zassenhaus).
  - The stabilizers of `P` on `SL_3(Z_p)/W` are 2-subgroups of conjugates of `W`, of order dividing `2^b`. So
    `v_2(n) >= a - b`.
- **Item 2, rechecked step by step.**
  - Irreducible `Q_2`-summands have 2-power dimension, so `Q_2^3` splits as `1+1+1` or `2+1`.
  - In the `1+1+1` case the signs give `|P| <= 4`. The `2+1` case embeds `P` in `GL_2(Q_2)`.
  - An abelian `C <= GL_2(Q_2)` has `|C| <= 4`, since `[Q_2(zeta_8) : Q_2] = 4`.
  - A non-abelian `P` is absolutely irreducible, with `Z(P) <= {+-1}` scalar.
  - The image of `P` in `PGL_2(C)` is cyclic or dihedral, and the preimage of the cyclic part is abelian. So `|P| <= 8`.
  - `I` is pro-2 and contains a conjugate of `D_8`, so `lcm(I) = 8` and `[SL_3(Z_2) : I] = 21`.
- **Consequence.**
  - The density bijection `SL_3(Z)/H -> SL_3(Z_p)/W`, then restriction and induction, give `rk in (1/(lcm(W) n))Z`.
  - Odd primes give a 2-part of at least 16.
  - Torsion-free 2-adic inputs give 48, by `sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48`. That is swarm
    5 §10, a PASS with the GAP enumeration trusted; it was not rerun here.
  - `W = I` gives `gcd(168, 5616) = 24`.
- **Nit (wiring).**
  - The route uses the rank transfers and `D_8 <= K_I` from `sl3z-strong-atiyah-iwahori-denominator-8-proof`.
  - The claim cites `sl3z-strong-atiyah-iff-discrete-iwahori-denominator-8`.
  - Neither is in `requires:`. The status is unaffected while those nodes stand.

### 41.3 `sl3z-satisfies-strong-atiyah` (5f0b48758): correctly OPEN, and the Attempts 4–6 citations match

- **Attempt 4.**
  - **Theorem 1.6, Proposition 2.6 and Corollary 2.7.** The account matches the source: an elementary amenable quotient
    `A`, and SAC for the preimages `H_E` of the finite `E <= A`. Property (T) makes `A` finite, and `E = A` gives
    `H_E = G`.
  - **Theorem 4.1 (pages 9–10).** It needs `H` with finite `BH`, `chi(H) = +-1`, SAC for `KH`, and `1 -> H -> G -> Q -> 1`
    with `Q` elementary amenable and `lcm(G) < infinity`. The node's account matches, and `chi(H) = [G:H] zeta(-1) zeta(-2)
    = 0` by Harder.
  - **Definition 4.3 (page 10).** Cohomological completeness matches. The failure argument checks. `Z/p`-acyclicity for
    every `p` forces `chi = 1`. A nontrivial `Hhat^p` is finite, or 8-dimensional `p`-adic analytic, so its mod-`p`
    cohomological dimension is infinite or 8, against `cd H = 3`.
  - **Not read.** Theorem 4.60 lies beyond page 10. The node uses only the cohomological-completeness hypothesis, which
    Theorem 1.7 in the introduction states.
- **Attempt 5.** Farkas–Linnell Theorems 1.1–1.3 and 6.1 were not re-read. The zero-divisor argument
  `(1 - g)(1 + g + ... + g^(n-1)) = 0` is correct.
- **Attempt 6.**
  - The inputs are Lemma 2.3, with `H = Gamma(4)`, `L = 1` and `D(Gamma(4))` a division ring, and Proposition 2.2.
  - Together they give `D(K_I)` semisimple Artinian, and `16 tr(e) in Z` from item 2, as the node says.
- **Status.** Nothing at the tip proves `8 rk_{K_I}(B) in Z`, so OPEN is correct. The crossed-product reformulation and
  the discrete-Iwahori sufficient condition are recorded as attempts, not as claims.
