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
- **Source.** arXiv:1711.02590, checked 2026-09-12 against the ar5iv HTML rendering through WebFetch, because
  the MSI auth breaker blocked a TeX extraction. Both quotes agree word for word with the TeX quotes in
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
  graphs are "outside" Hutchcroft's theorem. What is known is only that they are not known to be covered,
  as its own Attempts say.
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
