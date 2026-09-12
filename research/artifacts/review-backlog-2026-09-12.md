# Review backlog, 2026-09-12

Lane `review-backlog`. Adversarial review of ESTABLISHED claims landed since about 12:00 without an
independent verdict, taken in order of consequence: first the routes into `non-hyperlinear-group`,
`nonsofic-hyperbolic-group`, Boone–Higman, p_c < p_u and Strong Atiyah, then the rest. Claims already
covered by `review-swarm2-2026-09-12.md`, `review-bh-swarm-2026-09-12.md`,
`review-major-swarm-2026-09-12.md` and `review-reviewer2-queue-2026-09-12.md` are skipped.

Verdicts: PASS (the proof holds as written, up to stated trust surfaces), GAP (a step is asserted but not
proved, and the conclusion is not known false), FAIL (a step or the conclusion is false).

## 1. `compressor-transport-exactifies-under-vertex-rounding` (2eda8abf6): PASS

Checked item by item against `compressor-transport-exactifies-proof`.

- **Defect.** `σ(A)σ(s)σ(A)^(-1) = σ(AsA^(-1))`, and `AsA^(-1)` is a fixed element of `Λ ⊆ Γ`, hence a fixed
  word in `F_Γ`. A homomorphism `π_n` rounding an asymptotic homomorphism on generators rounds it on any
  fixed word, with error at most word length times the generator error. So `δ_n → 0`.
- **Kazhdan step.** For the representation `Φ(γ)X = ρ_n(γ)Xπ_n(γ)^*` on `(M_(n'), ||·||_2)`, the vector
  `X − EX` is orthogonal to the invariants and has the same displacements as `X`. So
  `||X − EX||_2 <= κ^(-1) max_s ||Φ(s)X − X||_2`, and `||Φ(s)U − U||_2 = ||ρ_n(s)U − Uπ_n(s)||_2` is the
  defect. Property (T) of `EL_r(F_q[x_1..x_d])`, `r >= 3`, is Ershov–Jaikin-Zapirain.
- **Contraction.** `π_n` and `ρ_n = π_n ∘ Ad A` factor through finite groups, so `E` is a finite average of
  maps `X ↦ ρ(γ)Xπ(γ)^*`. So `||T||_op <= 1`, where `T = E(U_n)`.
- **Support.** `1 − T^*T = U^*(U − T) + (U − T)^*T`, so `||1 − T^*T||_2 <= 2δ_n/κ`. On `1 − Q` the operator
  `T^*T` vanishes, so `τ(1 − Q) = ||(1 − T^*T)(1 − Q)||_2^2 <= 4δ_n^2/κ^2`.
- **Invariance and polar part.** `Tπ(γ) = ρ(γ)T` gives `T^*ρ(γ) = π(γ)T^*`, hence `T^*T ∈ π(Γ)'`. So
  `Q ∈ π(Γ)'`, `W = T|T|^(-1)` intertwines on `Q`, and ranks agree in finite dimension.
- **Spectral measures.** `ρ_n|e_12` has spectral measure `(D_A)_*μ_n`. For a spectral projection `P_E`
  commuting with `Q`, `μ_n(E) = τ(P_E Q) + τ(P_E(1 − Q))` with the second term in `[0, τ(1 − Q)]`. The same
  holds for `ρ` and `Q'`, and the first terms agree through `W`. So
  `|μ_n(E) − μ_n(D_A^(-1)E)| <= τ(1 − Q)`.

Bookkeeping, no effect on the conclusion: `σ_n(A)` lives in `M_n` and `π_n` on `C^(n')` with
`n'/n → 1`. The unitary representative must be taken in `U(n')`, as (H1) allows.

## 2. `nonunit-projection-bounded-by-root-spectral-mass` (2eda8abf6): PASS

- **Product splitting.** `St_r(A_u × A_nu) = St_r(A_u) × St_r(A_nu)` for `r >= 3`. I re-derived the one
  non-obvious relation: `x_ij((a,0))` commutes with `x_ji((0,b))`, because `x_ji((0,b)) = [x_jk((0,b)), x_ki((0,1))]`
  and `x_ij((a,0))` commutes with both factors by the Steinberg relations, since `(a,0)(0,b) = 0`.
- **Fixed space.** Irreducibles of a direct product are tensor products, so a constituent is trivial on the
  normal factor or has no invariant vector there. Hence `range P = ∩_(i≠j) Fix(x_ij(A_nu))`.
- **Weyl symmetry.** Conjugation preserves fixed-space dimension.
- **Count.** Codimensions of an intersection are subadditive.
- **Both directions.** `range P ⊆ Fix(e_12(A_nu))` also gives the reverse inequality
  `μ(χ|A_nu ≠ 1) <= τ(1 − P)`. So the "equivalent" in the Reading is correct: `τ(1 − P) → 0` iff the
  non-unit root mass `→ 0`.

## 3. `pure-nonunit-root-mass-is-log-scale-folner` (2eda8abf6): PASS

- **Item 1.** In `B_n = A_u × A_nu`, `z = x_1⋯x_d` is a unit on `A_u` and lies in the maximal ideal of every
  factor of `A_nu`, hence is nilpotent there. So `z^k B_n = A_u × z^k A_nu`, and a finite depth means
  triviality on `A_u`.
- **Item 2.** `φ_A(z) = x^(A·1)`, where every coordinate of `A·1` is at least `d` because all entries of `A`
  are `>= 1`. So `φ_A(z^k R_+) ⊆ z^(dk) R_+`, and triviality on `z^m R_+` transfers to `χ ∘ φ_A` once
  `dk >= m`.
- **Item 3.** `D_A^(-1){depth <= d^j} ⊇ {depth <= d^(j+1)}` by item 2. Item 3 of claim 1 then gives
  `F_(j+1) <= F_j + η_n`.
- **Item 4.** The kernel ideals of the root subgroups coincide by Weyl symmetry. `B_n` embeds additively
  in `∏_(i≠j) π_n(e_ij(R_+))`. Each factor is an elementary abelian `p`-subgroup of `U(n')`, which is
  simultaneously diagonalizable and so has `F_p`-dimension at most `n'`. Strict descent of `z^k A_nu`
  bounds finite depth by `dim_(F_p) A_nu <= r(r−1)n'`.
- **Reading.** The rate statement `δ_n^2 log n → 0` is correct.

## 4. `nonunit-component-root-mass-is-log-scale-folner` (7a719f99e): PASS

- **Components.** For `χ` factoring through `A_u × A_nu`, `χ = χ_u χ_nu`, and `depth_nu` is finite because `z` is
  nilpotent on `A_nu`. The independence from the choice of `I` holds: a quotient's local factors have the
  same maximal ideals, and type is read off the maximal ideal.
- **Types under `φ_A`.** I re-derived these steps.
  - `φ_A(x_i) = ∏_j x_j^(A_ji)` with every exponent `>= 1`. A prime `m` contains it iff it contains some `x_j`,
    so `m' = φ_A^(-1)(m)` has non-unit type iff `m` does.
  - A subring of a finite local ring is local, because units have inverses that are powers and nonunits are
    nilpotent. So `ι : R_+/I' → B_n` sends each `e_(m')` to `Σ_(m lying over m') e_m`, and `e'_u` to `e_u`.
- **Unit component survives.** The image of `S = φ_A(R_+)` in `A_u` is all of `A_u`, because each `x_i` is a
  monomial in the `x^(A e_j)` with integer exponents (`A ∈ SL_d(Z)`), and inverses of units are powers. So
  `χ_u ∘ φ_A = 1` iff `χ_u = 1`.
- **Items 2–4.** These are the componentwise versions of section 3, and the same checks apply.
- **Item 5.** `{χ_nu ≠ 1} = {depth_nu = 1} ⊔ {depth_nu > 1}`, combined with section 2.

## 5. `vertex-rounding-non-unit-mass-at-origin` (61450aafd): PASS

Checked against §§2–4 of `research/artifacts/nh-unit-type-counterexample-2026-09-12.md`.

- **Lemma 2.1.**
  - The Kazhdan average gives `T ∈ Hom_Λ(ρ_2, ρ_1)` with `||T − 1||_2 <= η_n` and `||T||_op <= 1`.
  - `|a^2 − 1| >= (a − 1)^2` for `a >= 0` gives `|| |T| − 1 ||_2^2 <= ||T^*T − 1||_1 <= η_n^2 + 2η_n`. That is
    `<= 3η_n` once `η_n <= 1`; for `η_n > 1/12` the stated bound `12η_n` is vacuous anyway.
  - On `1 − e`, `(|T| − 1)^2 >= 1/4`, so `τ(1 − e) <= 12η_n`.
  - Since `e ∈ ρ_2(Λ)'`, the polar part of `Te` identifies `ρ_2|e` with a subrepresentation of `ρ_1`, and isotypic
    masses agree up to `τ(1 − e)`.
  - A sharper constant `4η_n^2`, via the support of `T^*T`, is available; the stated one is correct.
- **Lemma 3.1.** `ρ_2 ≅ π_n ∘ Ad A^(-1)`, and `Ad A^(-1) : Λ → Γ` corresponds to the ring isomorphism
  `ψ : y_j ↦ x_j`. Types and depths transfer.
- **Lemma 3.2.**
  - `J_η ⊇ J_ρ ∩ S`, and lying-over holds for the integral extension `S/(J_ρ ∩ S) ⊆ R_+/J_ρ`.
  - Every nonempty type becomes full, and the full-type maximal ideal of `S` is `(y_1..y_d)`.
  - With no intermediate factor, the only full-type factor of `ρ` is `m_0 = (x_1..x_d)`. Its component
    embeds, and `y_j^k ∈ J_0` once `k A_jj >= o_j(x)`.
- **Theorem (a).** Zero intermediate mass in `ρ_1`, together with Lemma 2.1.
- **Theorem (b).**
  - `mass(ρ_1; Θ_t) <= P_n(2t − 1) + 12η_n`, using `⌈o/2⌉ >= t` iff `o >= 2t − 1`, and charging intermediate
    constituents to (a).
  - For the iteration, `2t − 1 >= (3/2)t` for `t >= 2`.
- **Theorem (c).**
  - I checked that `Γ_I` has finite index. `Γ_I` is the normal closure of `e_ij(I)`, and `Γ/Γ_I` is a quotient of
    `St_r(R_+/I)`: the Steinberg relations hold in `Γ`, and `e_ij(a)` depends only on `a mod I` modulo `Γ_I`.
  - `St_r` of a finite ring is finite for `r >= 3`, being a perfect central extension of a finite group.
  - So `Γ_I` is Kazhdan. `π_n(e_(Γ_I))` projects onto the constituents with `J_ρ ⊇ I`, which are exactly those
    trivial on `Γ_I`.
  - **Order of limits.** I had flagged this step as a possible gap, since (H1) rounds only generators and
    the `a_k` are long averages. It closes without any uniformity in `k`:
    - `|τ(π_n(e_(Γ_I))) − τ(π_n(a_k))| <= ||a_k − e_(Γ_I)||_(C*_max)`, uniformly in `n`;
    - for fixed `k`, `a_k` is a finite combination of fixed words, so `τ(π_n(a_k)) → a_k(e)` along `U`;
    - `a_k(e) = ⟨λ(a_k)δ_e, δ_e⟩ → ⟨λ(e_(Γ_I))δ_e, δ_e⟩ = 0`, because `Γ_I` is infinite.
  - **Import re-derived.** `kazhdan-projection-is-norm-limit-of-finite-averages` has no verdict of its own.
    Its content is the standard lazy-walk argument: `m = (1 + |S|^(-1) Σ_s s)/2` has spectrum in
    `[0, 1 − κ^2/(4|S|)] ∪ {1}` in `C*_max`, so `m^k → e` in norm.
- **Bookkeeping.** As in section 1, the unitary representative must be taken in `U(n')`.

## 6. `ccr-under-vertex-rounding-from-log-transport` (2d1b8ef92): PASS

- **Part 1: the entropy identity.**
  - `π ∘ θ = Σ m_i (ρ_i ∘ θ)` has the Γ-profile as its Λ-profile, so `τ(log ζ_A) = Σ_j w~_j log(m~_j/e_j)`.
  - Centring `log(m/e) = log(m/s) − log(e/s') + log(s/s')` cancels the constant, because `Σ w' = Σ w~ = 1`.
- **Part 1: the bounds.**
  - Mean value theorem with `f_s'(x) = 1 + log(x/s)`, and the endpoint case `b = 0`, give
    `|f_s(a) − f_s(b)| <= |a − b|(1 + (1/2) log R^m)`.
  - The dimension terms are `<= (1/2) log R^e`, and `Σ_j (e_j/n')|m'_j − m~_j| = 2η*`.
  - Together: `D <= η*(2 + log R^m + log R^e)`.
- **Part 2, Step 4.**
  - `v^*v ∈ π_n(Λ)'` from the adjoint relation, and the common subrepresentation has multiplicities
    `<= min(m'_j, m~_j)`.
  - So `η* = 1 − Σ min(w'_j, w~_j) <= 1 − τ(v^*v) <= 4||1 − v||_2^2`.
- **Step 5.**
  - `τ(J) <= D/log(1 + c)` on the joint diagonalization.
  - `log(1 + c) >= c log 2` on `[0,1]`.
  - `4/(log 2)^(1/2) + 2 ≈ 6.80 <= 7`.
  - `Y = 0` gives `ε = 0`.
- **Step 7, representative dependence.**
  - `PXQ = V`, `PV^*Q = 0`, and `P[X,h]Q = V QhQ − PhP V`.
  - `τ(V^*x) >= 2s τ(V^*V)`, hence `||[X,h]||_2 >= 2s w^(1/2)`.
  - One constant is slightly off: the second-order remainder of `u h u^* − h` is at most `2ε^2 + O(ε^3)`, not
    `ε^2`. This changes only the `O(1)` term in `N_n δ'_n >= 2s w^(1/2) N_n^(1/2) − O(1) − N_n δ_n`, and the
    conclusion `lim_U N_n δ'_n = ∞` stands.
- **Imports, not re-derived:**
  - the excess lemma `ε <= 4τ(J)^(1/2) + 2c` of `commutant-excess-bounded-by-aspect-ratio-jump-mass`
    (review-major-swarm §1: PASS);
  - the rate constant `η*_n <= 2ε'_n/κ` of `ccr-under-vertex-rounding-from-few-aspect-scales`
    (review-swarm2 §4: PASS, rate constant not fully re-derived). Only the rate corollary depends on it;
    the qualitative (CCR) consequence uses `||1 − v_n||_2 → 0` alone.

## 7. `bounded-blockwise-inner-realizers-fail-off-kernel` (0f7cbdcd8): PASS

- **Step 1.** `h = n^(-1)g ∉ N`. Since `C_G(N) = 1` and `⟨S⟩ = N`, some `s ∈ S` has `[h, s] ≠ 1`.
- **Error bookkeeping.**
  - `e_B` must also count the points `x ∈ B` where `σ(g)x`, possibly outside `B`, hits a multiplicativity failure
    of `σ(n^(-1))`.
  - `σ(g)` is a bijection, so the sum over blocks is still `o(|X_n|)`. With that reading, "off at most `e_B` points"
    is correct.
- **Step 3.** I re-traced the four substitutions.
  - Each `c^(±1)` substitution fails on at most `|B \ A| <= ε|B| + e_B` points, because the intermediate maps
    `s_B^(-1)` and `s_B c^(-1) s_B^(-1)` are bijections of `B`.
  - The `s_B^(±1)` substitutions fail only on edited points.
  - The substituted map is `[c, s_B] = id_B`.
- **Step 4.** Trace zero for `d ≠ 1`, together with `ε < 1/2`, gives `m_n = o(|X_n|)`; `F` is finite.
- **Known case.**
  - Take `G = SL_3(Z) ⋊ ⟨transpose-inverse⟩` and `N = SL_3(Z)`, with the approximations `G/N_p` for principal
    congruence subgroups `N_p`. Then `C_G(N) = 1`, the two `N`-cosets are the blocks, and every `g ∉ N` swaps them.
    So no block is realized, as the theorem says.
  - The example also shows that the Instance needs block invariance, which is a separate input.
- **Instance.**
  - `C_G(N) = 1` for the Leavitt cover is item 1 of `leavitt-cover-finite-quotients-split-over-the-kernel`
    (review-hyperbolic-leavitt-cover §8: PASS).
  - Block invariance comes from `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`. That claim has no
    independent verdict, and the theorem does not use it.
- **Scope.** The scope statement is accurate: nothing beyond the existence of the edited blocks is used, neither
  property (T) nor expansion.

## 8. `finite-orbit-indices-miss-twists-without-finite-quotients` (e8856c777): PASS

- **Items 1–3.** These are elementary.
  - Invariance makes `μ` constant on an orbit, so `|O| <= 1/μ(x)`.
  - A group with no nontrivial finite quotient acts trivially on each finite orbit.
  - Item 3 is definitional.
- **Item 4: `J <= Q`.**
  - `[EL_α(R), J] = 1` is Theorem 2 of `hyperbolic-leavitt-cover-relative-defect-2026-09-12.md`, and
    `leavitt-unit-group-carries-nontrivial-rigid-defect` has a PASS (review-hyperbolic-leavitt-cover §3).
  - `Q = C_(R^×)(EL_α(R))` needs `K = N`. That holds because `C_Ĝ(Γ̂)` is finite and the cover is torsion-free.
- **Item 4: `A`.** `A` is generated by copies of `V`, so it has no finite quotients, and `ε_u(A) <= A`.
- **Item 4: strictness, re-derived.**
  - Put `ε_u(zN) = u^(-1)zuN`. Since `N ⊴ Ĝ` and `N <= Z`, `[z] ∈ ε_u(Q)` iff `ûzû^(-1) ∈ Z`.
  - Theorem 3(c) gives a lift `z` of some `j ∈ J` with `[ûzû^(-1), γ̂] ∉ N`. So `[z] ∈ A \ ε_u(Q)`.
- **Citation scope (no correctness impact).**
  - Step 5 cites item 2 of `relative-defect-iff-surjective-compressor-endomorphisms`, which is stated for sofic hosts;
    the cover's soficity is open.
  - For `K = N` neither needed fact requires soficity: `t^(-1)Zt <= Z` follows from
    `[t^(-1)zt, γ] = t^(-1)[z, tγt^(-1)]t`, and injectivity from `t^(-1)zt ∈ N ⇒ z ∈ N`.
  - Step 7 assumes an injective `σ : H → S_U`, and says so.
- **Framing.** The "intended example" paragraph is motivation, not part of the established statement. It reads
  cluster type distributions as finite-orbit data. I did not verify that those distributions carry an invariant
  `Q_s`-action, and items 1–4 do not use it.

## 9. `kun-thom-wreath-sofic-radical-is-fibre-parity-kernel` (6be4178c4): PASS, one Consequences bullet overstated

- **Step 0.** `N <= EL_r(R)`, because `EL_r(R)` is normal and contains `Γ`. The reverse inclusion is
  `[e_ij(1), e_jk(b)] = e_ik(b)` with `k ∉ {i, j}`.
- **Step 1: the criterion applies.** The criterion is `sofic-groups-kill-rigid-compression-defects`
  (review-rigid-defect-criterion: PASS; Kun–Thom Theorem 4.1 checked against the v3 PDF, proof not re-derived).
  - `φ(W)` is countable and sofic.
  - `φ(Γ) <= φ(G)` are Kazhdan, being quotients of Kazhdan groups.
  - `φ(P_Γ) ⊆ P_(φ(Γ))`, and it generates `φ(G)`.
  - `φ(e_Γ)` centralizes `φ(Γ)`.
- **Step 1: lamp algebra.**
  - `[e_(gΓ), γ] = e_(gΓ) e_(γgΓ)`.
  - Conjugating by `h = yg^(-1)` gives `e_(yΓ) e_(ycΓ)` for `c = g^(-1)γg`.
  - Telescoping extends this to every `c ∈ N`.
  - `x'Γ` lies in the `N`-fibre of `xΓ` iff `x' ∈ xN`, and an even configuration within fibres is a product of pairs.
- **Step 2.**
  - `Ψ(l, g) = ((l, ρ(g)), g)` is a homomorphism because `g·l = ρ(g)·l`, and it is injective.
  - Gruenberg (1957): `A wr B` is residually finite iff `A` and `B` are, and `A` is abelian or `B` is finite.
  - `G` is finitely generated linear, hence residually finite.
- **Steps 3–4.**
  - The radical is the smallest normal subgroup with sofic quotient, since residually sofic countable groups are
    sofic.
  - In a finite quotient a compressor normalizes the finite image of `Γ`, so `ΓΔ ⊇ N`.
  - `N` is closed, because `SL_d(Z)` is residually finite.
- **Known case: infranormality of the Theorem E pair, re-derived.**
  - Nonnegative elementary matrices generate `SL_d(Z)`.
  - `B e_ij(x_1^k) B^(-1) = e_ij(x^(kBe_1))` reaches every monomial, since every primitive vector is a first column.
  - `[e_ik(c), e_kj(x^a)] = e_ij(c x^a)`.
  - So `⟨P_Γ⟩ = G`. Since `N/Γ` is infinite, `K_even ≠ 1`, consistent with Kun–Thom Theorem A.
- **Overstated bullet.** "Intermediate wreaths" says `W_K` is nonsofic *exactly* when `N ⊄ K`.
  - `kt-intermediate-coset-wreaths-are-nonsofic` proves only the direction `N ⊄ K` ⇒ nonsofic.
  - For `N <= K`, summing over fibres makes `W_K` a quotient of `W_N`. Quotients of sofic groups need not be sofic.
  - Soficity of `W_K` would need a separate argument, for example for permutational wreath products over
    `SL_d(Z)/(K/N)`, and none is on main.
  - The theorem does not use this bullet. Suggested wording: "`W_K` is nonsofic whenever `N ⊄ K`; for `N <= K` it
    is a quotient of `W_N`."

## 10. `bh-embeddability-forces-decidable-edge-membership` (9adc98525): PASS

- **(i).**
  - Finitely presented simple groups have solvable word problem (Kuznetsov), and finitely generated subgroups inherit
    it (`simple-envelope-forces-solvable-word-problem`).
  - For `a ∉ C` the word `t a t^(-1) a^(-1)` has no pinch, so Britton's lemma makes it nontrivial.
  - In the double, `i_1(a) = i_2(a)` iff `a ∈ C`, by the normal form theorem.
  - Each test is one word-problem instance of computable length.
- **(ii).**
  - Take `Q` finitely presented with unsolvable word problem, and `H = F_2`. Belegradek–Osin Corollary 1.2 (checked
    against the PDF in review-hyperbolic-leavitt-cover §1) gives a torsion-free hyperbolic `G` whose kernel `N` is a
    quotient of `F_2`.
  - After lifting generators, `q =_Q 1` iff the lift lies in `N`. So membership in `N` is undecidable, and (i)
    excludes both extensions.
  - `hyperbolic-groups-satisfy-boone-higman` has a PASS (review-bh-swarm §2).

## 11. `fa-subgroups-of-graph-towers-lie-in-base-pieces` (9adc98525): PASS

- **Induction on tower length.**
  - The last step acts without inversions on its Bass–Serre tree.
  - FA gives a fixed vertex, and vertex stabilizers are conjugates of vertex groups (Serre, *Trees*, I.4–I.6).
  - The conjugate is again FA and lies in a strictly shorter tower over the same bases.
- **Wording.** "Each `B_i` is a subgroup of `K`" holds only for bases on which `K_n` depends. A base listed but
  unused downstream need not embed. The conclusion is unaffected, because the base reached by the induction lies on
  the dependency chain.

## 12. `finite-bi-index-subgroups-have-decidable-membership` (9adc98525): PASS

- **Proof.**
  - Each `S g_i S` is recursively enumerable, because `S` is finitely generated and the word problem is solvable.
  - The double cosets partition `Γ`, so exactly one dovetailed search halts, and the answer is yes iff it is the
    search for `g_1 = 1`.
  - Non-uniformity is correctly flagged.
- **Consequence 1.**
  - It needs finitely generated stabilizers. That is condition 3 of type (A)
    (`type-a-action-gives-boone-higman-for-subgroups`, Zaremsky arXiv:2405.18354 as quoted there).
  - `Γ_x g Γ_x` corresponds to the `Γ`-orbit of `(x, gx)`. So `m` orbits of two-element subsets give at most `2m + 1`
    double cosets.
- **Consequence 2.** `S` is finitely generated, because the envelope argument of
  `ck-envelope-simple-core-has-finite-bi-index` requires a finitely generated point stabilizer.
- **Consequence 3.** Undistortedness bounds the search by `C·len(w) + C`, since `|w|_Γ <= len(w)`.

## 13. `perfect-unit-subgroups-embed-in-elementary-groups` (c72e1f791): PASS

- **Whitehead.** Multiplying out, `e_12(u) e_21(-u^(-1)) e_12(u) = [[0,u],[-u^(-1),0]]`. Only `u u^(-1)` and
  `u^(-1) u` occur, so no commutativity is used. Then `w(u) w(-1) = diag(u, u^(-1))`.
- **Commutators.** `diag(u,u^(-1)) diag(v,v^(-1)) diag((vu)^(-1), vu) = diag(uvu^(-1)v^(-1), u^(-1)v^(-1)vu) = diag([u,v], 1)`.
- **Assembly.** Perfectness writes every element of `P` as a product of commutators within `P`. The block inclusion
  sends `E_2(R)` into `E_n(R)`.

## 14. `leavitt-path-algebras-have-simultaneous-strong-division` (cbd624ed0): PASS

- **Step 1.** With no sinks every vertex is regular, so `1 = Σ_(|γ|=N) γγ^*`. For `|μ| <= N`, `μ^*γ` is a real path
  or `0`.
- **Step 2.** Support lengths of `(a_iγ)τ_γ` lie in `[|τ_γ|, |τ_γ| + N']`, and these windows are disjoint. Right
  multiplication by a path is injective on paths. Linear independence of real paths then gives `P_i ≠ 0`.
- **Step 3.**
  - If `|ν| < |ν'|`, then `0 < |ν'| − |ν| < k|C|`.
  - So position `|ν| + k|C| + |α| + 1` of `ν'τ` lies inside `C^k α`, where every edge is on `C`, while `ντ` carries
    `ε` there.
  - `ε ∉ C`, because a cycle has one outgoing `C`-edge per vertex. Hence the paths are incomparable, and
    `η_i^* P_i τ = c_i c_0`.
- **Step 4.**
  - A path of length `>= |E^0|` repeats a vertex, so it passes through a cycle vertex, and cofinality gives `μ_γ`.
  - The `π_j = C^j α ε ρ` are pairwise incomparable, so `S^*S = Σ_j γ_j γ_j^* = 1`.
- **Step 5.** `u_i a_i X = c_i^(-1) S^*(c_i c_0) S = S^* c_0 S = 1`.
- **Hypotheses used.** No sinks (steps 1, 4); cofinality (`ρ`, `τ_γ`, `μ_γ`); condition (L) (`ε`).
- **Known case.** `s = 1` agrees with the characterization of unital purely infinite simple rings: `αxβ = 1` for
  every `x ≠ 0`.

## 15. `leavitt-path-k-theory-over-finite-fields-via-det` (cbd624ed0): PASS

- **Inputs.** ABC Theorem 7.6 was read from `lit-groups/abc-clean.txt` on MSI (`abc-leavitt-path-k-theory-exact-sequence`).
  With no sinks, the long exact sequence splits as `0 → coker(T|K_n) → K_n(L) → ker(T|K_(n−1)) → 0`.
- **Degrees, re-checked.**
  - `n = 1` needs `D ≠ 0` on `Z^V` and `gcd(D, q−1) = 1` on `(Z/(q−1))^V`.
  - For `n = 2` only the kernel on `(Z/(q−1))^V` remains.
  - Both `n = 2i−1 >= 3` and `n = 2i >= 4` reduce to `gcd(D, q^i − 1) = 1`.
  - Item 4 also needs `K_(−1)(F_q) = 0`. That holds because `F_q` is regular, but the route never mentions it; ABC
    Corollary 7.7 gives it directly.
- **Arithmetic.** A prime `ℓ ≠ p` divides `q^(ord_ℓ q) − 1`, and `p` divides no `q^i − 1`.
- **Known cases.**
  - One vertex with 2 loops: `D = −1`, so all `K_n`, including `K_0`, vanish over every `F_q`. This agrees with
    Ara–Cortiñas for `L_2`.
  - Three loops over `F_2`: `D = −2`, `K_0 = Z/2` and `K_1 = 0`.
  - The two-vertex example: `D = −2`, and the relation at vertex 2 reads `[v_1] + [v_2] = 0`, so `[1] = 0`.
- **Unused hypothesis.** "No sources" is harmless and not needed.

## 16. `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` (repair 83fee9c7b): PASS, no K-theory vanishing consumed

Coordinator request, after bh-reviewer's FAIL of the first route (4ba6fa13b). This is a line-by-line pass over
`char-p-linear-embedding-corner-swindle-proof` and its one new import.

- **`leavitt-tensor-kills-k1-of-coefficient-matrices`, re-derived.**
  - `φ(r) = s_0 r t_0 + s_1 r t_1` is a unital endomorphism. The cross terms carry `t_0 s_1 = t_1 s_0 = 0`, and
    `t_i s_i = 1` sits directly between `r` and `r'`.
  - `φ` fixes `B ⊗ 1`, because `s_i` and `t_i` lie in `1 ⊗ L`.
  - `ST = I_N`, `TS = I_(2N)`, and `φ(X) = S diag(X,X) T`.
  - For `U = [[S,0],[0,T]]` and `V = [[T,0],[0,S]]` I checked `UV = VU = I_(3N)` and
    `U diag(X, X, I_N) V = diag(φ(X), I_(2N))`. So `[X] = [φ(X)] = 2[X] = 0`.
  - `K_1 = GL/E` then gives `diag(X, I_j) ∈ E_(N+j)` for some `j`. The statement is per element and says nothing
    about `K_1(R)` beyond the image of `K_1(B)`.
- **Steps 1–2.** Lemma A stands (review-bh-swarm §5), and `R_d = R_d ⊗ 1 ⊆ R_(d+1)` is unital.
- **Steps 3–4.**
  - Each generator gets its own `j_i`.
  - `X ↦ diag(X, I_(M−N))` is an injective homomorphism `GL_N → GL_M`, and `E_(N+j_i) ⊆ E_M`.
  - So `H` lands in `E_M` of the stated host `R_(d+1) = B ⊗ L_p`, with `B = R_d`. This is exactly where the
    Whitehead map failed. For `H = SL_3(F_p[t])` the new map is still a homomorphism.
- **Step 5.**
  - `Z(R_(d+1)) = F_p`, because the centre of a tensor product over a field is the tensor product of the centres
    (`leavitt-center-is-coefficient-field`).
  - Commuting with every `e_ij(r)` forces `cI` with `c` central.
  - For `M > N` the last diagonal entry is `1`, so `H` meets `F_p^× I` trivially.
- **Step 6.** `R_d` is central simple, as a tensor power of the central simple algebra `L_p`. The route uses only
  the first bullet of part 4 of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`, which carries no
  `K`-theory hypothesis.
- **Inputs consumed.**
  - Consumed: the swindle lemma, which is unconditional; the centre; part 4, bullet 1 of the host claim. That
    bullet is a paper argument reading the Lean root-detection proof, with reviewer-2 PASS.
  - Not consumed: part 2 (`K_1 = K_2 = 0 ⇒ GL_m = E_m`), `K_1(R_(d+1)) = 0`, or any `GL = E`.
  - In Cairn the route requires the whole host claim, but that claim is ESTABLISHED only as the implication
    "if `K_1 = K_2 = 0` then …". So no vanishing premise enters the closure.
- **Bookkeeping.**
  - The route names `M_0 = N + max j_i` but needs `M >= max(M_0, N+1, 3)`. For `M = N` with all `j_i = 0`, the image
    can contain the central `−I_N`.
  - The claim only asserts that some `M_0` exists, so it holds with `M_0 := max(N + max j_i, N+1, 3)`. The name is
    mismatched, but there is no error.

## 17. `leavitt-tensor-elementary-host-criterion` (d886a82ec): PASS, inheriting the Khanh and Krstić–McCool statements

- **Step 1.** `B ⊗ L ≅ F_2⟨X ⊔ Y⟩/(rel_B, rel_L, [x, y])`. Commuting generators give commuting subalgebras. Add
  `2 = 0` to present it as a ring.
- **Step 2.** `b ↦ b ⊗ 1` is injective, since `L ≠ 0` is free over the field.
- **Steps 3–4.** Step 3 is §13. Step 4 is part 1 of `central-simple-leavitt-tensor-unit-groups-are-simple`
  (review-boone-higman-leavitt-tensor-hosts: PASS).
- **Step 5.**
  - **Krstić–McCool.** Finite presentation of `St_n(R)` is Krstić–McCool Theorem 3, as quoted in Khanh Theorem 6.1
    (`khanh-acyclicity-and-steinberg-criteria` item 6; review-bh-swarm §1: PASS at statement level, from
    `lit-groups/khanh-clean.txt`). The primary source is JPAA 141 (1999) and is not on arXiv. No Krstić–McCool text
    is among the MSI literature files, so the quotation is secondary.
  - **Neumann's lemma.** `fp-quotient-iff-kernel-finitely-normally-generated` has no verdict. It is B. H. Neumann's
    lemma: for finitely presented `P ↠ Q` with kernel `K`, `Q` is finitely presented iff `K` is finitely normally
    generated. Finite presentability does not depend on the finite generating set, and finitely many relators of
    `Q` normally generate `K` modulo those of `P`.
- **Scope.** This is a criterion. `K_(2,n)` is not shown finitely normally generated for any `B`.

## 18. `fpbs-sphere-cut-fibre-tails-decay-exponentially` (6f0d6a546): PASS

- **Cut.** `|π(xs)| − |π(x)| ∈ {−1, 0, 1}`, so a path from `o` to `Γ_q` with `|q| >= R` meets `π^(-1)(S_Q(R))`.
- **BK.**
  - Splitting a simple open path at its first crossing `y` gives edge-disjoint witnesses.
  - `H` is normal, so `y^(-1)Γ_q = Γ_(q'^(-1)q)`.
  - Summing gives `σ_p(q) <= Σ_(|q'|=R) σ_p(q') σ_p(q'^(-1)q)`.
- **Norm.** Since `|q'^(-1)q| >= |q| − R >= m`, one has `σ_p 1_(>=R+m) <= λ(σ_(p,R))(σ_p 1_(>=m))` pointwise. That
  is item 1. By sharpness `σ_p ∈ ℓ^1` for `p < p_c`.
- **Uniformity up to `p_c`, re-derived.**
  - `||λ(a)|| <= ||λ(b)||` for `0 <= a <= b`, so `θ` bounds every `p < p_c`.
  - `T_0 <= Σ_(|q|<R_0) σ_p(q)^2 + θT_0`, with `T_0 < ∞`.
  - FKG along a bounded word gives `σ_p(q) <= p^(-L) σ_p(q'')` with `|q''| = R_0`, and
    `b_(R_0) <= ||λ(σ_(p,R_0))||^2 <= θ`.
  - `P_p(o ↔ x)` is an increasing limit of polynomials, so monotone convergence carries the bound to `p_c`.
- **Necessary rate.**
  - `χ_(p_c) <= Σ_m (|S_Q(m)| T_m)^(1/2)`, which is finite if `e^h θ^(1/R_0) < 1`.
  - But `χ_(p_c) = ∞`, so `θ^(1/R_0) >= e^(−h)`, and the hypothesis fails over subexponential quotients.

## 19. `fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one` (6f0d6a546): PASS, free-quotient remark overstated

- **Equivalences.**
  - (b)⇒(c): rapid decay on `S_Q(R_0) ⊆ B_Q(R_0)`.
  - (c)⇒(d),(e): §18.
  - (d)⇒(e)⇒(a): summation by parts.
  - (a)⇒(b): `C^2(1+R)^(2D) b_R <= C^2 W_D/(1+R)^2 → 0`.
  - The dichotomy is the negation of (b)⇔(d).
- **Overstated remark.** The claim, and artifact §3, say Haagerup's inequality turns (b) into
  `(1+R_0)^2 b_(R_0) < 1` "on every generating set, with no tree-projection hypothesis".
  - Haagerup's `||λ(f)|| <= (R+1)||f||_2` holds for spheres of the *free-basis* length. Here `|·|` is the
    `π(S)`-length, and the two coincide only when `π(S) ⊆ {1} ∪ B^(±1)`.
  - For other `S`, a `π(S)`-sphere lies in a free-basis ball of radius `cR`. Rapid decay then holds with an
    `S`-dependent constant and a larger exponent, so only the general form `C^2(1+R_0)^(2D) b_(R_0) < 1` is available.
  - Switching to the free-basis length does not help, because edges can then change the length by more than one,
    which breaks the sphere cut of §18.
  - The equivalence is unaffected. Suggested wording: "When `π(S) ⊆ {1} ∪ B^(±1)` for a free basis `B`, (b) reads
    `(1+R_0)^2 b_(R_0) < 1`; otherwise it carries the rapid-decay constants of the `π(S)`-length."

## 20. `atiyah-amalgam-rank-from-cohn-coproduct` (426690471): PASS

- **Item 1.** `X = D_A ∩ U(C)` is a subring containing `K[C]`. An `x ∈ X` invertible in `U(C)` has the same inverse in
  `U(A)`, and that inverse lies in `D_A`. So `X` is division closed, and `D_C ⊆ X`.
- **Item 2.**
  - The inclusions agree on `D_C`, which gives `φ`.
  - `K[G]` has the coproduct property over `K[C]`: algebra maps are unit-group homomorphisms agreeing on `C`, and
    those extend over `A *_C B`. This gives `ψ`.
  - `φψ` equals the inclusion on `A ∪ B`, hence on `K[G]`.
- **Item 3.**
  - `rk_G ∘ φ` is a Sylvester rank function on `R`, and `rk_G(M) = rk_G(φψM)`.
  - Integrality for every `Y` forces integral kernel dimensions over `K[G]`, and `Z ⊆ (1/lcm)Z`.
  - If `G` has torsion the hypothesis fails already at `1 + g`, so the implication is vacuous there.
- **Item 4.** `Y = PQ` through `r` columns gives `rk(φY) <= rk(φP) <= r`. A non-integral `rk_G(M)` therefore lies
  strictly below the integer `ρ_R(ψM)`.
- **Context.** The Linnell and Cohn statements are flagged as not re-read, and nothing uses them.

## 21. `tree-action-with-elliptic-stabilizers-kills-lattice-transfer` (aa5d531db): PASS, conclusion 3 understated

- **Steps 1–3.**
  - A finite `F ⊆ Γ_v` lies in a compact `K`, and `Γ ∩ K` is finite, so `Γ_v = 1` by torsion-freeness.
  - An inversion `γ` would give `γ^2 ∈ Γ_v = 1`.
  - Vertex stabilizers of `Aut(T)` are open, so the image of `Γ` is discrete.
- **Step 4.**
  - A group acting freely without inversions on a tree is free (Serre, *Trees*, I.3.3), and free groups satisfy
    Strong Atiyah (Linnell).
  - The import `tree-by-elliptic-lattices-satisfy-strong-atiyah` with `H_1 = N = 1` is correct but unnecessary.
    Conclusion 3 could read "`Γ` is free".
- **Step 5.**
  - `Δ_k` is a matrix over `Z[Γ]`, so `b_k^(2)(X;Γ) ∈ Z`.
  - `free-cocompact-lattices-proportional-l2-betti` has no verdict. On its ratio: Haar unfolding gives
    `|Γ\O| = covol(Γ)/μ(Aut(X)_(v_O))` on each `Aut(X)`-orbit `O` of vertices. So the vertex-orbit ratio
    `r = |Γ\X_0|/|G\X_0|` equals the covolume ratio, and it is rational.
- **Remark.** The Platonov closure and the lamplighter instances are flagged as unchecked, and the claim does not
  use them.

## 22. `fpbs-tree-projected-translate-symmetric-nonunimodular` (f17fe39a8): PASS

- **Source, verified from the PDF.** Hutchcroft arXiv:1711.02590 (PDF dated 2020-02-26) was fetched and extracted on
  MSI (`lit-groups/hutchcroft-1711.02590.txt`).
  - Theorem 1.2: "Let G be a connected, locally finite graph, and suppose that Aut(G) has a quasi-transitive
    nonunimodular subgroup. Then p_c(G) < p_u(G)." The abstract adds `p_c < p_h <= p_u`.
  - A subgroup `Γ` is unimodular iff `|Stab_u v| = |Stab_v u|` for all `u, v` in one orbit. Closedness is not
    required.
  - Item 2 of `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` matches the source. That claim records no verdict of
    its own.
- **Step 1.** `D_(s^(-1)) = −D − a = D − c − a` is a translate of `D`, and translates of a finite nonempty set are
  unique. Reversal gives `t(ē, f̄) = −t(e,f)`.
- **Step 2.** `φ(ē)` is the reversal of `φ(e)`, so `δ_φ` is antisymmetric, and the potential exists on the tree.
- **Step 3.**
  - A horizontal edge with difference `d ∈ D(e)` maps to one over `φe` with difference `d + t(e,φe) ∈ D(φe)`.
  - Vertical edges stay in their fibre.
  - The inverse is the lift of `φ^(-1)`, with `h_(φ^(-1)) = −h_φ ∘ φ^(-1) + const`, so non-edges are also preserved.
- **Step 4.**
  - `δ_(φψ) = δ_ψ + δ_φ ∘ ψ`.
  - Closedness: if `φ_j(v_0) = w` eventually, then `φ_j` maps the ray `[v_0, ξ)` onto the unique ray `[w, ξ)`, so
    limits fix `ξ`.
  - `Aut(T)_ξ` is vertex-transitive. Hutchcroft only needs quasi-transitivity.
- **Step 5.**
  - An element fixing `u = (g,0)` fixes `g`, `ξ` and hence `p`, and sends `v` to `(p, t(e,e)) = v`.
  - An element fixing `v` sends `u` to `(φg, −t(e,φe))`. Its height is a function of `φg`, and `Aut(T)_(ξ,p)` is
    transitive on the `2n − 1` neighbours of `p` off the ray.
  - So `|Stab_u v| = 1 ≠ 2n − 1 = |Stab_v u|`. This is Hutchcroft's definition directly, and no Trofimov/BLPS
    equivalence is needed.
- **Known case.** `S = B^(±1) × {0} ∪ {(1, ±1)}` gives `T_(2n) □ Z`, covered by Hutchcroft Corollary 1.3. The
  claim reproduces it with `D = {0}`, `c = 0`.

## 23. Cairn state of the linear-group Boone–Higman chain (coordinator request, follows §16)

MSI `cairn check` at 4667e71ee, which contains §16: EXIT 0, 0 ERROR.

- **The embedding.** `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` is ESTABLISHED via
  `char-p-linear-embedding-corner-swindle-proof`. Its closure is the swindle lemma, the centre, the prime-field host
  claim and Khanh. The Whitehead route shows ✗, invalidated by `whitehead-diagonal-map-is-not-multiplicative`.
- **The finite-presentation premise.** `positive-char-linear-groups-satisfy-boone-higman` is OPEN. Its only live
  route waits on this chain, every link OPEN:
  - `leavitt-power-projective-elementary-groups-finitely-presented`;
  - `leavitt-power-projective-e-fp-from-trivial-k-theory`;
  - `prime-field-leavitt-tensor-powers-have-trivial-k-theory`;
  - `prime-field-leavitt-powers-k-theory-via-coherence`;
  - `leavitt-tensor-powers-are-left-coherent`.
- **Characteristic two and the conjecture.** `char-two-linear-groups-satisfy-boone-higman` is OPEN, through
  `leavitt-tensor-powers-have-trivial-k-theory` and the same coherence claim. `boone-higman-conjecture` is OPEN.
- **Coherence.** `cairn why leavitt-tensor-powers-are-left-coherent` reports a frontier hole with no live routes. If
  it is established, the cascade establishes `char-two-linear-groups-satisfy-boone-higman`,
  `leavitt-power-projective-elementary-groups-finitely-presented` and `positive-char-linear-groups-satisfy-boone-higman`.
- **Conclusion.** The linear-group Boone–Higman claims stay OPEN while coherence is open.
- **Routing gap, not an error.** Attempt 3 of `leavitt-power-projective-elementary-groups-finitely-presented`, finite
  normal generation of the unstable Steinberg kernel, would bypass coherence and `K_1`. It is recorded as an attempt,
  not as a route.
