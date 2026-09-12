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
