# SK review 7, part 4: distortion, towers, trace templates, recurrent kernels, Cartans, strips, rank envelopes, Laurent lattices

Lane `sk-verify-7`, 2026-09-13 ~21:30 CDT. This is the triaged backlog of `sk/queue/sk-verify-7.txt` after the fleet restart.
- I re-derived every step before reading the owners' justifications.
- Skipped per main's triage (owned by sk-verify-8): sk-universal-lef-host-a, sk-characters-rigidity-b, sk-el2-fq,
  sk-simpler-unify, sk-rank3-lef-converse. No `sk-review-8` artifact was on main at this landing.
- Already covered in part 3 (ef28dd4d20): sk-perfect-overgroup (2314f1f919), sk-strong-5 (8bda51df7f), sk-lef-growth-all
  parts 1–2 (0cfa7e7002), sk-strong-6/8, sk-universal-lef-host-b and sk-wp-host. The commits main cited for these hold
  exactly the text reviewed there.

## 0. Verdicts

| Claim (owner) | Verdict |
|---|---|
| `subshift-crossed-product-gl-has-no-distorted-elements` (sk-sl3z-bandwidth) | PASS |
| `heisenberg-group-lies-in-no-z-subshift-elementary-group` (sk-sl3z-bandwidth) | PASS |
| refutation recorded on `every-lef-group-embeds-in-a-z-subshift-elementary-group` | PASS (the refutation holds) |
| `lef-growth-of-subshift-el-groups-is-monotone-under-factors` (Theorem M) | PASS |
| `thue-morse-elementary-group-lef-growth-is-exp-r-squared` (Theorem TM) | PASS; note W8 |
| `chacon-elementary-group-lef-growth-is-exp-r-squared` (Theorem Ch) | PASS |
| `fp-simple-models-concentrate-on-template-constituents` (sk-trace-template) | PASS |
| `constituent-gapped-finite-groups-closed-under-products` | PASS; (c) conditional on `lst-quasisimple-classical-character-ratio-bound` |
| `fp-simple-groups-have-no-models-through-classical-products` | PASS; conditional on the LST import |
| `template-constituents-primitive-or-small-minimal-degree` | PASS |
| `subshift-visit-chains-are-bounded-off-every-minimal-subset` (sk-k2-recurrent, Chain Lemma) | PASS |
| `minimal-set-complement-ideal-is-ultramatricial` (Proposition C′) | PASS; the GL clause is conditional on Lemma B (`ultramatricial-ideals-have-elementary-congruence-kernels`) |
| `restriction-kernel-relative-elementary-off-minimal-sets` (Theorem D′) | PASS; the K_2 clause is conditional on Lemma A of sk-k2-subsystems |
| `finitely-many-minimal-sets-el-normal-subgroups-are-kernels` (Corollary E′) | PASS; conditional on the sandwich and ideal nodes |
| `recurrent-orbit-closure-with-unique-sturmian-minimal-set` (§5 example) | PASS |
| `equivariant-retract-splits-subshift-el-restriction` (Theorem R) | PASS |
| `clopen-invariant-complement-el-kernel-is-elementary` (Proposition S) | PASS |
| `cohomologous-roofs-give-conjugate-cantor-towers` (sk-cartan-counterexample, Theorem A) | PASS |
| `corner-matrix-ring-isos-force-flip-conjugacy` (Corollary B) | PASS; conditional on the reconstruction and full-group imports |
| `orbit-bijective-cocycle-gives-z-action-groupoid` (Lemma C) | PASS |
| `cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity` (Theorem D) | PASS; conditional on Theorem C of `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity` |
| `strip-commutative-tiling-families-force-periodic-points` (sk-labbe-2d, Theorem A) | PASS |
| `aperiodic-sft-torus-modules-are-contextual-in-every-direction` (Corollaries C, D) | PASS; note W9 |
| `sofic-lamplighter-bernoulli-crossed-products-have-rank-models` (sk-measured-subshift, Theorem A) | PASS |
| `sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups` (Theorem B) | PASS; conditional on `rank-modelled-simple-rings-give-linear-sofic-projective-el` |
| `laurent-sl-n-representations-have-sl2-invariant-vectors` (sk-matricial-stability, Theorem 1) | PASS; conditional on the BMS import and `sl4-over-finite-chain-rings-has-sl2-invariant-vectors` |
| `laurent-sl4-stability-makes-overgroups-reduced-non-mf` (Theorem 2) | PASS |

No FAIL, no GAP.

## 1. Distortion obstruction (priority item)
- **Slot module.** `fδ_{x,t} = f(T^tx)δ_{x,t}` and `uδ_{x,t} = δ_{x,t+1}` satisfy `ufu^{-1} = f∘T^{-1}`.
  - `M_m(R)` acts faithfully: `Aδ_{x,0}ξ = Σ_jA_j(T^jx)ξδ_{x,j}`, and the terms lie in distinct slots.
  - Propagation is subadditive.
- **Theorem D.**
  - `p(z^n) ≤ w|z^n|_S`, so the Krylov space `K_N(v)` lies in `m(2wℓ(N)+1)` slot dimensions.
  - Fekete gives `|z^n| ≤ (τ+ε)n + C`. So for `τ < 1/(2wm)` there is one `N_0`, independent of `v`, with every slot vector
    killed by a monic polynomial of degree `< N_0`.
  - The lcm `P` of those polynomials kills the spanning slot vectors, so `P(z) = 0` by faithfulness.
  - `P = t^aQ` with `Q(0) ≠ 0`, and `z` invertible, give `Q(z) = 0`. So the powers of `z` lie in the finite ring
    `F_q[z]` and `z` has finite order.
  - Checked.
- **Heisenberg.**
  - `c = [a,b]` is central of infinite order, and `[a^n,b^n] = c^{n²}`.
  - For `n² ≤ N < (n+1)²`, `|c^N| ≤ 4n + 4·2n ≤ 12√N`.
  - So `τ(c) = 0` for the images of `a^{±1}, b^{±1}`, which have bounded propagation.
  - `H` is RF, hence LEF. `SL_n(Z) ⊇ H` for `n ≥ 3`, and `a` is exponentially distorted in `BS(1,2)`.
  - Checked. The refutation of `every-lef-group-embeds-in-a-z-subshift-elementary-group` holds: `G_X ≤ GL_3(R)`.
- **For the note.** The note may cite this as the reason rev3's LEF characterization needs lamplighter hosts rather
  than the Z-family.

## 2. Towers: parts 3–4
- **Theorem M.**
  - `π∘T_X^{-1} = T_Y^{-1}∘π`, so `f ↦ f∘π` gives an equivariant injective ring map `R_Y → R_X`.
  - The generators map to words of bounded length `K`, and partial models restrict along `B_Y(r) → B_X(Kr)`.
  - Checked.
- **TM1.**
  - `q_{2n} = 1 + t_n + 1 + t_n = 0` and `q_{2n+1} = t_n + t_{n+1} = 1 + q_n`, with `q_0 = 0`.
  - The period-doubling point has `p_{2n} = 0` and `p_{2n+1} = 1 + p_n`.
  - The block code maps onto `X_PD`.
  - Checked.
- **TM2.**
  - The residue classes `c ≢ 2^k−1 (mod 2^k)` are constant by induction, and the class `2^k−1` carries `(k mod 2) + p_n`.
  - The odd-period descent argument shows `p` is not eventually periodic.
  - `σ²(0) = 0100` and `σ²(1) = 0101`, so `σ` is primitive.
  - Checked.
- **TM3.** `σ³(0) = 01101001` and `σ³(1) = 10010110` each contain `00, 01, 10, 11`, and `2^{k+5} < 64n`. Checked.
- **Theorem TM.** The factor map, T2 and Theorem M give the lower bound; `N ≤ 2R ≤ 128n` gives the upper bound. Checked.
- **W8 (wording).** Hypothesis (T) is phrased for a two-sided `x ∈ A^Z`, but the period-doubling point is one-sided. The
  proof of T1 still works:
  - use forward-orbit density (minimality) to pick `s ≥ |t|` with `T^sx ∈ W_k ∩ T^tW_k`, for any two-sided `x ∈ X` whose
    right half is `p`;
  - then only nonnegative positions are used, where the class structure is proved.

  Add one sentence.
- **Chacón.**
  - Ch0: only the first two slots of a `B_{n+1}`-copy give `(0,1)`.
  - Ch1: `h_{k+1} = 9h_{k−1} + 4 < 9n+4`.
- **Theorem Ch.**
  - Local characterization, case `o ≤ h_n − 2`: `c+h_n+1` lands at offset `o+1−σ` of the next copy, and reads `0`.
  - Case `o = h_n−1`: `σ = 0`, and the letter after the second copy is `1` exactly on the slot pair `(0,1)`.
  - No returns: two occurrences are ends of first copies in distinct `B_{n+1}`-copies, which start `≥ h_{n+1}` apart.
  - Cost `2+2·25 = 52`, then `104 + 2(1+24(h_n+1)) = 154 + 48h_n`.
  - Ch2: `20κ + 480m = 3080 + 2400m`, and `9(36(4r+1)+18)² = 9(144r+54)²`.
  - Checked.

## 3. Trace templates
- **Step 0.** Unitaries give `‖AB − A′B′‖_2 ≤ ‖A−A′‖_2 + ‖B−B′‖_2`, so `Δ_k → 0` and `E_k → η² > 0`.
- **Additivity.** `τ(ρ(g)) = Σ_σ p_σχ̃_σ(g)`.
- **Classes.**
  - (i) The kernel of `S → Q_k/Z_σ` has finite index, so it is `S`, and `c` acts trivially.
  - (ii) `2 − 2Reχ̃ ≥ 2 − 2θ`, then Markov.
  - (iii) The compactness lemma: a limit point is a homomorphism `S → U(n)`. Its image is f.g. linear, hence RF, and a
    quotient of the infinite simple `S`, hence trivial.
  - (iv) At most `4p_σ` each.
- **Conclusion.** `η² ≤ ε + 4lim Σ_T p_σ`. Checked.
- **Corollary 1.**
  - The diagonal sets `B_m ∈ ω` and `m(k) → ∞`.
  - Choose `e_σ ≥ η²/2`.
  - `d_proj² = 2 − 2|τ|`, and the null sequences form a normal subgroup, which gives `Ψ`.
  - Nontriviality: `‖[A,B′] − I‖_2 ≤ 2‖A−I‖_op‖B′−I‖_2 ≤ 4β_k`.
  - The adjoint: `2−2t ≤ 2−2t² ≤ 2(2−2t)`.
  - Checked.
- **Permutation template.** Hamming distance averages over orbits, and a nontrivial permutation moves `≥ 2` points.
  Checked.
- **Closure.**
  - A tensor product of scalars is a scalar.
  - Quotients keep their characters.
  - Abelian groups have only one-dimensional irreducibles, so the condition is vacuous.
  - (d): Schur.
  - (e): the standard representation of `A_m`, `m ≥ 4`, is irreducible, and a 3-cycle has ratio `(m−4)/(m−1)`.
  - Checked; (c) rests on the LST import.
- **Classical products.**
  - `S` is perfect, so `v_x ∈ F(X)^{(L)}` and the model moves into `Q_k^{(L)}` without changing `Π`.
  - Derived series: `GL_2(3)^{(4)} = 1`, `GL_2(2)^{(2)} = 1`, and `GL_N(q)^{(1)} = SL_N(q)` perfect otherwise.
  - Permutation matrices satisfy `‖P−I‖_2² = 2·(moved fraction)`.
  - Checked.
- **Primitive sections.**
  - Maximal block systems exist.
  - Fixed points push down: `fpr_𝓑 ≥ fpr_Ω`.
  - Relators are seen on 𝓑, else there is a homomorphism to a finite group.
  - For induced representations, `|χ̃_σ(q)| ≤ fpr_Ω(q)`.
  - `GL_N(F_2)` on nonzero vectors has `μ̂ > 1/2`.
  - Checked.

## 4. Recurrent restriction kernels
- **Chain Lemma, (a)⇒(b).**
  - `V_m` is clopen, decreasing and nonempty, and König gives an infinite `J`-chain.
  - Limits of shifts visit `V` in every `J`-interval (fixed times after subsequences, `V` clopen).
  - A minimal subset of the orbit closure meets `V ⊆ X∖Y`.
  - Checked.
- **Chain Lemma, (b)⇒(a).** `M ∩ Y` is closed invariant in minimal `M`, and a clopen neighbourhood of `M` inside `X∖Y`
  gives unbounded chains. Checked.
- **C′.**
  - `V = ⋃(supp f_j ∪ T^{-j}supp f_j)` gives `r_i = e_Vr_ie_V`.
  - `~` is an equivalence relation with class size `≤ M` and time diameter `≤ (M−1)J`.
  - `B_{V,J}` is closed under products by transitivity, and matrix units on the class towers give
    `∏M_{k_0}(F_2)^{c_{k_0}}` after refinement.
  - Checked.
- **D′.**
  - `R_{Y∪Z} = R_Y × R_Z`.
  - The lift `e_Us` with `U ⊇ Z`, `U ∩ Y = ∅` restricts to `(0, ρ_Z(s))`.
  - `gh^{-1} ∈ ker π_{Y′} ⊆ E_n(I_Y)`.
  - Checked.
- **E′.** Finitely many infinite minimal sets means no periodic points. Take `Z` = the minimal sets outside `Y`; then
  sandwich plus D′ collapse, and `I_Y` recovers `Y`. Checked.
- **§5 example.**
  - (G) keeps every subsum with an index `≥ k+1` outside `[−N_k,N_k]`, and every subsum with an index `≥ k+2` beyond
    `n_{k+1} + N_k`.
  - Windows copy, so `x` is recurrent; the gap `n_{k+1} − N_k → ∞`, so it is not uniformly recurrent.
  - `n_j − N_{j−1}` is increasing by (G), so `J`-chains stay in one translate of `S_k`. Minimal sets carry syndetic
    visits, so the only minimal set is `X_α × {0^∞}`.
  - Checked.
- **Proposition S.** `e_U` is central for clopen invariant `U`, `g = (1−e_U)I + e_Ug`, and `e_Ug ∈ EL_n(R_U)` lifts
  factorwise. Checked.
- **Theorem R.**
  - `s(f) = f∘r` splits `ρ_Y`.
  - `e(r_t) = e(r′_t)e(d_t)`, and conjugating the `d_t` factors gives `g ∈ EL_n(s)(π_Y g)·E_n(R_X,I_Y)`.
  - Checked. The example `X_α × S` works because Sturmian systems have no rational eigenvalues, so `X_α × O(p)` is minimal.

## 5. Cartan reduction
- **Theorem A.**
  - `R′_k − R_k = h(z) − h(σ^kz)` by telescoping; representatives are unique because `σ` is aperiodic.
  - `Φ` is well defined by the partial-sum identity.
  - Continuity: `z ↦ T_{r′}^m(z,0)` is continuous for fixed `m`, on the clopen pieces.
  - Coboundary conventions `f − f∘σ^{-1}` and `h − h∘σ` agree.
  - Checked.
- **A′.** `θ_*[r_U] = [r_V]` makes `r_V∘θ − r_U` a coboundary. In the flip case `[r_V∘S_V^{-1}] = [r_V]` and `K^0` is
  unchanged. Checked.
- **B.**
  - The reduction `𝒢_X|_U = Z ⋉_{T_U} U`.
  - The diagonal-preserving isomorphism gives a groupoid isomorphism, hence full groups, hence θ (imports).
  - `ι_U[1_X] = [r_U] = n[1_U]` by linearity of ι_U.
  - Checked.
- **Lemma C.**
  - `s|_{B_n}` is a homeomorphism.
  - `r|_{B_1}` is injective (`γ^{-1}γ′` has `c = 0`, so it is a unit) and onto (`η^{-1}` with `c(η) = −1`).
  - Checked.
- **D.**
  - (D1) with Lemma C gives `G ≅ Z⋉_TY` with `T` minimal and aperiodic.
  - Finite generation makes `(Y,T)` a subshift (`crossed-product-el-kazhdan-iff-finite-field-and-subshift`, PASS in sk-review-5).
  - (D2) then gives the isomorphism.
  - Checked.
- **§5 test object (not a claim).**
  - `s² = 1` and `sT′s = T′^{-1}`.
  - `T′` is minimal because `−1` is not an eigenvalue of `X_α`.
  - `sT′^k` fixes palindromes centred at `k/2`, for odd `k`.
  - The isotropy `Z/2` rules out a fibre-bijective cocycle.
  - Checked.

## 6. Strips
- **Lemma 1.** Illegal `π` has only illegal extensions. `B_D` factors commute by (Q2), and inserting (Q1) expands the
  product into (Q3) terms. Checked.
- **Theorem A.**
  - `ℓ_e(w) = 1` exists for primitive `e`, and `|ℓ_e(h)| ≤ m_e` on `B_r`.
  - Levels give commuting blocks `E_β(c)`. A repeated (level, `t mod L`) site forces the same letter, so the product is
    idempotent.
  - An illegal window multiplies to 0 through (Q3_r).
  - König gives a period-`Le` point.
  - Ordered expansion of `1 = ∏_cΣ_βE_β(c)` makes every term contain a consecutive illegal window, so `W = 0`.
  - A.2: with `|A|^{2m_eL}+1` block positions two blocks coincide.
    - The periodic extension `y` agrees with `β` on `[p, p′+2m_e)`, by induction on `i` using the block coincidence at
      offsets `< 2m_e`, also when `p′−p < 2m_e`.
    - Windows starting in `[p,p′)` end by `N−1`.
    - `x` has independent periods `Le` and `(p′−p)w`.
  - Checked.
- **B.** Shifting by multiples of `(0,L)` gives `|z_2−z′_2| ≤ ⌊L/2⌋ ≤ 2D` and `|z_1−z′_1| ≤ 2r ≤ 2D`, so (Q2) commutes.
  Checked.
- **C.** `L_ee ∈ Λ`; the contrapositive of A.1; (T2) rules out representatives in `B_{2D}`. Checked.
- **W9 (scope).** Corollary D uses that `U^e` has finite order. That holds for finite-dimensional families over a finite
  field; the claim should say "finite-dimensional" (torus modules are). The mathematics is unchanged.

## 7. Rank envelopes over sofic groups
- **Right action.** `v·h = σ_k(h^{-1})v` is a right action on `K`-good points and injective on `K`.
- **Localization.** `x_{π(s)p}(h) = c(v·(s^{-1}h)) = (s·x_p)(h)`, and `x_{π(a)p}(h) = x_p(h) + [h=e]` by injectivity.
  Checked.
- **(ii).** On columns with good base points, covariance and multiplicativity hold (items 1–2 with `K` containing
  inverses), so the rank is `≤ 2^{|V_k|}·#bad = o(N_k)`. Checked.
- **(iii).**
  - A clopen `U` exists with `f_{ℓ_0}∘ℓ_0 ≡ λ` and `U ∩ ℓU = ∅` for `ℓ ∈ F^{-1}F∖e`.
  - Exact counting `#{c : x_{(c,v)} ∈ U} = ν(U)2^{|V_k|}`, since `h ↦ v·h` is injective on the window.
  - A nonzero entry at row `π(ℓ_0)p`, column `p′ ∈ C_k` forces `x_p ∈ U ∩ ℓ_0^{-1}ℓU`, so `ℓ = ℓ_0` and `p′ = p`.
  - The submatrix is `λI`.
  - Checked.
- **Theorem B.** The half-line overgroup (PASS, part 3); the lamplighter host is simple with trivial centre (part 1) and
  Kazhdan; linear sofic by the rank-model node; `diag(u_ℓ,1,1)` on `[L,L]`. Checked, conditional on the rank-model node.
- **§5 overgroup (not a claim).** `σ ↦ σ⊕σ` is a Hamming isometry into `Alt`, and Ore works coordinatewise. Checked.

## 8. Laurent lattices
- **Theorem 1.**
  - Commuting unitaries of order `p` give `|ρ(U_ij)| ≤ p^d`, so the kernel has finite index.
  - `[e_ik(r),e_kj(s)] = e_ij(rs)` gives `(I_ik) ⊆ I_ij`, and `J` is a nonzero product ideal.
  - BMS 4.3(a,b) apply because `F_q[t^{±1}]` is the ring of `S`-integers of a function field, not totally imaginary, so
    `SL_n(A,J) = E_n(A,J) ⊆ ker ρ`.
  - `A/J` is a finite principal ideal ring, so the chain-ring node gives a block-`SL_2` invariant vector in the upper-left
    `SL_4`.
  - Kesten gives `‖λ(z)‖ = 2√3` for a free pair.
  - Checked; conditional on the BMS page-image import and the chain-ring node.
- **Theorem 2.**
  - `C*_r(Λ) ⊆ C*_r(Γ)` isometrically; lift unitaries; stability gives genuine `π_n`.
  - `limsup‖π_n(z)‖ = ‖λ(z)‖ = 2√3` against `‖π_n(z)‖ = 4`.
  - Checked. It applies to `G_X ⊇ SL_{3k}(F_q[t^{±1}])` (`subshift-elementary-groups-contain-laurent-sl-n-lattices`).

## 9. Scope
- **Not re-read at source:** LST Theorem 1.2.1, BMS (owner read page images), Magee–de la Salle, Kesten, Nagao,
  Droubay–Pirillo, Elek–Szabó, Kerr–Li.
- **Not searched:** novelty (sk-lit-novelty-2).
- **Imports named as conditions:** these keep their own review status on main.
