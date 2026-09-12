# Review backlog, pass 3, 2026-09-12

Lane `review-backlog-3`. This pass reviews ESTABLISHED claims landed on 2026-09-12 before 15:00 that have no verdict yet. That excludes passes 1 and 2 (`review-backlog-2026-09-12.md`, `review-backlog-2-2026-09-12.md`) and every other review artifact on main. Claims landed after 15:00 belong to `swarm4-reviewer`.

Order of work:
1. the Kun–Thom rounding and unit-type chain to `non-hyperlinear-group`;
2. Leavitt rank-model nodes;
3. Thompson F;
4. Gottschalk table nodes.

**How the queue was built, at tip e367b4372:**
- start from the nodes first added between 00:00 and 15:00, not counting the restore commit 3f71a3a50;
- keep those marked ESTABLISHED in `research/FRONTIER.md`;
- drop every id that heads a section in any 2026-09-11 or 2026-09-12 review artifact.

69 claims remain.

**Verdicts:**
- **PASS:** the proof holds as written, up to its stated trust surfaces.
- **GAP:** a step is asserted but not proved, and the conclusion is not known to be false.
- **FAIL:** a step or the conclusion is false.

## 1. `root-character-nonunit-depth-at-most-log-q-dimension` (3a9a8d38e): PASS

Checked against `root-character-depth-log-dimension-proof` and §2 of
`nh-h1-quantitative-2026-09-12.md`.

- **Item 1, independence.**
  - Suppose `Σ_(i0<=i<k) c_i e_nu z^i ∈ J_χ` with `c_(i0) ≠ 0`. It factors as `e_nu z^(i0) u` with `u = c_(i0) + zw`.
  - Each local factor of `A_nu` is finite, with `z` in its maximal ideal, so `z` is nilpotent there. Hence the `A_nu`-component of `u` is a unit.
  - Multiplying by an element whose `A_nu`-component is `u^(-1)` stays inside the ideal `J_χ`. So `e_nu z^(i0) ∈ J_χ`, and then `e_nu z^(k-1)B ⊆ J_χ ⊆ ker χ`.
  - That makes `χ_nu` trivial on `z^(k-1)R_+`, contradicting minimality of `k`.
  - `J_χ` is an `F_q`-subspace because `F_q ⊆ B`. So `dim_(F_q) B/J_χ >= k`, and `|B/J_χ| >= q^k`.
- **Item 2, Heisenberg count.**
  - I re-derived the three Steinberg relations it uses, each needing `r >= 3`:
    - `[x_12, x_13] = 1`, since both lie in the same row;
    - `[x_12, x_32] = 1`, since `x_ij` and `x_kl` commute when `j ≠ k` and `i ≠ l`;
    - `[x_13(b), x_32(c)] = x_12(bc)`, by the rule `[x_ij(a), x_jk(b)] = x_ik(ab)` with `i ≠ k`.
  - On `V_χ` this gives `X(b)Y(c) = χ(bc)Y(c)X(b)`.
  - Let `v` be a joint eigenvector of `X(B)` with character `λ`. Then `Y(c)v ≠ 0` has character `b ↦ λ(b)χ(bc)`.
  - Two of these characters agree iff `χ(b(c−c')) = 1` for all `b`. That says `(c−c')B ⊆ ker χ`, which by definition is `c − c' ∈ J_χ`.
  - Distinct joint characters have orthogonal eigenspaces, so `dim V_χ >= |B/J_χ|`. The same argument runs inside any irreducible constituent whose `x_12`-spectrum contains `χ`.
- **Item 3.**
  - For the normalized spectral measure, `μ({χ}) = dim V_χ/N`.
  - Chaining the inequalities gives the display.
  - `D(π)` is at most `log_q` of the largest constituent dimension, which is at most `log_q N`.
- **Factorization through `St_r(B)`, a hypothesis the consumers need.** It holds automatically for every finite-image representation `π` of `EL_r(R_+)` with `r >= 3`, with no congruence subgroup property:
  - `J = {f : x_12(f) ∈ ker π}` is an ideal: `x_12(fb) = [x_13(f), x_32(b)]`, `ker π` is normal, and Weyl conjugation carries `x_12(f)` to `x_13(f)`;
  - `J` has finite index;
  - `St_r(R_+) → EL_r(R_+) → im π` kills every `x_ij(J)`, so it factors through `St_r(R_+/J)`.

  The components do not depend on the level (item "Components" of `nonunit-component-root-mass-is-log-scale-folner`), so `D(π)` is well defined.
- **Test case.** Take `d = 1` and `B = F_q[x]/(x^k)`, so `A_u = 0`, and let `χ` be nontrivial on `x^(k−1)B`.
  - The ideals of `B` are `x^iB`, so `J_χ = 0` and the bound reads `q^k <= dim V_χ`.
  - This matches Stone–von Neumann for the Heisenberg group over the finite local ring `B`: an irreducible representation with a central character that is nontrivial on the socle has dimension `|B| = q^k`.

## 2. `nonunit-root-mass-log-depth-scale-bound` (3a9a8d38e): PASS

Checked against `nonunit-root-mass-log-depth-proof` and §3 of the artifact.

- **The inputs match their statements on main.**
  - Item 3 of `nonunit-component-root-mass-is-log-scale-folner` (pass 1 §4) is exactly the per-scale cap
    `μ_n(d^j < depth_nu <= d^(j+1)) <= η_n` for `j >= 0`.
  - Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` (pass 1 §24) is
    `μ_n(depth_nu = 1) <= qη_n + η_n^t`, and its item 2 gives `η_n^t → 0` along `U`.
  - `nonunit-projection-bounded-by-root-spectral-mass` (pass 1 §2) bounds `τ(1 − P)` by
    `r(r−1)·μ(χ|A_nu ≠ 1)`, and `χ|A_nu ≠ 1` is the same event as `χ_nu ≠ 1`.
- **Item 1.**
  - By definition `D_n` is the largest depth on the support of `μ_n`, so no mass lies above it.
  - The blocks `(d^j, d^(j+1)]`, `j >= 0`, that meet `(1, D_n]` are those with `d^j < D_n`. There are `⌈log_d D_n⌉ <= 1 + log_d D_n` of them.
  - If `D_n <= 1`, the left side is 0.
- **Item 2.** `{χ_nu ≠ 1} = {depth_nu = 1} ⊔ {depth_nu > 1}`, because `depth_nu = 0` iff `χ_nu = 1`. Adding the two bounds gives the display exactly.
- **Item 3.**
  - `η_n → 0`, so the constant term vanishes.
  - `log max(1,D) <= log(1+D) <= log 2 + log max(1,D)`. So `η_n log_d max(1, D_n) → 0` iff `δ_n^2 log(1+D_n) → 0`.
  - With `D_n <= log_q n'` from §1 and `n'/n → 1`, it suffices that `δ_n^2 log log n → 0`.
- **Counterexample shape.**
  - Order-one mass `c` above depth one forces `log_d D_n >= c/η_n − 1`, so `D_n >= d^(c/η_n − 1)`.
  - The claim writes `>` where only `>=` follows. Nothing downstream uses strictness.
  - §1 then forces a constituent of dimension at least `q^(D_n)`.
- **Amplification.** The rate is correctly stated against `D_n`. Normalized HS distances, and the support of `μ_n`, do not change under `σ ↦ σ ⊗ 1_m` when the rounding is amplified along with `σ`.

## 3. `kt-free-action-hyperlinear-iff-wreath-hyperlinear` (2e14f4a8a): PASS

Checked against `kt-free-action-hyperlinear-iff-wreath-proof` and the verbatim GKP statements in
`research/artifacts/gkp-2401-04945-verified.md`.

- **Step 1.**
  - Fourier duality identifies `L(⊕_I Z/2)` with `L^∞({0,1}^I, fair)`, `G`-equivariantly, where `I = G/Γ ⊔ G`. So `L^∞(X) ⋊ G = L((⊕_I Z/2) ⋊ G)`.
  - The Bernoulli factor `{0,1}^G` makes the diagonal action free. The orbit-relation algebra is therefore this crossed product, which gives item 1 ⇔ item 2.
- **Step 3.** I re-derived `W' = Z/2 ≀_α W`.
  - In `W'`, `(a,b,g)(a',b',g') = (a + g·a', b + g·b', gg')`.
  - Let `w = (b,g) ∈ W` act on `a'` through `p(w) = g`. This is exactly `(a,w)(a',w') = (a + p(w)·a', ww')`.
- **Step 4.**
  - `G = EL_r(R) ⋊ SL_d(Z)` is residually finite by Theorem E (imported in `kun-thom-nonsofic-wreath`), hence sofic.
  - GKP Theorem 2.14 with `N = {1}` makes `G ↷ G` sofic.
  - GKP Proposition 2.15(1), composition with the quotient map `p : W → G`, makes `α` sofic.
  - The route re-derives 2.15(1) from Definition 2.1(5), consistently with the transcription.
- **Step 5.** The "in particular" clause of GKP Theorem 3.8, with lamp group `Z/2` and acting group `W`, gives 3 ⇒ 1.
- **Step 6.** A factor map gives a trace-preserving `G`-equivariant embedding of `L^∞(Y) ⋊ G = L(W)` into `L^∞(X') ⋊ G`.

Trust surface: Kun–Thom Theorem E (unrefereed) and the GKP transcription.

## 4. `hyperlinear-flexibly-hs-stable-group-is-residually-finite` (8a12c4708): PASS

- **Separating approximations.** Hyperlinearity gives asymptotic representations whose normalized traces tend to 0 off `e`, so `||π_n(g) − I||_2 → √2`.
- **Stabilizing.** `P_n I_(D_n) P_n = I_(d_n)`. So the triangle inequality gives `||P_n(ρ_n(g) − I)P_n||_2 >= √2 − o(1)`, and `ρ_n(g) ≠ I` for large `n`. Hence `Γ` is maximally almost periodic.
- **Malcev.** Every f.g. linear group is residually finite. A finite quotient of `ρ_n(Γ)` separating `ρ_n(g)` from `I` is a finite quotient of `Γ` that does not kill `g`.

This is a standard principle, and the claim asserts no novelty.

## 5. `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class` (e1558fc60): PASS on the derivation, inheriting three inputs

- **Step 1** is §4.
- **Step 2.**
  - `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` has exactly the hypotheses used: hyperbolic, (T), `b_2 >= 1`, flexibly HS stable. Hyperlinearity of `Γ` is not needed there.
  - It gives a non-hyperlinear finite central extension `Γ_N`.
  - F.g. residually finite groups are sofic, so `Γ_N` is not residually finite.
- **Step 3.** `finite-kernel-nonrf-has-central-prime-reduction` applies with `K = Z/N`, `H = Γ` (residually finite by step 1) and `E = Γ_N`. Its output `R(L/B) = R/B ≅ C_p` says `L/B` is not residually finite.
- **Step 4.**
  - Apply `finite-central-extension-rf-iff-virtually-splits` with `H = H_0` and `A = C_p` central. `H_0` has finite index in `Γ`, so it is residually finite and hyperbolic.
  - This turns "`L/B` is not residually finite" into "`α` restricts nontrivially to every finite-index subgroup".
  - I checked the folklore equivalence. A finite-index normal `N <= E_α` with `N ∩ A = 1` is a section over its image. Conversely, a splitting over `H_0` puts `A × H_0` at finite index.
- **Step 5.**
  - For a good group, every class in `H^2(−; C_p)` is inflated from a finite quotient `Γ/N`, and so dies on `N`.
  - Goodness passes to finite-index subgroups, so `Γ` is not good.
- **Inherited, not re-reviewed here:**
  - `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity`, through Dogon–Vigdorovich arXiv:2506.20843;
  - the Section 3 proof of `finite-kernel-nonrf-has-central-prime-reduction`.

  I spot-checked the reduction's first two assertions. `R(E) <= K` because `H` is residually finite. `R(E) <= Z(K)` because the finite-index normal subgroup `C_E(K)` contains `R(E)`.

## 6. `vertex-mismatch-needs-nonextendable-clifford-orbits` (25a77f4f3): PASS

Checked against its route, and against `stable-vertex-mf-trace-models-need-inequivalent-marginals-proof`, whose steps 1–2 it reuses.

- **Item 1.**
  - For `t ∈ P_Γ`, the image of `t` conjugates `L_n` into itself.
  - A conjugate of a compact Lie group has the same dimension and the same number of components. So `tLt^(-1) ⊆ L` forces equality.
  - The normalizer is closed, and it contains the image of the group generated by `P_Γ`, which is `G`. That image is dense in `K_n`, so the normalizer is `K_n`.
  - Each `π^i(k)` intertwines `π^i|_L` with its `k`-conjugate, so the multiplicities are `K`-invariant.
- **Item 2.**
  - Steps 1–2 of the parent give a polar intertwiner `V` whose support and range have normalized coranks at most `η^2`, with `η = δ_n/ε`.
  - The two restrictions differ only on the complements, so `μ_n <= 2η^2 d_n`.
- **Item 3.**
  - `V ⊕ 0` intertwines the padded restrictions on subspaces of corank at most `η^2 d + m`.
  - Cancellation of finite-dimensional representations completes it to a unitary within `O(η + (m/(d+m))^(1/2))` of 1 in normalized HS norm.
  - The exact model `τ_n` of `D = G *_Γ G` then has traces within `2l||U − 1||_2 + 2m/(d+m) + o(1)` of those of `σ_n`, on words of length `l`.
  - If `m_n/d_n → 0` along a subsequence, `D` would be maximally almost periodic, against the parent's hypothesis.
- **Item 4.**
  - `K_0` is connected and acts continuously on the discrete dual of `L`, so it fixes every class. Inertia groups `S` therefore have finite index.
  - For extendable `ω`, `Res_L Ind_S^K ω~ = ⊕_(k ∈ K/S) ω^k` contains each orbit member once. These induced representations of `K` are representations of `G` through the dense image.
  - The cost is `Σ_O |Δ(O)|·|O|·dim ω <= μ_n`.
- **Assembly.** Suppose `Δ_n` vanished on the non-extendable orbits infinitely often. Then item 4 would cancel everything at cost `<= 2η^2 d_n = o(d_n)`, against item 3.
- **Wording.** Item 3 says "total dimension `m_n`", while the proof uses `dim ρ^1 = dim ρ^2 = m`. Equivalence forces equal dimensions, so `m_n/d_n → 0` means the same thing on either reading.

## 7. `leavitt-algebra-has-no-unital-rank-model` (973727ddf): PASS

Agrees with the independent check in §6 of `gk-vf-linear-verification-2026-09-12.md`.

- **Rank ultraproducts are directly finite.**
  - Over any field, `rk(1 − ab) = rk(1 − ba)`.
  - The map `v ↦ bv` sends `ker(1 − ab)` into `ker(1 − ba)`, because `(1 − ba)bv = b(1 − ab)v`. It is injective there, because `v = a(bv)`. The same holds with `a` and `b` swapped.
- **Contradiction.**
  - `L_(F_2)(1,2)` is simple, so every unital homomorphism out of it is injective.
  - In it, `t_0 s_0 = 1` while `s_0 t_0 = 1 − s_1 t_1 ≠ 1`. Direct finiteness of the target contradicts injectivity.
- **Corners.**
  - For an idempotent `p` and `a, b ∈ pMp`, `1 − ab = (1 − p) + (p − ab)`, and the two summands live on complementary supports. So ranks add, and `pMp` is directly finite.
  - That covers non-unital elementary-matrix models, as the route's scope remark says.
- **Characteristic.** `R` has characteristic two, so ring homomorphisms exist only into targets of characteristic two. Over other fields "any field" makes the statement vacuous, and the route says so.
