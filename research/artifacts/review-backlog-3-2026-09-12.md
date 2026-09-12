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

## 8. `fournier-facio-group-carries-rigid-defect` (ba967bc03): PASS

Checked against `fournier-facio-rigid-defect-proof`, and against the import `fournier-facio-torsion-free-skeleton` (Fournier-Facio arXiv:2608.02025, Section 2).

- **Hypotheses from the skeleton.**
  - `Γ = π(P)` and `G` have (T), and `G = <Γ, t_1, t_2>` with `t_iΓt_i^(-1) <= Γ`.
  - `π|_S` is injective.
  - `J = t_1^(-1)π(S)t_1` satisfies `[Γ, J] = 1`, `Γ ∩ J = 1` and `t_1Jt_1^(-1) = π(S) <= Γ`.

  The last inclusion is the one step 2 needs, because `γ` is taken in `π(S)`.
- **Step 1.** `Γ`, `t_1` and `t_2` lie in the compression semigroup and generate `G`, so `Γ` is infranormal.
- **Step 2.**
  - `J <= C_G(Γ)`.
  - For `1 ≠ s ∈ S`, put `z = t_1^(-1)π(s)t_1 ∈ J`, so that `t_1zt_1^(-1) = π(s)`.
  - `π(S) ≅ S` is infinite, simple and nonabelian, hence centreless. So some `γ ∈ π(S) <= Γ` has `[π(s), γ] ≠ 1`.
  - With `g = t_1`, this is a nontrivial generator of `D_G(G, Γ)`.
- **Step 3.** `D_G(G, Γ)` is normal in `G`. So its intersection with `π(S)` is a normal subgroup of `π(S)`; it is nontrivial, hence all of `π(S)`.
- **Step 4.** If `Γ` were normal, `C_G(Γ)` would be normal. Every `gzg^(-1)` would then centralize `Γ`, and every generator would be trivial.
- **Consequence bullets.** The two bullets are the two directions of one implication, and both are correctly scoped. If `G` is hyperlinear, it refutes `hyperlinear-groups-kill-rigid-compression-defects` as a universal statement.

Trust surface: the Fournier-Facio preprint (unrefereed), through the skeleton import.

## 9. `cckw-ghb2-kms-group-structure` (7c34249c7): PASS as an import; the CCKW proofs were not re-read

These are the consistency checks the repo text allows.

- **Vertex groups.**
  - The relators `[a,b,a]`, `[a,b,b]` give the Heisenberg group of order `7^3`.
  - The relators `[c,b,c]`, `[c,b,b,c]`, `[c,b,b,b]` give a class-3 group with basis `c, b, [c,b], [c,b,b]`, so of order `7^4 = 2401`. Both orders match the claim.
  - "`U_4(7)`" is CCKW's name for that order-`7^4` group. It is not the 4×4 unitriangular group, whose order is `7^6`.
- **Curvature.** Half-girth type `(3,4,4)` has `1/3 + 1/4 + 1/4 < 1`. That is consistent with the CAT(−1) development and with hyperbolicity (items 1 and 3).
- **Item 4.** This is the standard fixed-point consequence of a proper cocompact action on a CAT(0) complex with a strict fundamental domain. Finite subgroups fix a point, and point stabilizers lie in conjugates of vertex groups.
- **Lean corroboration.** The citation route says items 1 and 5 are corroborated by compiled Lean on main: `hasKazhdanPropertyT_ghb7`, the relator checks, and vertex injectivity. I did not rebuild them.
- **Source.** Not re-read in this pass. The route records an MSI extraction, and lists what it did not re-read.

## 10. `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2` (7c34249c7): PASS

Checked against `ghb7-congruence-kernel-b2-euler-count-proof`.

- **Freeness.**
  - Every simplex stabilizer lies in a conjugate of a vertex group.
  - `H ∩ gX_ig^(-1) = g(H ∩ X_i)g^(-1) = 1`, because `H` is normal and `ψ` is injective on `X_i`.
- **Cell count.**
  - Take `H` normal with `H ∩ G_σ = 1`. The `H`-orbits on `Gσ` are the orbits of `G_σ` acting on `G/H` by right multiplication. That action is free, so there are `[G:H]/|G_σ|` orbits.
  - The strict fundamental domain has:
    - three vertices, with stabilizers of orders `343`, `2401` and `2401`;
    - three edges, with stabilizers of order 7;
    - one face, with trivial stabilizer.
  - So `χ(H\Y) = [G:H](9 − 1029 + 2401)/2401 = [G:H]·1381/2401`. I re-did the arithmetic.
- **Betti numbers.** `H\Y` is a finite 2-dimensional `K(H,1)`, and `b_1 = 0` by (T). So `b_2 = χ − 1`.
- **Index.** `[G:H] = |ψ(G)|` is divisible by `|ψ(X_1)| = 2401`, so `b_2 >= 1381 − 1 = 1380`.
- **`G` itself.** A proper cocompact action on a contractible complex gives `H^*(G;Q) = H^*(G\Y;Q)`. That is the cohomology of a triangle, so `b_2(G) = 0`.

Inherits §9.

## 11. `central-pullback-finite-image-center-criterion` (23510de00): PASS

Checked against `central-pullback-finite-image-center-criterion-proof`.

- **Kernels.** For `P = E ×_Q G`, the kernel of `P → G` is `A × {1}`, which is finite and central. The kernel of `P → E` is `{1} × N`. Both projections are onto, because the other map to `Q` is onto.
- **The mark is invisible.** Take any `φ : P ↠ F` with `F` finite, and put `J = φ(N)`.
  - `F/J` is a quotient of `P/N ≅ E`, and `z` lies in the finite residual of `E`. So `φ(z,1) ∈ J`.
  - `φ(z,1)` is central in `F`, so it lies in `Z(J)`.
  - `J` is a finite image of `N`, so `|Z(J)|` is prime to `p`, while the order of `φ(z,1)` divides `p`. Hence `φ(z,1) = 1`.
- **Hyperbolicity and torsion.**
  - `P` is f.g. and quasi-isometric to `G`.
  - Suppose `P` had a torsion-free finite-index subgroup. Its normal core would be a torsion-free finite-index normal subgroup, and the quotient by it would be a finite image of `P` in which `(z,1)` survives. That is excluded above.
- **Heredity.** Finite images of a quotient of `H` are finite images of `H`, so the hypothesis passes to quotients.

## 12. `hyperbolic-rf-central-prime-center-equivalence` (23510de00): PASS, inheriting three imports

Checked against `hyperbolic-rf-central-prime-center-equivalence-proof`.

- **(1) ⇒ (2).**
  - Take the infinite hyperbolic group with no nontrivial finite quotients supplied by `hyperbolic-rf-vtf-kazhdan-equivalence`.
  - Its only finite image is trivial, so (2) holds for every `p`.
  - It is non-elementary, because virtually cyclic groups are residually finite.
- **(2) ⇒ (1).**
  - `Q = Sp_4(Z)` is finitely presented.
  - Let `E_∞` be the preimage of `Q` in the universal cover of `Sp_4(R)`. Its central kernel is `<t> ≅ Z = π_1(Sp_4(R))`.
  - Deligne's theorem, as stated, puts `t^2` in every finite-index subgroup of `E_∞`.
  - In `E_p = E_∞/<t^(2p)>`, `z = t^2` has order exactly `p`. It lies in the finite residual, because finite-index subgroups of `E_p` pull back to finite-index subgroups of `E_∞`.
  - Belegradek–Osin give `1 → N → G → Q → 1` with `G` hyperbolic and `N` a quotient of `H`. So the center hypothesis descends to `N`, and §11 applies to `E_p ×_Q G`.
- **Inherited, not re-read here:**
  - Deligne (C. R. Acad. Sci. 1978);
  - Belegradek–Osin Corollary 1.2;
  - `hyperbolic-rf-vtf-kazhdan-equivalence`.

## 13. `normal-subgroups-of-arithmetic-lattices-are-congruence-open` (4433ee391): PASS; one step compressed, repair below

Checked against `arithmetic-normal-subgroup-congruence-openness-proof`, with the four standard imports (SA), (QS), (FR), (LIE) taken as stated.

- **(a) Almost all primes.**
  - Nontrivial central elements have finite order, and `Γ` is torsion-free. So `1 ≠ a ∈ M` is non-central, and it stays non-central mod `𝔭` for almost all `𝔭`.
  - `M` is infinite, since `Γ` is torsion-free.
  - For almost all `𝔭`, `Γ ↠ G(O/𝔭)` by (SA). A normal subgroup of a perfect quasisimple group that is not central is everything: if `M̄Z = G`, then `G = [G,G] = [M̄,M̄] <= M̄`.
  - (FR) lifts this to `G(O_𝔭)`.
- **(b) The tail.**
  - (SA) puts each `G(O_𝔭)`, `𝔭 ∉ S`, inside `Γ̄` as the elements whose other components are 1.
  - For such `x` and `m ∈ N`, `[m, x] ∈ N` has only a `𝔭`-component.
  - With `m_𝔭` ranging over `G(O_𝔭)`, topological perfectness gives `N ⊇ G(O_𝔭)`. `N` is closed, so `N ⊇ ∏_T G(O_𝔭)`.
- **(c) Finitely many primes: the compressed step.**
  - The route treats `⊕_𝔭 𝔤(k_𝔭)` as one Lie algebra and takes an ideal of it. When the remaining primes have different residue characteristics, that is not one `p`-adic Lie group, so the Lie correspondence does not apply to the product as written.
  - **Repair, factor by factor.**
    - `Γ̄` is open, so it contains `U_𝔭 × {1}` for an open subgroup `U_𝔭 <= G(O_𝔭)`.
    - For `m ∈ N` and `x ∈ U_𝔭`, `[m, x] ∈ N` has only the `𝔭`-component `[m_𝔭, x]`.
    - `π_𝔭(N)` is infinite and normalized by `U_𝔭`. So its Lie algebra is a nonzero ideal of the simple `Q_p`-Lie algebra `𝔤(k_𝔭)`, hence all of it.
    - The closed subgroup generated by `[π_𝔭(N), U_𝔭]` then has Lie algebra `[𝔤_𝔭, 𝔤_𝔭] = 𝔤_𝔭`, so it is open, and it lies in `N`.
    - So `N` contains an open subgroup of each remaining factor, together with the tail. Hence `N` is open.
  - `G` is absolutely almost simple, so `𝔤(k_𝔭)` stays simple over `Q_p` after restriction of scalars.
- **The consequence** is correct. Congruence quotients of `Γ/M` correspond to open subgroups of `Γ̄` containing `closure(M)`, and there are finitely many.

## 14. `leavitt-surjunctivity-tower` (49e2d072c): PASS, inheriting four inputs

- **`V <= R^x`.**
  - `V <= EL_9(R)` by `leavitt-cylinder-swaps-generate-thompson-in-el`.
  - `EL_9 = GL_9` by `leavitt-gl-equals-el-and-perfect-unit-group` (pass 2 §9).
  - `R ≅ R^n` as modules gives `M_n(R) ≅ R`, so `GL_n(R) ≅ R^x`.
- **`R^x <= A^x`.** Use the corner family of `d-ary-leavitt-groups-nonsofic-over-finite-fields`.
  - The binary family generates a copy of the simple algebra `L(1,2)`, so the map is injective.
  - `u ↦ u + (1 − e)` is injective on units.
- **Heredity** of surjunctivity along subgroups is `surjunctivity-passes-to-subgroups`, independently re-derived by gk-verify-pos.
- **"A non-surjunctive `V` is nonsofic"** is Gromov–Weiss.

The four inputs are not re-reviewed here.

## 15. `thompson-v-finitely-presented-infinite-simple` (3260355f8): PASS (classical import)

- Cannon–Floyd–Parry (Enseign. Math. 1996) records Thompson's finite presentation of `V` and its simplicity.
- `V` contains every finite symmetric group (permuting dyadic intervals of equal length), so it is infinite.

## 16. Already independently checked by gk-verify-pos; spot checks agree

These queue entries carry "Independently re-derived 2026-09-12 by gk-verify-pos: PASS" in their routes, so they got only a spot check here.

- **`leavitt-units-embed-in-their-scalar-quotient`** (aad8009fa, gk-verify-pos §24).
  - I re-did the product: `t_0 s_0 = 1`, `t_0 s_1 = t_1 s_0 = 0` and `t_1 s_1 = 1` give `ι(g)ι(h) = ι(gh)`.
  - `t_0 ι(g) s_0 = g`.
  - If `ι(g) = λ`, then `λ s_1 = s_1`, so `λ = 1`.
- **`leavitt-units-carry-nested-rigid-defect`** (d907d9ab8, §17). `u z u^(-1)` is a nontrivial element of the simple nonabelian group `EL_3(R)`, so it is noncentral there.
- **`ternary-leavitt-swap-problem-splits-at-central-involution`** (faf9c127d, with correction 7.4(e)).
  - In characteristic 3, `(2(1 ± z))^2 = 2(1 ± z)`, and the two idempotents sum to 1.
  - `d^2 = 1` and `dwd = −w = zw`.
  - Item 6 needs `b, c ∈ S_−` for `CA = 1`, since otherwise `c ε_+` survives. A solution in `S` can be replaced by `ε_− b` and `ε_− c`, because `ε_−` is central and `e_− ∈ S_−`. So nothing is lost.
- **`gottschalk-reduces-to-fg-simple-kazhdan-groups`** (a03dd1b0c, §18). The automaton splits over the cosets of `L = <M>` into copies of `τ_L`, for both injectivity and surjectivity, and the alphabet is unchanged.
- **Not spot-checked here:**
  - `countable-group-embeds-in-fg-simple-kazhdan-group` (a03dd1b0c, §18);
  - `surjunctivity-is-axiomatized-by-rectangle-clauses` (fb5e07c43, §15);
  - `positive-rokhlin-entropy-makes-leavitt-units-surjunctive` (5a2a793cd, §13).

## 17. `fpbs-twisted-level-graph-generates-cyclic-extension` (aede48402): PASS

Checked against `fpbs-twisted-level-graph-generates-cyclic-extension-proof`.

- **Return moves.** `t^(-m) s t^m = φ^(-m)(s)`, because `tut^(-1) = φ(u)`. So the path `z → t^m z → s t^m z → φ^(-m)(s) z` realizes each `G_A`-edge inside `R_(Φ_A)`.
- **Only if.**
  - A `Φ_A`-path between two points of one `N`-orbit has total `t`-exponent 0, since the action is free.
  - I re-derived the rewriting `t^(a_k)s_k ⋯ s_1 t^(a_0) = ∏_j φ^(-b_j)(s_j)`, with `b_j = a_0 + ⋯ + a_(j−1)`.
  - Each `s`-move at `t^(b_j)z_j`, forward from `A` or backward into `A`, is the `G_A`-edge `{z_j, z_(j+1)}` at level `b_j`. So the path is a `G_A`-path, and `R_(Φ_A) ∩ R_N` is exactly "connected in `G_A`".
- **Bernoulli labels.**
  - `t^m(ux) ∈ A` iff `x(u^(-1)t^(-m)) < δ`.
  - `(u,m) ↦ u^(-1)t^(-m)` is injective, by uniqueness of the normal form `ut^k` in `N ⋊ Z`. So the open pairs are independent with probability `δ`.
  - Freeness identifies the orbit with `N`.
- **Cost.** `C(b_Γ) <= 1 + |S|δ`, and aperiodic relations cost at least 1.
- **Free-group check.**
  - The edge `{u, x_(−m)u}` is present iff `(u,m)` or `(x_(−m)u, m)` is open, which has probability at most `2δ`.
  - Tree edges with disjoint endpoint sets use disjoint pairs, and there are infinitely many such edges.
  - So for `δ < 1/2` some tree edge is almost surely missing, and a subgraph of a tree missing an edge is disconnected.
  - This matches `F_2` having cost 2.

## 18. `random-complex-group-no-quotients-below-exp-pn` (1bca9dba4): PASS

Checked against `random-complex-no-quotients-below-exp-pn-proof`. Meshulam's statements are taken as quoted.

- **Expansion.**
  - `(φ_u·φ)(u,v) = 1`, so `φ_u·φ` is supported on the edges opposite `u`, and there it records violated triangles.
  - Each violated triangle is counted once at each of its three vertices. So `Σ_u ||φ_u·φ|| = 3||d_1φ||`, which gives `||d_1φ|| >= (n/3)||[φ]||`.
  - Whether a triangle is violated is gauge-invariant (holonomy is conjugated), so `||d_1φ||` is a class invariant.
- **First moment.**
  - There are at most `(n^2/2)^k |G|^k` classes of weight `k`, and each survives with probability `<= exp(−pnk/3)`.
  - So `Pr <= Σ_k r_G^k <= 2r_G` once `r_G <= 1/2`. That holds eventually for every `|G| <= N`, since `r_G <= (n^2/2)exp(−5pn/24)`.
- **Union bound.**
  - There are at most `2N` simple groups of order at most `N` (Kimmerle–Lyons–Sandling–Teague).
  - The bound `2N · n^2 N exp(−pn/3) = 2n^2 exp(−pn/12)` tends to 0 exactly when `pn − 24 log n → ∞`. I re-did the exponent arithmetic with `N = exp(pn/8)`.

## 19. `barlak-li-uct-iff-z2-z3-actions-fix-cartan` (17e477373) and `barlak-li-p-half-iff-zp-actions-fix-cartan` (b214f717f): PASS as literature imports; source not re-read here

- **Consistency of the two nodes.** Theorem 1.4 (= Corollary 4.17) is Theorem 4.16 at `p = 2, 3`, combined with Barlak–Szabó Proposition 4.16. The node for `p` records the source's 3 ⟹ 1 through Kirchberg's Theorem I and the Barlak–Szabó action `γ` with `O_2 ⋊_γ Z_p ~_KK M_(p^∞)^(p−1)`. The chain is coherent.
- **Why the primes 2 and 3 suffice.** The UCT class has two-out-of-three permanence for extensions. `A` sits in an extension with `A ⊗ M_(2^∞)`, `A ⊗ M_(3^∞)` and `A ⊗ C([0,1], M_(6^∞))`, through a dimension-drop algebra KK-equivalent to `C`. That is the standard reason two coprime primes capture every separable nuclear algebra. It matches Theorem 1.4 as quoted.
- The MSI extraction of arXiv:1704.04939v2 is recorded in the citation routes. This pass did not re-read the PDF.

## Overlap noted after landing

§4 and §5 are also discussed in `review-kazhdan-hyperbolic-hs-2026-09-12.md`, and §4 in `review-major-swarm-2026-09-12.md`. Their headers did not name those ids, so the queue filter kept them. These sections are independent second reads.
