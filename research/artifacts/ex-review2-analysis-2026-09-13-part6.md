# EX review wave 2, part 6: W*-bundles over closed faces, SL_3(Z) matricial fields and congruence strong convergence (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. This part covers the census
claims of ex-tw-projection-starved-bundle (6), ex-sl3z-purely-matricial (7) and ex-cubic-division-strong-convergence (3).

**Sources.**
- Every node and route named below.
- Toms arXiv:2606.12188v2, Sections 4 and 7 and Proposition 4, as read for part 2.
- Not re-read here: Ozawa arXiv:1304.3523 (Section 5, Theorems 3 and 15) and Magee--de la Salle arXiv:2312.03220v2,
  Sections 2.2--2.4. Those quotes are the lanes' own MSI readings.

**Unreviewed prerequisites** (established, no PASS line in any review), named so later lanes can pick them up:
- `r-fibre-bundle-triviality-iff-uniform-central-halving` (Ozawa import);
- `toms-ah-counterexample-to-uniform-gamma` (Toms import). Its Theorem 5 and Proposition 4 were checked against the
  text in part 2 §2.9, so that import is at least consistent with the source.

**Roots.** `infinite-kazhdan-group-with-mf-reduced-cstar` and `sl3z-purely-matricial-field` stay open. So do
`cubic-division-lattice-purely-matricial-field`, `cubic-division-congruence-representations-converge-strongly` and
`nontrivial-w-star-bundle-with-r-fibres-exists`. Every claim below is either a necessary condition, a reformulation, or
a no-go for one mechanism.

## 6.1 `block-balanced-towers-have-central-halving`: PASS

- **The projections.** p_j = μ(Σ_{b ≤ ⌊L_j/2⌋} e_b) commutes exactly with μ_m(A_m) for m ≤ m_j. The union of those images
  is dense, so ‖[p_j, a]‖ → 0 in norm.
- **Traces.** Every trace of A restricts to A_{n_j}, so τ(p_j) = ⌊L_j/2⌋/L_j.
- **Splittings.** Orthogonal ranges give e_b φ^{(b′)}(a) = δ_{bb′}φ^{(b)}(a) = φ^{(b′)}(a)e_b. Point traces give
  τ(e_b) = rank e_b / rank q_n.
- **Toms instances.** Checked against the part 2 text. φ_i = π_1*(·) ⊗ γ_1 ⊕ π_2*(·) ⊗ γ_2 has two blocks of rank d_i. In
  Proposition 4, ψ^top and the point evaluations are blocks of rank rank(s_i). Composites multiply the block counts.

## 6.2 `closed-extreme-trace-sets-give-r-fibre-w-star-bundles`: PASS

- **Face.** The barycentres of Prob(K) give F = conv‾(K), and Milman's converse gives ∂_eF = K. The face property:
  tμ_{τ′} + (1−t)μ_{τ″} is maximal and represents τ ∈ F. Choquet uniqueness puts it on K, so τ′ ∈ F.
- **Bundle.** Ozawa's Section 5 framework applies to a closed face with closed boundary. For nuclear A with no
  finite-dimensional representation, every extreme fibre π_λ(A)″ is an injective II_1 factor, hence R.
- **Dictionary.** Constant matrix units in a trivial bundle lift through ℓ^∞(A)/c_F, by order zero projectivity. That
  gives λ(1 − ψ_m(1)) → 0 uniformly on K.

## 6.3 `central-halving-trivializes-every-closed-bauer-face-bundle`: PASS, one unreviewed import

- **Central sequence.** The images of p_n in M_K are asymptotically projections with E(p_n) → 1/2 uniformly.
  - For contractions, ‖[p_n, x]‖_{2,u} ≤ ‖[p_n, a]‖_{2,u} + 2‖x − a‖_{2,u}.
  - The unit ball of A is ‖·‖_{2,u}-dense in that of M_K, so (p_n) is central in M_K.
- **Triviality.** Ozawa's Theorem 15, (ii) ⟹ (iii), through `r-fibre-bundle-triviality-iff-uniform-central-halving`.
  No balancing hypothesis is needed, because factoriality of the fibres supplies it.
- **Model test.** C([0,1]) fails CH, since p_n(x) would have to be near both {0, 1} and 1/2.

## 6.4 `hopf-doubling-tower-has-no-m2-but-divides-unit-tracially`: PASS

- **No square subbundle.** In H*((S²)^M; F_2) = F_2[e_1, ..., e_M]/(e_c²), every positive-degree class squares to 0.
  - Cross terms vanish mod 2, and each monomial contains some e_c.
  - So c(F ⊕ F) = c(F)² = 1, and c(G) = c(q_n) = ∏_c(1 + e_c).
  - The degree-2M term e_1⋯e_M ≠ 0 forces rank G ≥ M = rank q_n, so F = 0.
- **The limit.** M_2 is semiprojective, so a nonzero *-homomorphism M_2 → A comes from some A_n, which is impossible.
- **Face divisibility.** The tower is block-balanced (two blocks of rank 2^{n−1}), nuclear, and has rank q_n → ∞ with
  injective maps. §6.1 and §6.3 then apply.

## 6.5 `tensor-tower-bundle-trivial-iff-tails-softly-split`: PASS

- **Bauer.** A is a continuous field over X̂ whose fibres are infinite tensor products of matrix algebras with unique
  trace. So T(A) = Prob(X̂).
- **(⟸).** p = 1 ⊗ h ∈ A_m commutes exactly with A_n ⊗ 1, with pointwise trace bounds. That is condition (ii).
- **(⟹).** The identity x − 1 ⊗ Φ(x) = d^{-1}Σ_α Σ_{ij} e^α_{ij}[f_α e^α_{ji}, x] was re-derived.
  - Σ_{ij} e_{ij}[e_{ji}, x] = d·x − d(1 ⊗ tr x), using that f_α is central in A_m.
  - So ‖p_j − 1 ⊗ Φ(p_j)‖_{2,u} → 0, and h = Φ(p_j) is a soft half splitting.
  - Bauer point traces make the 2,u-bounds pointwise.
- **General position.** A complex bundle of rank R over a d-dimensional base has a trivial subbundle of rank
  R − ⌈d/2⌉.

## 6.6 `toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces`: PASS, one unreviewed import

- **Central halving** follows from §6.1 with the block ranks of §6.1. §6.3 needs nuclearity and no finite-dimensional
  representation, which Toms records for these towers.
- **Failure of uniform Γ** comes from `toms-ah-counterexample-to-uniform-gamma` (unreviewed import, consistent with the
  part 2 reading).
- **The infinite-dimensional face.** The branch traces with z_{i+1} = (z_i, z_i, ℓ_i) have point masses at every stage,
  so they are extreme.
  - The map (z_1, ℓ_1, ℓ_2, ...) ↦ trace is continuous, since each stage uses finitely many coordinates.
  - It is injective, since z_n determines ℓ_{n−1}. So it is a homeomorphism onto a closed set.
  - ∏ CP^{j_i} contains a Hilbert cube.

## 6.7 `pmf-permanence-amenable-kernel-without-exactness`: PASS

- **Matrix coefficients.** Strong convergence σ_n → λ_Q amplifies to matrix coefficients, because the corona embedding
  of C*_r(Q) is isometric on M_d. So ‖(id ⊗ σ_n)(x_{N,z})‖ → ‖(π_N ⊗ λ_Q∘p)(z)‖.
- **Upper bound.** Fell absorption gives π_N ⊗ Ind_A^G 1 ≅ Ind_A^G(π_N|_A). The quasi-regular π_N|_A ≺ λ_A because A is
  amenable, and induction preserves weak containment. So ‖ρ_{N,∞}(z)‖ ≤ ‖λ_G(z)‖.
- **Lower bound.** 1_{A_N} → δ_e pointwise gives λ_A ≺ ⊕_N π_N|_A. The norms increase with N, so their limit is
  ‖λ_G(z)‖.
- **Diagonal.** Diagonalize over an ℓ¹-dense sequence. Finite image is preserved.
- Exactness is never used, and the model test for A = F_2 is correct.

## 6.8 `affine-sl2z-purely-matricial-field`: PASS

- **Free subgroup.** Γ(2) = {±I} × F has index 6, so the Sanov subgroup F is free of index 12.
- **Induction.** Bordenave--Collins random permutations (import) are PFF for F. Induction to SL_2(Z) preserves strong
  convergence through matrix coefficients.
- **Permanence.** §6.7 with A = Z² and A_N = N!Z², which is invariant with trivial intersection. GL_2(Z) is handled by
  a second induction.
- **Relative (T).** It is classical for (Z² ⋊ SL_2(Z), Z²) (import), so the group is not Haagerup.
- The literature-status sentences quote survey statements and are phrased as such.

## 6.9 `sl3z-pmf-iff-affine-kazhdan-group-pmf`: PASS

- **(⟹)** §6.7 with A = Z³.
- **(⟸)** ℓ²(P) splits into right cosets of SL_3(Z), so λ_P restricted to C[SL_3(Z)] has the regular norm, and
  restriction preserves strong convergence.
- **MF.** C*_r(SL_3(Z)) ⊆ C*_r(P) with MF heredity. The forward direction replaces σ_n by an MF embedding; only
  amplified isometry is used.
- **Structure.** P = Z³ ⋊ SL_3(Z) has (T) (import), and it is the index-2 subgroup of Z³ ⋊ GL_3(Z) = P_{3,1}(Z).

## 6.10 `mdls-obstruction-is-affine-mechanism-plus-level-matching`: PASS, MdlS quotes not re-read

- **Step 2.** Transitivity on primitive vectors moves ξ to (0,0,1).
  - The Heisenberg group with entries (2,3), (3,4), (2,4) lies in P_r and preserves V_χ, with z trivial.
  - Conjugating with the coordinate-(1,2) SL_2 produces v with x trivial and y a nontrivial character.
- **Step 3.** v is fixed by N = {(2,3)}. Its G_2-translates are eigenvectors of {[0;y;z]} with pairwise distinct
  characters, since the stabilizer is exactly N. So they are orthogonal, and their sum is a nonzero G_2-invariant
  vector (Frobenius reciprocity).
- **Level matching.** The Chinese remainder theorem factorizes irreducibles, and invariants of a product of groups are
  tensor products. A factor where U_1 is invisible is pulled back from SL_3(Z/p^b) and can have no G_2-invariants
  (Deligne's representations, MdlS Example 2.2).

## 6.11 `sl3z-prime-level-invariant-witnesses-are-complete`: PASS, the p = 7 census not rerun

- **1. Non-cuspidal.**
  - The P_{1,2} Jacquet module W = ρ^{⟨e_12, e_13⟩} ≠ 0, after transpose-inverse, and W is invariant under the Levi.
  - If e_23 acts trivially on W, its normal closure SL_2(F_p) (odd p) fixes W.
  - Otherwise v with e_23 ↦ ψ ≠ 1 is an eigenvector of ⟨e_13, e_23⟩. Its character's stabilizer in B_2 is
    N = {e_12(b)}, which fixes v. Coset translates are orthogonal, and their sum is B_2-invariant.
- **2. Cuspidal.**
  - Deligne--Lusztig for the Coxeter torus: at unipotent classes (1,1,1), (2,1), (3) the Green function values are
    (p−1)(p²−1), 1 − p, 1.
  - The character vanishes where the semisimple part is non-central with an eigenvalue in F_p.
  - Nonidentity elements of Ω ≅ PSL_2(F_p) are regular unipotent (p² − 1 of them) or semisimple with eigenvalue 1.
  - So dim π^Ω = [(p−1)(p²−1) + (p²−1)]/(p(p²−1)/2) = 2. GL_3-stability gives the same for every Ω^{(t)}.
- **3. Split restriction.** F_p^×/(F_p^×)³ permutes the three constituents simply transitively, so the sum over cube
  classes is dim π^Ω = 2.

## 6.12 `sl3z-prime-level-sc-forces-congruence-sc-for-sl2z`: PASS

- **Cuspidality.** Non-cuspidal ρ_i have block-fixed vectors, while ‖λ(L_{B_2}/4)‖ < 1 (Kesten). So ρ_i is cuspidal for
  large i.
- **Restriction to the block.** χ_π restricted to diag(g,1) is (p−1)(p²−1) at 1, 1 − p at nontrivial unipotents, and 0
  otherwise. That matches (Reg − Ind_U 1)(g): at a unipotent u, Ind_U 1 counts the p − 1 nonzero fixed vectors; at −u
  and at non-central semisimple elements both sides vanish. So every nontrivial σ occurs with multiplicity
  dim σ − dim σ^U > 0.
- **Cubic twists.** diag(g²,1,1) acts on B_2 by an inner automorphism times a central one, so it fixes each σ. Each
  constituent carries a third of each multiplicity.
- **Norms.** The norm is the maximum over constituents, which gives ‖l²_0(SL_2(F_p))(z)‖, and regular norms restrict.
  The payoff is stated as forced, not proved.

## 6.13 `sl3z-prime-level-sc-needs-cubic-chebotarev-primes`: PASS

- **Witnesses.** H_m ⊇ diag(m,1,1)Sym²(Γ(m))diag(m,1,1)^{-1} is nonamenable and reduces onto Ω^{(m)} for p ∤ 2m
  (strong approximation for Γ(m)). The block-diagonal Kesten element y_M has ‖λ(y_M)‖ < 1 and ‖ρ(y_M)‖ = 1 whenever
  some witness fixes a vector.
- **Consequences for large i.**
  - Cuspidal (§6.11.1), and split restriction via H_1, so p_i ≡ 1 mod 3.
  - By §6.11.3 the set E_i of missed cube classes is not everything, but it contains the classes of every m ≤ M².
  - A non-cube m ≤ M would give classes 1, m, m², all ≤ M², and fill all three classes.
- The node is correctly marked a necessary condition, not a refutation.

## 6.14 `congruence-sc-fails-along-levels-with-recurring-divisor`: PASS

- π_M ⊆ π_N for M | N.
- A nonzero finite-dimensional σ ≺ λ would give 1 ≺ σ ⊗ σ̄ ≺ λ by Fell absorption, contradicting nonamenability.
- A group-ring witness z with ‖σ(z)‖ > ‖λ(z)‖ + ε then persists along every level divisible by M.

## 6.15 `cubic-division-congruence-sc-descends-to-thin-subgroups`: PASS, strong approximation imported

- **Onto mod p.** Zariski density comes from `cubic-division-lattice-subgroups-are-zariski-dense`, which has a PASS.
  Matthews--Vaserstein--Weisfeiler and Weisfeiler strong approximation make H → SL_3(F_p) onto for p ∉ P_H.
- **Identification.** Γ_D/Γ_D(p) = H/H(p) as H-sets, and regular norms restrict across right cosets.
- **Kesten.** 2√3 for F_2.
- **Part 4.** Take H_z generated by supp z. If H_z is amenable, weak containment bounds the norm. Otherwise the
  hypothesis applies. The lower bound is automatic.

## 6.16 `cubic-division-congruence-sc-forces-asymptotic-laplace-gap`: PASS

- **Torsion-free.** φ(n) | 3 with φ(n) even for n ≥ 3, and Nrd(−1) = −1.
- **Parts 1--2.** R_π(f) = Σ_{γ ∈ E_f} a_γ ⊗ π(γ) with continuous Hilbert--Schmidt kernels, and finite-rank truncation
  lands in M_n(C[Γ]). Amplified strong convergence gives part 1. Lower semicontinuity of σ ↦ ‖σ(f)‖ in the Fell
  topology, plus compactness, gives part 2.
- **Part 3.** The Harish-Chandra eigenvalue ‖ρ‖² + ‖Im ν‖² − ‖Re ν‖² with Re ν ≠ 0 defines a compact non-tempered
  spherical family. The new part has no trivial constituent. The spherical theory is an import.
- **Hedge.** The "known tools do not give this" sentence is flagged in the node as from memory only.
