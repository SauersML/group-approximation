# EX review, analysis lanes, part 3 (2026-09-13)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0. Main tip at
review time: `1d67b356c`.

## 1.5 ex-uct: the cyclotomic structure of Z_p-actions on O_2

None of these claims decides Problem II. They constrain what a witness can look like, and the
UCT root `nuclear-algebra-without-uct-exists` stays OPEN with no firing route (part 2, §2).

### `order-p-automorphism-kk-cyclotomic-structure` (fffff736b8): PASS

Re-derived.
- **Mapping torus.** Put `Φ(u) = z·v`. It is covariant, and injective through the equivariant
  faithful conditional expectations. The image is `{f : f(ωz) = σ(f(z))}`: Fourier coefficients
  satisfy `σ(d_m) = ω^m d_m`, so they lie in `C·v^m`, and Fejér means converge. Restricting to an arc
  gives `M_σ`.
- **Contractibility.** `0 → SD → M_σ → D → 0` has the cp lift `(1−s)d + sσ(d)`, so it is semisplit.
  So KK(E, M_σ) = 0 for every E.
- **1 − t is a unit.** Kasparov's Pimsner--Voiculescu sequence in the second variable makes
  `1 − β_*` bijective on KK^*(E, C). Right multiplication by `1 − t` on R is then bijective, and the
  two-sided argument makes `1 − t` a unit.
- **Arithmetic.** `t^p = 1` gives `Φ_p(t) = 0`. Every `1 − t^k` divides the unit `1 − t` inside the
  commutative Z[t], and `p = ∏(1 − t^k)`.
- **Model tests.** Both are right: the cyclic shift on C^p, and Barlak--Szabó's `γ` giving the
  rank-one free module.
- **Trust surface.** Kasparov's KK form of Pimsner--Voiculescu, whose theorem number was not re-read.

### `o2-zp-crossed-products-invert-p-in-kk` (fffff736b8, 94e542bb2a): PASS

- Takai duality for finite abelian groups gives `C ⋊_β Z_p ≅ O_2 ⊗ M_p`.
- `[id_{O_2}] = 2[id_{O_2}]`, since `a ↦ s_1 a s_1^* + s_2 a s_2^*` is approximately unitarily
  equivalent to `id`. So KK(O_2, O_2) = 0, and the theorem applies.
- **[1_C] = 0.** `β` is unital, so `(1 − β_*)[1_C] = 0`, and `1 − β_*` is invertible.
- The proof route restricts the established content to the three bullets and the module
  statement. Consequences 1--3 are commentary, and consequence 3's quasi-free formula is flagged as
  not re-derived. That matches the text.

### `o2-zp-crossed-products-absorb-uhf-p-without-uct` (5042f4822d): PASS

Re-derived.
- **Admissibility.** Meyer--Nest Lemma 2.7 holds with `φ_m = id_C ⊗ E_m`, where E_m is the
  trace-preserving conditional expectation. The maps converge pointwise, exactly on the algebraic
  tensors and hence everywhere.
- **Milnor sequence.** It follows from Proposition 2.6's triangle and countable additivity.
- **Tower.** Under Morita equivalence the connecting maps are multiplication by `p`, which is a unit
  of KK(C, C). So lim¹ = 0 and `ι^*` is bijective for every D, and Yoneda makes [ι] invertible.
- **Item 2.** It uses Kirchberg--Phillips in KK form, which needs no UCT, together with Barlak--Li
  II's derivation that C is Kirchberg for outer α. Neither theorem number was re-read; the node says
  so.
- **Repair of Barlak--Li II Theorem 4.16, (i) ⟹ (ii).** Correct as stated: item 1 is exactly the
  membership in the class that (i) quantifies over.

### `zp-algebras-with-contractible-restriction-are-cyclotomic` (f8d569a7ab): PASS

Re-derived.
- The semisplit disc extension, together with equivariant Bott periodicity for the complex
  representation `C_χ`, makes `C(S^1)` with free rotation the cone of the Euler class `1 − χ`, up to
  a unit and a sign. The node notes the convention caveat, and it is harmless:
  `1 − ζ^{-1} = −ζ^{-1}(1 − ζ)`.
- **Mayer--Vietoris.** Two arcs, each a union of p translates, give induced pieces. The adjunction
  `KK^G(Ind X, E) ≅ KK(X, Res E)` makes each piece contractible once Res D ≃ 0. The partition of unity
  makes the extension semisplit, so `C(S^1) ⊗ D ≃ 0`.
- So `1 − χ` acts invertibly, `ρ` acts as 0, and p is a unit.
- The model test `D = C(G)` is right.

### `bootstrap-zp-actions-realize-every-cyclotomic-k-module` (9492e7cb16): PASS as a derivation from the imported statements

- **Trust surface.** Meyer--Nadareishvili arXiv:2604.12529v2: §2.3, Theorem 2.7, Definition 2.8,
  Theorems 2.9 and 2.10, Proposition 5.1. These state Köhler's UCT. The lane quotes them from a
  ghostscript extraction, and I did not re-read them.
- **Item 1.** U(A) is exact (Theorem 2.9). `Q_0 = K_*(Res A) = 0` is uniquely p-divisible, so
  Proposition 5.1 gives `A_X = A_Y = 0` and `Q = Q(0, 0, M)`.
  - The vertex bookkeeping argues that `p · 1_2 = N(t_2) + N(s_2)` is incompatible with
    `End(C(Z/p))` of rank p, so vertex 2 is `C_p`. The relations are symmetric in vertices 0 and 1,
    so the labelling does not affect the conclusion.
- **Item 2.** The Theorem 2.7 relations check on `Q(0, 0, M)` with `α_12 = 1 − ϑ` and `α_21 = 1`.
  Exactness needs only that both are bijective, and `1 − ϑ` is a unit of O. Theorem 2.9 realizes Q in
  B^G. Res A is in the type I bootstrap class with K_* = 0, hence contractible.
- **Item 3.** Theorem 2.10's surjection lifts the isomorphism. The cone D has U(D) = 0 by the long
  exact sequence, and Res D ≃ 0. If `(O_2, α) ∈ B^G`, then D ∈ B^G and KK^G(D, D) = 0, so x is
  invertible. Conversely, invertible x puts the action in B^G.
- **The fence.** No invariant factoring through Köhler's invariant separates an action on O_2 from
  B^G. That follows correctly and is stated with its scope. The node explicitly leaves open whether a
  UCT crossed product forces B^G.

### `nuclear-algebra-without-uct-exists` edits (f8d569a7ab): PASS

The root still reads OPEN. Each new bullet cites an established node of this cluster, or an earlier
one. The phantom sentence is a correct reading of item 3, not a new claim.

The root also cites `o2-zp-cartan-fixing-*`, `bootstrap-class-zp-actions-on-o2-fix-a-cartan`,
`torsion-kk-identity-dies-after-uhf-absorption` and `gardella-rokhlin-actions-preserve-uct`. These
were landed on 09-12 between 11:20 and 17:06 by an earlier campaign, so they are outside this
review.

## 1.6 ex-k1-properly-infinite: reformulations of STW Problem LXI

### `trivial-unit-class-lxi-iff-universal-halving-homotopy` (156a949eae): PASS

Re-derived.
- **(3 ⇒ 1).** `[1_U] = 2[1_U]` through the Cuntz pair, so it is 0.
- **(1 ⇒ 2).** `C(z) = Θ(diag(z,1))` with `Θ(x) = Σ s_i x_ij s_j^*`, so `z^*C(z)` is K_1-trivial.
  Push it forward along the universal map `U → A`.
- **(2 ⇒ 3).** `[1⊕1] = [1]` for properly infinite projections gives 1⊕1 ~ 1 (Cuntz), hence a Cuntz
  pair. BRR Lemma 2.4(ii) gives `diag(u,1) ∈ U_0(M_2)`, so `C(u) ∈ U_0`.
- **Remark 3.** I checked that Blanchard's substitution maps compose to the identity on all
  generators.
- The claim correctly says only that LXI implies these; the converse is open.
- **Trust surface.** BRR Lemma 2.4(ii), not re-read.

### `o2-multiplier-extension-k1-injective-iff-unitization` (ca07feae67): PASS

Re-derived.
- `A = I + C*(S_1,S_2)` is closed, since I is an ideal of M(I). `I ∩ C*(S) = 0`, by simplicity of O_2
  and because I is non-unital.
- The Bartle--Graves section makes `U_0(A) → U_0(O_2)` a principal bundle, hence a Serre fibration.
  `π_1(U(O_2)) = K_0(O_2) = 0` (Jiang, for the unital Z-stable O_2), so the fibre `U_0(A) ∩ (1+I)` is
  path-connected and lies in `U_0(Ĩ)`.
- **(⟸)** Lift π(u) through the bundle. The remainder y is in 1 + I with [y] = 0 in K_1(A), and
  `K_1(I) → K_1(A)` is injective because `K_0(O_2) = 0`.
- **Trust surfaces.** Jiang arXiv:math/9707228 (abstract quoted) and Bartle--Graves.

### `k1-injectivity-extends-over-properly-infinite-quotients` (156a949eae): PASS on the theorem, GAP in the consequence list

**Theorem: PASS.** Re-derived.
- Lift π(u) ∈ U_0(A/I) to w ∈ U_0(A), and put y = uw^* ∈ 1 + I.
- `[y]_{K_1(I)} = δ_0([e])` for a projection e ∈ A/I, which exists by Cuntz because A/I is properly
  infinite.
- `y' = exp(2πih)`, with h a self-adjoint lift of e, is in `(1+I) ∩ U_0(A)` and realizes `δ_0([e])`.
- So `yy'^*` is K_1-trivial in Ĩ, hence in `U_0(Ĩ)`.

**GAP (citation), consequence list.** The claim says that stable, stable rank one, real rank zero and
Z-stable ideals are excluded. That needs K1-injectivity of `Ĩ` in each case, and the artifact justifies
these cases with "(Lin)" and "(Jiang)".
- Stable ideals and stable rank one (Rieffel) are standard.
- **Real rank zero.** RR(Ĩ) = RR(I), so this needs "unital real rank zero implies K1-injective". I could
  not confirm such a theorem, and the artifact gives no theorem number.
- **Z-stable ideals.** Jiang's theorem is stated for *unital* Z-stable algebras. For a non-unital
  Z-stable I, `Ĩ` is not Z-stable, so an argument or a source is needed.
- To close it: give exact theorem statements that cover unitizations, or restrict the list to stable
  ideals and ideals with stable-rank-one unitization.
- The theorem itself is unaffected.

**GAP closed by the lane (b56032c54c, 00:20 CDT).** Both the claim and the artifact now say the
following, and the correction is PASS:
- two cases are fully justified: stable ideals, via a corner embedding, and unitizations of stable
  rank one (Rieffel 1983, Theorem 10.12);
- real rank zero is covered only conditionally, on Lin's theorem as quoted in Blanchard
  arXiv:0804.4624v13, proof of Proposition 3.2 ([Lin01, Corollary 4.2.10]), and that citation is marked
  as not checked against Lin's book;
- Z-stable ideals are no longer claimed.

## 1.7 ex-kadison-kaplansky, second batch

### `selfless-projection-traces-equal-k0-trace-image` (510cea6b08): PASS

- **Lemma.** Given x = [p] − [q] with trace in (0,1), strict comparison gives q ~ q' ≤ p, so
  r = p − q' has [r] = x, and r ~ e ≤ 1_1 lies in A. The Cuntz-to-Murray--von Neumann step is the one
  verified in §1.1.
- **Corollary.** y − k[1] has trace in [0,1).
- **C_2 * C_3 example.** Correct: traces 1/2 − 1/3 = 1/6, and subgroup averages have traces 1, 1/2 or 1/3.
- **Class 3.** `zariski-dense-psl-subgroups-are-completely-selfless-citation` quotes Ozawa
  arXiv:2508.07938v8 Theorem 14 and Proposition 16 verbatim. PSL(3,R) = SL(3,R), and Borel density
  gives Zariski density of finite-index subgroups of SL_3(Z).
- Class 4, `vigdorovich-linear-selflessness`, has a citation route with `requires: []` that I did not
  re-read.

### `reduced-free-product-k0-generated-by-factor-images` (dab3891556): PASS as a derivation from Fima--Germain

The inputs are quoted verbatim from arXiv:1510.02418v3: Theorems 3.1 and 4.1, Lemma 4.10 and
Proposition 2.15.
1. x is invertible, so `x_*` is an isomorphism.
2. `K_1(C) = 0`, so the six-term sequence makes `K_1(SA_1 ⊕ SA_2) → K_1(D)` onto.
3. Lemma 4.10 transports this to `(j_1)_* + (j_2)_*`.
4. λ is a KK-equivalence, and GNS-faithful vertex-reduced equals reduced.

The consequence that the torsion-free trace conjecture passes to free products is correct.

### `free-product-kk-iff-trace-conjecture-for-factors` (dab3891556): PASS

It combines the three results above. Corollary 2, Kadison--Kaplansky for G * Z being the trace
conjecture for G, strengthens the one-directional per-group Corollary B of §1.1, and the
strengthening is correct. The (1/2)Z + (1/3)Z model test is correct.

### `selfless-real-rank-zero-iff-dense-k0-traces` (8da6fa48e8): PASS

- **Item 1** is Dykema--Rørdam II Theorem 1.5(i), quoted verbatim, with Q = {τ}, Π = all projections
  and 𝔄 = A.
  - (α) and (β) are Robert's strict comparison. Cuntz subequivalence descends to the corner:
    `e r_n e`.
  - (γ) comes from the lemma and density.
  - sr(A) = 1 comes from Robert's Theorem 3.1(ii).
- **Item 2.** I re-derived the squeeze.
  - Take y invertible with ||y − (x − c)|| < δ' < δ, and p = χ_{(−∞,0)}(y).
  - A vector in `ran P_- ∩ ran(1−p)` would give `0 ≤ ⟨yξ,ξ⟩ ≤ −δ + δ'`, so the intersection is 0.
  - Kaplansky's formula then gives `F(c−δ) ≤ τ(p) ≤ F(c+δ)`.
- For g of infinite order, λ(g) + λ(g)^* has the arcsine law.

### `torsion-free-trace-defects-are-discrete-or-real-rank-zero` (8da6fa48e8): PASS

- A subgroup of R containing 1 is (1/m)Z or dense.
- τK_0(G * Z) = S + Z = S.
- Case 2: the projection traces are k/m, which are not dense, so RR ≠ 0 by item 2 with the
  generator of Z.
- Case 3: RR = 0 by item 1.
- (b) ⇒ (a) uses only item 2's squeeze, which needs no selflessness, as the proof notes.
- The model tests with torsion are correct.

### `scalar-unitary-commutators-force-k0-trace-values` (d9acb657b1): PASS

Re-derived the de la Harpe--Skandalis determinant.
- **Rules.** Δ is additive on pointwise products, invariant under constant conjugation, and changes
  sign on inverses.
- **Homotopy invariance.** The integrability identity holds because
  `τ_*[∂_t H H^{-1}, ∂_s H H^{-1}] = 0`.
- **Loops.** Bott periodicity sends [p] to `exp(2πis)p + 1 − p`, with Δ = τ_*(p). So Δ maps
  π_1(GL_∞) onto τ_*(K_0).
- **Rotation path.** `ξ(π/2) = V ⊕ V^{-1}`, and η = ξ · (wξ^{-1}w^{-1}) ends at
  `(VUV^{-1}U^{-1}) ⊕ 1`, with Δ(η) = 0.
- **Scalar path.** Δ = nθ, so the loop ησ^{-1} gives −nθ ∈ τ_*K_0.
- **Consequences.**
  - Group unitaries give scalar commutators only when they commute, by linear independence of the
    λ(g).
  - Surjective assembly for torsion-free G forbids `A_θ → M_n(C*_r G)` with θ irrational.

### `reduced-higher-kazhdan-projection-kk-witness` (249e700056): PASS

- **Trust surfaces.**
  - Li--Nowak--Pooya arXiv:2006.09317v2, Definition 4 and Propositions 1, 5 and 7, quoted verbatim;
  - Lück, Invent. Math. 149 (2002), Theorem 0.3, quoted verbatim in
    `lueck-surjective-assembly-traces-lie-in-lambda-g-citation`.
- **Items 1--4.**
  - Items 1 and 2 are the §1.1 scalarization and the selfless lemma applied to [p_n], of trace
    β^n_(2) ∉ Z.
  - Item 3: Δ_n ∈ M_k(Z[G]) has kernel of dimension β^n_(2), a Strong Atiyah failure over Q for the
    torsion-free G.
  - Item 4 is the contrapositive of Proposition 1.
- The model tests (F_m in degree 1, and degree 0) are correct.

## 1.8 ex-uct, second batch

### `cyclotomic-class-group-counts-zp-actions-on-stable-o2` (a8481ac4e9): PASS as a derivation from the imports

- **Trust surfaces.**
  - Gabe--Szabó arXiv:2205.04933 Theorem A, quoted;
  - Meyer's realization theorem, as quoted in Meyer--Nadareishvili's introduction;
  - Köhler's UCT (Meyer--Nadareishvili Theorem 2.10);
  - stability of pointwise outerness under stabilization;
  - pure infiniteness of the crossed product.

  Only the first three are quoted, and none was re-read by me.
- **Item 1, injectivity.**
  - An O-isomorphism M → M' gives a K_p-isomorphism of Q(0, 0, M) that commutes with α_12 = 1 − ϑ and
    α_21 = 1.
  - It lifts to a KK^G-equivalence between bootstrap objects.
  - Gabe--Szabó upgrades that to cocycle conjugacy.
- **Item 1, surjectivity.** Item 2 of the parent claim realizes M. Meyer's theorem gives an outer
  action on a Kirchberg algebra. After stabilization, KK-contractibility gives B ⊗ K ≅ O_2 ⊗ K.
- **Item 2.** O is a Dedekind domain. Rank-one finitely generated torsion-free modules are
  fractional ideals. The only prime of Z[ζ_p] over p is (1 − ζ_p), which is principal, so
  Cl(O) = Cl(Q(ζ_p)).
- **Item 3.**
  - Bootstrap crossed products satisfy the UCT.
  - A fractional ideal is a finitely generated torsion-free Z[1/p]-module of rank p − 1, hence free.
  - Kirchberg--Phillips with the UCT identifies the crossed products.
  - Baaj--Skandalis duality separates the dual actions.
- **Class numbers.** h_p = 1 exactly for p ≤ 19 (Masley--Montgomery) and h_23 = 3 agree with the
  standard table, which I did not re-read either.

### `zp-restriction-and-crossed-product-detect-kk-g-contractibility` (a8481ac4e9): correctly OPEN

It has Attempts and no route. Its "why it matters" implication is correct: under the UCT for
`O_2 ⋊ G`, `x ⋊ G` is a K-theory isomorphism between UCT algebras, hence a KK-equivalence.

### `stw99-problem-ii-nuclear-uct` edit (400f743677): PASS

It adds an Attempts bullet only. The root is still OPEN, and the bullet cites the claims reviewed in
§1.5 and §1.8 accurately.
