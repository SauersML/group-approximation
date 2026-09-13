# EX review, backlog, part 3: percolation bridges, hidden-solved imports, Howie's tuple (2026-09-13)

Lane `ex-verify-backlog`. Index: `ex-review-backlog-2026-09-13.md`.

## 4. ex-free-bridges (b850838e74, cfec2971af, 31952c5668)

### 4.1 `leavitt-unit-groups-have-fixed-price-one`: PASS

- **The commensurated step.**
  - Given `x`, pick `l in L_j` with `l x in B_j`, a complete section of the aperiodic `R_(L_j)`.
  - Then `g_j x = (g_j l^(-1) g_j^(-1)) · g_j(l x)`, and `g_j l^(-1) g_j^(-1) in K`.
  - Markers of measure `< ε 2^(-j)` exist by Kechris--Miller 6.7.
- **Commutation over any ring.** `E_ij E_kl = δ_jk E_il` and `E_kl E_ij = δ_li E_kj`.
  - The chain `E_12 -> {E_13, E_32} -> {E_31, E_23} -> E_21` was checked pair by pair.
  - The pairs `(13,12), (32,12), (31,32), (23,13), (21,23)` all satisfy `j != k` and `i != l`.
- **The unit group.**
  - `R^x ≅ GL_3(R) = EL_3(R)`, from `leavitt-gl-equals-el-and-perfect-unit-group`.
  - A countable field is needed, so that the group is countable.
  - Then `β_1^(2) <= C - 1`.

### 4.2 The percolation threshold: PASS

Claims: `uniqueness-phase-cluster-relations-inherit-nonsoficity` and
`nonsofic-groups-have-cluster-soficity-threshold-in-pc-pu`. Route:
`nonsofic-benjamini-schramm-from-sofic-supercritical-clusters`.

- **Freeness.** `g` fixes an edge `{h, hs}` only for at most one label per vertex, so some edge is moved.
  The base measure is nonatomic.
- **Item 1.**
  - If `ξ` and `g^(-1)ξ` lie in `A_p`, then `1` and `g` lie in infinite clusters of `ω_p(ξ)`.
  - Uniqueness above `p_u` puts them in one cluster. This uses the imported trichotomy, including
    monotonicity of uniqueness.
- **Permanence lemmas**, re-checked from the artifact's operator-algebraic definition.
  - *Subrelations:* restrict `Θ`.
  - *Restriction:* a permutation that almost commutes with a diagonal projection maps all but `o(n_k)`
    points of the support into it, and can be corrected there.
  - *Amplification:*
    - `x ↦ (v_i^* x v_j)` maps onto `p M_m(1_A L(R) 1_A) p`;
    - partial isomorphisms extend inside the ergodic `R|_A`;
    - the block partial permutations assemble to a permutation up to `o` points.
  - *Free actions:* `τ(u_g) = μ(Fix g) = 0`.
- **Threshold.**
  - `R_(p') ⊆ R_p` for `p' <= p`.
  - Classes are finite below `p_c`, and also at `p_c` on nonamenable Cayley graphs (BLPS import).
  - Relations are nonsofic above `p_u`.
- **Graph status.** The reduction route requires the OPEN `some-supercritical-cluster-relation-is-sofic`.
  So `nonsofic-groups-satisfy-benjamini-schramm` stays OPEN.
- **Model test.** For sofic `G` the premise holds trivially and the theorem says nothing, which is why it
  is stated for nonsofic groups only. No nonsofic group is known to satisfy the premise.

### 4.3 Actions and subgroups: PASS

- **`nonsofic-actions-have-cluster-soficity-threshold-in-pc-pu`.**
  - `L^inf(X)` and the `u_g` generate `L(R_a)` inside `L(R_(a x B))`, and full-group elements lift. So a
    sofic `R_(a x B)` would make `R_a` sofic.
  - Above `p_u`, the unique infinite cluster identifies `R^a_p` with the restricted product relation.
- **`nonsofic-subgroup-bounds-cluster-soficity-threshold`.**
  - `H` acts freely and mixingly on `Ω`.
  - The open `S_H`-edges of the coset `H` are Bernoulli percolation on `Cay(H, S_H)`.
  - `R^H_p ⊆ R_p`.

## 5. ex-free-unused-power (c609c3bab4, dc2f7ed4d4, 3ca27ba509, 010b3d3524, 8c2f470b70, a6259edc33)

### 5.1 `sofic-coset-action-makes-amalgam-double-sofic`, established by the GKP citation route: PASS

- `b(h) = z_o^(-1) z_(h o)` is a cocycle (CDC1), so `i_1(h) = b(h) h` is a homomorphism. It agrees with
  `i_0` on `Γ`.
- The fold kernel is free on `{k_x : x != o}`: the quotient graph has two vertices and edge set `X`.
- `Φ(k_x) = z_o^(-1) z_x`. The set `{z_o} ∪ {z_o^(-1) z_x}` is a Nielsen transform of the basis of `F_X`,
  so `Φ` is injective on the kernel.
- `Φ` followed by the projection to `H` is the fold, so `Φ` is injective.
- **Import.** GKP Theorem 3.7, free case, quoted from the v3 HTML. I did not re-read it.

### 5.2 `free-group-doubles-over-any-subgroup-are-sofic` and `gkp-free-group-actions-are-sofic`: PASS

- GKP Theorem 2.19 makes the coset action sofic for every `Γ <= F`, and §5.1 applies.
- **Normal case.** `Γ` is normal in both copies, hence in `D`, and `D/Γ ≅ Q * Q`.
- For every `Γ`, normal or not, the fold kernel has rank `|F/Γ| - 1`.

### 5.3 `one-kun-thom-compressor-is-relatively-embeddable`: PASS

- **`P_A` is the ascending HNN group.** Inside `G`, the telescope `∪ t^(-j) Γ t^j` is a union of
  inclusions. The exponent map shows that `⟨t⟩` meets it trivially.
- **Tietze step.** `s = t_2^(-1) t_1` satisfies `s γ s^(-1) = t_2^(-1) β(γ) t_2 = γ`.
- **Fold kernel.** For `P_A *_Γ (Γ x ⟨s⟩)`, the quotient graph is a star: its centre is `P_A` and its
  leaves are `P_A/Γ`, with trivial edge stabilizers. So the kernel is `*_(P_A/Γ) Z`.
- **Inputs, not re-derived here.**
  - `kt-one-compressor-full-coset-action-is-sofic`, through `monomial-ascending-hnn-coset-action-sofic`.
    That route requires `ascending-hnn-action-iff-iterated-cosets`, whose own route has `requires: []`.
  - The general equivalence "double hyperlinear iff `RE/C`": items 4 and 6 of
    `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`.

### 5.4 `commuting-kun-thom-compressors-are-relatively-embeddable` and `heisenberg-kun-thom-slice-is-relatively-embeddable`: PASS at the checked steps

- **Separability (MTC2--MTC3).**
  - `A^v N^d` is a free monoid, and `EL_r(R_v) = SL_r(R_v)` by Suslin.
  - Truncating `k[N^d] -> k[x]/(x_i^M)` keeps a monomial `x^w` with `w ∉ A^v N^d` outside the image of
    `R_v`. So `SL_r(Q_M)` separates.
- **Heisenberg Ore condition.** Use the normal form `c^ρ b^q a^p`, with
  `(p,q,ρ)(p',q',ρ') = (p+p', q+q', ρ+ρ'+pq')`. Common left multiples equalize the central coordinate by
  nonnegative deficits.
- **Not re-derived.** The finite-window Schreier assembly (MTC4) was read but not re-derived line by line.

### 5.5 `opposite-transvections-are-first-nonore-relative-gate`: PASS

- `I + E_12` and `I + E_21` generate `SL_2(Z)`, and their positive monoid is free.
- **`P = E_pm ⋊ SL_2(Z)`.** The commutators `[e_il(m_+), e_lj(m_-)] = e_ij(m_+ m_-)` generate
  `EL_r(R_pm)` from the two cones.
- **(OTG2).** In a finite group, `π(A) π(Γ) π(A)^(-1) ⊆ π(Γ)` forces equality. So `π(Γ)` is normal and
  contains `π(E_pm)`.
- **(OTG3)** is the general double/`RE/C` equivalence.

### 5.6 The Steinberg and K2 chain: PASS, one justification note

**`farey-tree-lift-hits-opposite-steinberg-cycle`.**
- (FTC1) follows from the cone commutators above.
- (FTC2) lifts `SL_2(Z) = C_4 *_(C_2) C_6`.
- The word (FTC3) is killed by the Steinberg formula but is reduced in the amalgam.

**`one-opposite-steinberg-relator-does-not-close-laurent-cycle`.**
- Evaluate `R_+` at `x_1 = 1, x_2 = 0` and `R_-` at `x_1^(-1) = 1, x_2^(-1) = 0`. These agree on `R_0`.
- Then `ρ(w_1) = [e_12(1), e_23(1)] e_13(-1) = 1` and `ρ(w_2) = e_13(-1)`.

**`two-coordinate-relators-leave-stable-laurent-k2`.**
- Over a finite field, `K2 = 0` for the polynomial cones by homotopy invariance, so `E(R_±) ≅ St(R_±)`.
- The amalgam maps onto `St(R_pm)` by (PKL5).
- So `ker q ->> K2(R_pm) = (k^*)^2 ⊕ Z`, by two Bass boundaries and `K2(F_q) = 0`.
- At finite rank, `r >= d+3 >= sr + 2`, so van der Kallen's injective stability applies to all four rings.

**`stable-laurent-k2-has-minimal-three-symbol-packet`.**
- The boundary summands are generated by `{a, x_1}`, `{a, x_2}` and `{x_1, x_2}`.
- `Z ⊕ C_m ⊕ C_m`, with `m = q-1 > 1`, needs three generators: tensor with `F_ℓ` for a prime `ℓ | m`.

**`torsion-symbols-exactify-by-corners-not-infinite-symbol`.**
- `c_i^m = 1` in `St_r(R)` needs injective stability at rank `r`. It is available in the stable range.
- The spectral gap is `2 sin(π/m)`, and `1 - P_1 P_2 <= (1 - P_1) + (1 - P_2)`.
- The clock--shift pair satisfies `U V U^(-1) V^(-1) = ω^(-1)`.

**`rank-five-laurent-k2-stability-is-dimension-free`.**
- (AIP1): `sr(A) <= 3` for the two-torus ring, so `K2(r, A) ≅ K2(A)` for `r >= 5`.
- (AIP2): Sinchuk Theorem 1.1 for type `A_(r-1) ⊇ A_4`, applied one variable at a time to regular rings
  containing `k`.
- (AIP3): the naturality square.
- **Justification note.**
  - The route says: "Since the fixed-rank Steinberg kernel maps isomorphically to central stable `K2`, it
    is central as well". That inference is not valid as stated. An element that becomes central after
    stabilization need not be central in `St_r`.
  - The conclusion is true, because `K2(r, R)` is central in `St_r(R)` for commutative `R` and `r >= 3`
    (van der Kallen 1977; not re-read here).
  - (RFL4) does not need centrality: `K2(r, R_d)` is normal and generated by the three symbols. Only the
    minimality count uses centrality.
  - Corrected forward on `a1-invariance-removes-polynomial-dimension-proof`, in the landing of part 4.
- The Sinchuk quote is used as recorded from the v1 HTML. I did not re-read it.

### 5.7 `sofic-linear-weakly-sofic-chain-has-a-strict-link`: PASS

If both inclusions were equalities, weakly sofic would equal sofic, contradicting `weakly-sofic-not-sofic`.

### 5.8 The census's negative result: labelled correctly

- "No unused theorem settles a famous root" is stated as bounded by the sweeps, not as an established
  claim.
- The census also lists 18 claims whose prose says ESTABLISHED but which have no route. They are prose-only
  (the graph computes them open) and unreachable from roots. I did not repair them.

## 6. `howie-pro-p-tuple-fails-the-profinite-certificate-at-a5` (57fdcf7cf3): PASS

- The exponent-sum vectors `(-2,-3)` and `(3,5)` have determinant `-1`, so `P` is perfect.
- `z = x^2 = y^(-3) = (xy)^5` is central, and `P/<z> = D(2,3,5) ≅ A_5`. The five-term sequence gives
  `|z| <= 2`.
- Composing right to left, `XY = (1 4 3 5 2)`, and `X Y^(-1)` sends `1 -> 5`.
- The necessary condition is correct, because certificate condition (1) is non-membership in the normal
  closure (`research/artifacts/non-weakly-sofic-word-certificate.md`, line 11).
