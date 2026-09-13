# EX review, dynamics: part 1. Nonsofic actions, Rokhlin entropy, tree lattices

Continues `research/artifacts/ex-review-dynamics-2026-09-12.md` (verdict definitions in §0 there). Lane
`ex-verify-dynamics`.

## 2. ex-nonsofic-action-relative (db83b00ca5, 3d96d53492, 23b018d16c, ee004845a5)

| node | verdict |
|---|---|
| `howe-moore-lattice-nonsofic-action-transfers-to-mixing` (+ `-proof`; artifact parts 1–2: Theorem MT, Lemmas LC, ED, EQ) | PASS |
| `sofic-action-with-sofic-ergodic-components-is-sofic` (+ `-proof`) | PASS |
| `permutation-centralizer-blind-to-weakly-mixing-actions` (+ `-proof`); dead route `mixing-nonsofic-action-via-permutation-centralizers` | PASS. The dead route does not fire |
| `induced-actions-sofic-iff-homogeneous-action-sofic` (+ `-proof`) | PASS |
| `paunescu-orbit-equivalent-free-actions-share-soficity` (+ `-citation`) | PASS. Verbatim against arXiv:1002.0605v5, p. 3 |
| `howe-moore-property-for-simple-lie-and-p-adic-groups` (+ `-citation`) | Definition 2.6 and Theorem 1.1: PASS, verbatim. Item 2: GAP (wording), corrected forward at f606d06f01 (§2.5) |
| conditional routes into `mixing-free-nonsofic-action-of-sofic-group`, `sl3z-admits-nonsofic-action`, `simple-group-lattice-admits-nonsofic-action` | None fires, since every `requires` names an OPEN claim. One wording note (§2.5) |

### 2.1 Theorem MT

Re-derived step by step.
- **Step 1.** `Z'` is ergodic (ergodic times mixing), free (the Bernoulli coordinate), and nonsofic. For
  nonsoficity: soficity passes to factors, because a sofic embedding restricts to `A ⋊ K` (Lemma A).
- **Step 4.** Freeness of `W`: `(γh, z) = (hδ^-1, δz)` forces `δ = 1` off a null set.
- **Step 5.** `H ↷ W` is ergodic by Fubini. Howe–Moore applies to the continuous Koopman representation on
  `L²_0(W)`, and the discrete `Γ` meets compact sets finitely, so `Γ ↷ W` is mixing.
- **Step 6.** `R|X_r = R(W)` and `R|X_ℓ = R(V)`. `R|X` is ergodic, because saturations descend to `W`.
  Lemma EQ: the remainders satisfy `m(A') = m(B')`, so a positive remainder meets some `θ_j^-1(B')`
  positively, which is a contradiction.
- **Step 7.** Păunescu Theorem 1.5.

Păunescu Definition 1.4 (p. 2), Theorem 1.5 and Lemma 1.6 (p. 3) match the artifact's transcription verbatim.

### 2.2 Lemmas LC and ED

- **LC (⇐).** The 2-norm identity on words makes the substitution well defined, multiplicative and trace
  preserving on the dense ∗-algebra. Moments agree, so operator norms agree, and the map extends.
- **ED.** Word traces are affine in the measure, and the integral lies in the closed convex hull of the
  component vectors. The disjoint union with `c_j = a_j N / |Y_j|` copies averages the traces with weights
  `a_j/b`.
- **Corollary ED.** The nonsofic components do not form a `ν`-null set. Almost every component is ergodic and
  essentially free.

### 2.3 Permutation centralizer

Steps 1–5 re-derived.
1. `A` is a masa, and the permutation `w` normalizes both `D_𝒰` and `Θ(M)`, hence `Θ(A)`.
2. So `x = a u_φ`, uniquely.
3. Commutation with `σ(Γ)` gives `γ·a = a` and `γφγ^-1 = φ`.
4. The cocycle `c` is equivariant for conjugation. `c_*μ` lives on finite `Γ`-classes, and weak mixing leaves
   no finite invariant partition, so `c ≡ c_0 ∈ C_G(Γ)`.
5. `λ = 1`, because the trace of a permutation is nonnegative.

The scope sentence, about permutations outside `Θ(M)`, is accurate.

### 2.4 Induced actions

- **Product lemma.** Tensor products of sofic embeddings. Traces multiply, a diagonal tensored with a diagonal
  is diagonal, and likewise for permutations.
- **(1 ⇒ 2).** `V ≅ H/Γ × Z` via `h ↦ h^-1`, then amplification and restriction.
- **Hypothesis note.** Item 2 quantifies over all sofic seeds, while the proof assumes `W` free. That holds
  automatically, since `W → H/Γ` is an equivariant factor map and `H/Γ` is free.
- **Freeness of `SL_3(R)/SL_3(Z)`.** `{g : γg = gδ}` is empty or a coset of the proper closed centralizer
  `C(δ)` of `δ != 1`, so it is null.

### 2.5 The Howe–Moore import

- **Source.** Definition 2.6 (p. 4) and Theorem 1.1 (p. 2) match verbatim. Theorem 1.1 points to Section 4.1
  and Definition 4.23 (p. 17), which reads "Let G := G(k) ... Let G^+ := ⟨U_h ≤ G | h is a root of ∂Δ⟩ ...
  We call G^+ an isotropic simple algebraic group over the non Archimedean local field k."
- **The gap.** So the p-adic family is `G^+`. Read as `G(k)`, item 2 can fail. `PGL_2(Q_p)` has a finite
  quotient, and the characters of a finite quotient are not `C_0`.
- **Instances.** `SL_n(Q_p)` and `SL_3(F_q((1/t)))` are simply connected, so `G^+ = G(k)` there.
- **Correction.** A review note was added to the node.
- **Route note.** Step 1 of `mixing-nonsofic-action-from-simple-lattice-nonsofic-action` should take
  `H = G^+`. A lattice of a non-simply-connected `G(k)` needs a separate argument, since `G(k)/G^+` can be an
  infinite compact group in positive characteristic.

## 3. ex-nonsofic-action-entropy (3ecde705af, 577c3a94cd, d7a988a3fc, 2739e2b19a, 8b13935ba6)

| node | verdict |
|---|---|
| `sofic-free-actions-are-soe-invariant` (+ `-proof`) | PASS. Step 3 of the amplification is a sketch, with a complete alternative (§3.1) |
| `cordeiro-sofic-relation-permanence` (+ `-citation`) | statement-level import, not re-read from the source here |
| `paunescu-class-is-measure-equivalence-invariant` (+ `paunescu-class-me-invariance-proof`) | PASS |
| `product-tree-lattices-in-paunescu-class-iff-f2xf2` (+ `-proof`) | PASS |
| `product-of-tree-groups-has-factorwise-howe-moore` (+ `-proof`) | PASS. The Ciobotaru lemmas it cites were read only on pp. 1–5 and 13–17 |
| `tree-product-lattice-nonsofic-gives-mixing-nonsofic-action` (+ `tree-product-lattice-mixing-transfer-proof`) | PASS |
| `weak-containment-is-blind-to-kazhdan-fixed-algebras` (+ `-proof`); dead route `mixing-nonsofic-action-via-weak-containment-of-kun-thom-action` | PASS. The dead route does not fire |
| open `f2xf2-admits-nonsofic-action`, `f2xf2-in-paunescu-class`, `nonsofic-lattice-with-dense-projections-in-tree-product`, and their conditional routes | no false establishment |

- **3.1 Amplification.**
  - Steps 1–2 check: `ι_n` is injective and carries `R|P_n` onto `(R|V × [n]²)|ι_n(P_n)`.
  - Step 3, the cut-down, is only sketched. A complete alternative: `R_n = R|P_n ∪ Δ_(W∖P_n)` is sofic by
    Cordeiro 3.2(b). It increases with union `R`, and increasing unions are sofic (remark after Cordeiro 2.2).
  - The SOE chain is right.
- **3.2 ME invariance.**
  - The twisted actions commute, and they are free through the `G × H` Bernoulli coordinate.
  - `Z` is a factor of `Y_Z`, and `R(H ↷ Y_Z) ≅ E|D_G^Z`.
  - Amplify from `D_H^Z`, restrict to `D_G^Z`, then apply Lemma A.
- **3.3 Products of trees.**
  - `Δ_p` is simply transitive on the vertices of `T_p`.
  - `K_p` is torsion free, since the conjugates of `s_i` map to `e_i`.
  - Kurosh makes `K_p` free, and `F_a` has index `a - 1` in `F_2`.
- **3.4 Factorwise Howe–Moore.**
  - The weak limit `E` of the commuting unitaries `π(g_n)` is normal.
  - `π(g_n^-1 u_+ g_n) v → v` in norm gives `π(u_+) E = E`. Symmetrically, `E π(u_-) = E`.
  - `E` is normal, so `ran E` and `ran E^*` have the same closure. That closure is fixed by `U^+` and `U^-`,
    hence by a group containing `G_1 × {e}`.
  - A topologically simple closed subgroup of `Aut(T)` is type preserving, so Corollary 4.18 applies.
- **3.5 Tree-product transfer.**
  - Nonsoficity moves through SOE.
  - Factor ergodicity comes from two facts. The mean `F_0` is invariant under the dense `p_2(Γ)`. The rest is
    killed by the mixing Koopman representation along `γ_n → ∞` with `p_2(γ_n) → e`.
- **3.6 Weak containment.** Approximate `1_(A_0)` by `1_B` with `ν(gB Δ B) < δ` on a Kazhdan set. Then
  `‖π(g)v - v‖ < (2δ/(α(1-α)))^(1/2)`.

## 4. ex-bernoulli-positive (26c156968e, 781800afec, 433c5db36c, a1e1bf7e3c, 9c34e9e7f5, 8e8c53cea1)

| node | verdict |
|---|---|
| `seward-approximate-bernoulli-models-and-semicontinuity` (+ `-citation`) | PASS. Corollary 6.1 (text line 1288) and Lemma 6.2 (line 1358) of arXiv:1501.03367v4 match verbatim |
| `rokhlin-entropy-is-the-bernoulli-approximation-threshold` (+ `-proof`) | PASS. Uses Seward II Theorem 1.10 (baseline import, not re-derived) |
| `semicontinuous-invariants-blind-above-rokhlin-supremum` (+ `-proof`) | PASS |
| `bernoulli-isomorphism-collapse-set-is-a-subgroup` (+ `-proof`) | items 1–7 PASS (§1.5) |
| OPEN `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`, `zero-rokhlin-supremum-forces-bernoulli-collapse`; routes `collapse-above-rokhlin-supremum-gives-bernoulli-collapse`, `collapse-above-supremum-gives-zero-supremum-collapse`, `leavitt-zero-supremum-and-collapse-give-bernoulli-failure`, `positive-rokhlin-via-classification-and-collapse` | No false establishment. Every route requires an OPEN claim, and `leavitt-units-have-zero-rokhlin-entropy-supremum` is OPEN, with four conditional routes |

- **Threshold.**
  - Item 2 is upper semicontinuity along models `ν_n` isomorphic to `X`.
  - Item 3 covers the infinite case through the empty infimum.
  - AINV ⟹ INF: take `s < H(λ) < H(κ)`.
  - AINV ⟹ INV: the reduction from an infinite base, `(L × M)^G ≅ (K × M)^G ≅ K^G ≅ L^G`, checks.
- **Semicontinuity.** One-sided approximation gives monotonicity. Two-sided approximation above `s` gives
  constancy.
- **The reformulation on the open claim is right.** `L^G ≅ K^G` iff `K^G` has a generating partition with law
  `λ` and independent translates.

## 5. ex-rokhlin-lower (a564fb2cfc, 142d6e141e, eed9297d75)

| node | verdict |
|---|---|
| `factors-fixed-by-large-finite-subgroups-have-zero-outer-entropy` (+ `-proof`) | PASS. The credit is correctly moved to Alpeev–Seward Theorem 1.11(ii) |
| `alpeev-seward-stabilizer-growth-kills-outer-entropy` (+ `-citation`) | citation not re-read from the PDF here |
| `kun-thom-wreath-actor-subgroups-are-not-co-amenable` (+ `-proof`) | PASS |
| `kun-thom-wreath-bernoulli-rokhlin-maximal` | OPEN root; landing added Attempts only |

- **Zero outer entropy.**
  - `μ(B ∩ M) = μ(B)/|T|`, because `B` is `T`-invariant.
  - `H(α) = H_2(1/|T|) + H(β)/|T|`.
  - `B = ⊔_t t.(B ∩ M)` gives generation.
  - Subadditivity with `h(X|F) <= h^Rok(X)` gives the equality.
- **Co-amenability.**
  - `V` is infinite: a finite nonzero `V` would have finite orbits.
  - Translation invariance gives `m({0}) = 0`.
  - (T) excludes an invariant mean on a `G`-set whose orbits are all infinite.

## 6. ex-tree-lattice-mixing (4c5d1a7d34)

| node | verdict |
|---|---|
| `induced-lattice-action-mixing-forces-c0-homogeneous-space` (+ `-proof`) | PASS |
| `radu-lattice-induced-actions-are-never-mixing` (+ `-proof`) | PASS, given the relations of `radu-bmw-lattice-embeds-in-titz-witzel-kernel` and `radu-horizontal-projection-kills-delta-squared`, not re-derived |

- **Mixing criterion.**
  - Write `l_n = λ_n c_n` with `c_n` in a compact set. Every subsequence has a further subsequence along
    which the coefficient tends to `0`.
  - The Bernoulli part is `⊕ Ind_(K_F)^L 1`, with `K_F` finite. That sits inside the regular representation,
    whose coefficients are `C_0`.
- **Radu's lattice.**
  - `a` and `b` fix `xA, yA, zA`, and `c` swaps `xA, zA`. So the closure of the vertical projection is locally
    intransitive.
  - `{h : hNh^-1 ⊆ N}` is closed and contains the dense `p_v(Γ_R)`, so `p_v(Λ_v)` is normal in `H_v`.
  - Both envelope cases violate the criterion.

## 7. ex-bernoulli-negative, later landing (74c6402170)

| node | verdict |
|---|---|
| `bernoulli-classes-meager-on-central-locally-finite-hosts` (+ `-proof`) | PASS, one local fix |

- **What checks.**
  - `h(·|P, Q) = inf_m H_m/|F_m|` is upper semicontinuous, and the Rokhlin-distance bound makes
    `E = {h(·|P) = 0}` a `G_δ`.
  - The generalized shifts over `Γ/K_n` have zero entropy along `P`, because `P` is central and `[P : K_n]` is
    finite.
  - Weak containment runs through `Coind_F^Γ` and Abért–Weiss.
- **Fix.** In Steps 3b and 3c, the window coincidences `γ s K = γ' s' K` involve `γ'^-1 γ ∈ W^-1 W`. Generate
  `F` by `K_n ∩ S~^-1 W^-1 W S~`, and choose `n` with `K_n ∩ S^-1 W^-1 W S ⊆ {1}`. The set stays finite, and
  nothing else changes.

## 8. ex-lattice-space-action (05d4563791, e3d75e3d00)

| node | verdict |
|---|---|
| `finite-equidistributed-orbits-give-sofic-action` (+ `-proof`; artifact §2, Theorem P) | PASS |
| `sl3z-lattice-space-action-is-sofic` (+ `-proof`; artifact §3, part 2 §§4–6) | PASS |
| `sl3z-lattice-space-action-is-not-sofic` [REFUTED], with `refuted_by: [sl3z-lattice-space-action-is-sofic]` | PASS. The conditional routes `sl3z-nonsofic-action-from-lattice-space-action` and `mixing-nonsofic-action-from-sl3z-lattice-space-action` can never fire |

- **Theorem P.**
  - Operators on `V_k × W_k` multiply factorwise, so a word becomes `(1_(B_w ∩ V_k) π_k(h_w)) ⊗ S_w(σ_k)`,
    with trace `ν_k-fraction · tr S_w(σ_k)`.
  - `B_w` has `μ`-null boundary, because translates by `μ`-preserving homeomorphisms keep boundaries null.
  - Vague convergence to a probability measure is weak convergence, so the Portmanteau theorem applies.
  - The sofic factor gives `tr S_w(σ_k) → δ_(h_w,1)`.
- **Lemma S1.**
  - `Z[1/p] ∩ Z_p = Z`, so `Δ ∩ (G × K) = Γ`.
  - Strong approximation, `SL_n(Z) → SL_n(Z/p^m)` onto, makes `Γ` dense in `K`.
  - `H = KΔ` because `Kh` is open and `Δ` is dense.
- **Lemmas S2–S3.**
  - `D × K` is a fundamental domain for `Δ`.
  - `π` is well defined because two choices `γ, γ' ∈ Kh` differ by `K ∩ Δ = Γ`.
  - `Φ_a` is constant on `U`-cosets, `U = K ∩ a^-1 K a`.
  - Its image is in `Γ a^-1 Γ/Γ`, since `K = ⊔ Uδ_j` with `δ_j ∈ Γ`.
  - The stabilizer of `a^-1Γ` is `Γ ∩ U`, so `|V(a)| = [Γ : Γ ∩ U] = [K : U]`, and `U\K → V(a)` is a bijection
    carrying Haar measure to counting measure.
- **Lemma S4.** An `H`-invariant `F` is a function of `g` alone, invariant under the dense `Δ`. So `H` is
  ergodic on `Y`, and Howe–Moore holds for `SL_n(Q_p) = G^+`.
- **Lemma E.**
  - `U^-1 U ∩ Γ = {1}` allows `U ⊆ D`.
  - `(u, ak) = (1, a)(u, k)` and `G`-equivariance of `π` bound the change by `ω_f(U)`.
  - The thickened average is `⟨λ(a^-1)F, Ψ_U⟩ → ∫ f dμ`.
- **Theorem H.** `|p^-k|_p = p^k`, so `a_k → ∞` in `H`.
- **Remark F** (not used) checks. The conditions defining `U_k` imply `m e_1 ∈ Z_p e_1 + p^k Z_p^n`, and the
  eigenvector set of a non-scalar `γ` is Haar-null among primitive vectors.
- **Model test 2.** A colouring with finite orbit is invariant under a finite-index normal `M`, and
  `g ∈ N ⊆ MΓ` forces `c(gΓ) = c(Γ)`.
- **Credit.** Equidistribution of Hecke points is classical: Clozel–Oh–Ullmo 2001, Eskin–Oh 2006. The artifact
  proves the case it needs. Its consequence, soficity, had only a bounded novelty check and may be folklore.
