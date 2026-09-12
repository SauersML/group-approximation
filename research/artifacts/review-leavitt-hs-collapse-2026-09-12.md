# Independent review: the Khanh collapse of the Leavitt–Steinberg fork

Reviewer lane `reviewer`, 2026-09-12. This is an adversarial review of the claims that turn the Leavitt–Steinberg fork into "`L^×` is normalized-HS stable iff `L^×` is nonhyperlinear", where `L = L_(F_2)(1,2)`:

- `leavitt-unit-hs-stable-iff-nonhyperlinear` and `leavitt-unit-hs-stable-iff-nonhyperlinear-proof` (landed f7200406e);
- `steinberg-hs-stability-equals-nonhyperlinearity`, its proof route, and the 2026-09-12 update 89511e146;
- `leavitt-steinberg-hs-stability-fork` (update 448ad75f7) and `leavitt-steinberg-hs-unstable` (update cb311d832);
- `leavitt-unit-hyperlinear-iff-projective-hs-model` and `leavitt-unit-projective-hs-lift-proof`;
- the inputs:
  - `leavitt-steinberg-map-iso-from-rank-three` (Khanh Theorem 5.4);
  - `leavitt-unit-group-finitely-presented` (Khanh Theorem 6.1);
  - `binary-leavitt-unit-group-is-simple`;
  - `binary-leavitt-unit-group-is-minimally-almost-periodic`;
  - `leavitt-gl-equals-el-and-perfect-unit-group`;
  - `pointwise-hs-stability-from-no-hyperlinear-quotient`.

## Verdicts

| claim | verdict | trust surface |
| --- | --- | --- |
| `leavitt-unit-hs-stable-iff-nonhyperlinear` | **PASS** | Khanh Theorem 5.4 (read, not refereed); simplicity via Lean theorem, axiom closure not audited here |
| `steinberg-hs-stability-equals-nonhyperlinearity` | **PASS** for this ring | its general 3 ⟹ 2 step cites Thom's central-quotient permanence, not re-verified here; moot after Khanh because `Z(U) = 1` |
| `leavitt-unit-hyperlinear-iff-projective-hs-model` | **PASS** | Khanh Theorem 4.4 at rank one (`H_2(L^×;Z) = 0`) |
| `binary-leavitt-unit-group-is-minimally-almost-periodic` | **PASS** | independently confirmed by Malcev plus simplicity (Section 3) |
| `pointwise-hs-stability-from-no-hyperlinear-quotient` | **PASS** | none |

**Bottom line.** The collapse is sound. After Khanh, `St_5(L)`, `EL_4(L)` and `L^×` are one simple, finitely presented, minimally almost periodic group. For that group, normalized-HS stability, in the strict sense or the flexible sense (they coincide here), is equivalent to nonhyperlinearity, and instability is equivalent to hyperlinearity. Instability is therefore exactly a hyperlinear nonsofic group, i.e. Q3.4. Neither side is decided.

**Normalized versus plain HS.** Every equivalence here is for the normalized trace metric `‖T‖_2 = tr(T*T)^(1/2)` with `tr` normalized by the dimension. That is the metric of tracial ultraproducts. None of it transfers to the unnormalized Frobenius norm. There, vanishing defects bound the operator-norm defect, and the relevant limit object is not a tracial ultraproduct. The graph asserts nothing about that notion. Strict versus flexible (Dogon–Vigdorovich's "HS stable" is flexible, Becker–Lubotzky's is strict) makes no difference for `L^×`: every genuine finite-dimensional representation is trivial, so a flexible correction is a compression of `1`.

## 2. The proof chain, line by line

### 2.1 Identifications

- **Khanh Theorem 5.4** (`leavitt-steinberg-map-iso-from-rank-three`): `St_r(L) → GL_r(L)` is an isomorphism for `r >= 3`. lit-groups verified the statement against the v1 PDF and read the proof chain. Its rank-5 form rests on Voronetsky's refinement isomorphism, which nobody here re-read.
- **Prefix codes.** A complete binary prefix code `w_1, …, w_k` exists for every `k >= 1`, and it satisfies `w_i* w_j = δ_ij` and `Σ w_i w_i* = 1`. So `(a_ij) ↦ Σ w_i a_ij w_j*` is a unital ring isomorphism `M_k(L) → L`, with inverse `r ↦ (w_i* r w_j)`. I re-checked the three-leaf instance written out in `binary-leavitt-unit-group-is-simple-proof`: `T_2 S_2 = t_0 t_1 s_1 s_0 = 1`, `T_2 S_3 = 0`, and `S_1T_1 + S_2T_2 + S_3T_3 = 1`. Hence `GL_k(L) ≅ L^×` for every `k`.
- **GL = EL** at every rank `>= 2` is internal: `leavitt-gl-equals-el-and-perfect-unit-group`, Lean `KOne/AllRanksElementary`.
- **Result:** `U = St_5(L) ≅ GL_5(L) ≅ L^× ≅ GL_4(L) = EL_4(L) = Q`.
- **Center.** `Z(GL_5(L))` consists of the central units of `M_5(L) ≅ L`, i.e. `Z(L)^× = F_2^× = 1` (`leavitt-center-is-coefficient-field`). So the kernel called central in the pre-Khanh fork is trivial, in agreement with Theorem 5.4.

### 2.2 The three structural inputs

- **Finite presentation.** Khanh Theorem 6.1. It follows independently from Krstić–McCool at rank 4 together with Khanh's rank-4 criterion (Theorem 5.1), which avoids Voronetsky.
- **Simplicity.** `binary-leavitt-unit-group-is-simple` identifies `L^×` with `GL_3(L) = EL_3(L)` and cites
  `RootDetectionBinary.isSimpleGroup_elementaryGroup_binaryLeavitt (hcard : 3 ≤ Fintype.card ι) : IsSimpleGroup (elementaryGroup ι (BinaryLeavittAlgebra (ZMod 2)))`.
  The statement matches. `GroupApproximation/Leavitt/RootDetectionBinary.lean` contains no `sorry`, `admit` or `axiom`, and the root `GroupApproximation.lean` imports it. **Not done in this pass:** an axiom audit of the declaration's closure. `Endpoint/OneSidedTransportAudit.lean` has `#audit_axioms` only for the Preusser variant `isSimpleGroup_elementaryGroup_binaryLeavitt_via_preusser`.
- **Minimal almost periodicity.** The recorded route kills one Thompson swap and uses characteristic-two normal generation. Independent check: a homomorphism `ρ : L^× → U(d)` has finitely generated linear image, which is residually finite by Malcev. The image is a quotient of the simple group `L^×`, so it is trivial or isomorphic to `L^×`. An infinite simple group has no nontrivial finite quotient, so it is not residually finite. Hence `ρ` is trivial. **PASS**, by two independent arguments.

### 2.3 The equivalence (`leavitt-unit-hs-stable-iff-nonhyperlinear`)

- **2 ⟺ 3.** A nontrivial homomorphism into `U(∏_ω M_(d_n))` is injective by simplicity, and a countable subgroup of that unitary group is hyperlinear. If `d_n` is bounded on an `ω`-large set, the ultraproduct is `M_d` and the homomorphism is trivial by 2.2. Conversely, a hyperlinear approximation gives an injective homomorphism. Correct.
- **1 ⟹ 2.** Correct, with one presentational gap. Stability is quantified over sequences whose relator defects tend to `0` as `n → ∞`, but the text applies it "along `ω`". The repair is standard. Pick `n_1 < n_2 < …` with `n_k` in the `ω`-large set where every relator defect is `< 1/k` and each `‖φ_n(s) − 1‖_2` lies within `1/k` of `‖π(s) − 1‖_2`. Apply stability to `(φ_(n_k))_k`. The genuine representations are trivial, so `‖π(s) − 1‖_2 = 0`. Not a logical gap.
- **2 ⟹ 1.** Correct. Negating stability gives `ε` and a sequence at distance `>= ε` from every representation, hence from `1`. The finitely many relators give a homomorphism of `Q` into the ultraproduct that is nontrivial on a generator.
- **Presentation independence.** The Tietze-move argument is the same as for P-stability. Correct.
- **External corroboration.** Becker–Lubotzky Theorem 1.3(ii): hyperlinear plus property (T) plus infinite implies not strictly HS-stable. That gives `1 ⟹ 3` independently, because `L^× ≅ EL_4(L)` is Kazhdan (Ershov–Jaikin-Zapirain, `EL_n` over a finitely generated ring, `n >= 3`; `L` is generated by `s_0, s_1, t_0, t_1`).

### 2.4 The pre-Khanh nodes

- **`steinberg-hs-stability-equals-nonhyperlinearity-proof`, step 3 ⟹ 2** uses "Thom's central-quotient permanence" (hyperlinearity passes to quotients by central subgroups). The graph pins it only in notes (`notes/EXPLICIT_LEAVITT_ATLAS.md:1541`, "Lemma 3.3 and Remark 3.4"), and it was not re-verified here. For this ring `Z(U) = 1`, so the step is vacuous and the equivalence stands without it. It becomes a live trust surface only if the node is reused for a ring where the Steinberg kernel is nontrivial.
- **`leavitt-steinberg-hs-stability-fork-proof`, unstable branch.** Its "central-cover theorem" is replaced, for this ring, by OpenAI's nonsoficity of `L^×` itself. No gap.

### 2.5 `leavitt-unit-hyperlinear-iff-projective-hs-model`

- **Trace identity.** `min_(λ∈T) ‖u − λ‖_2² = 2 − 2|tr u|`, since `‖u − λ‖_2² = 2 − 2 Re(λ̄ tr u)`. Correct.
- **Projective homomorphism.** Minimizers `λ_n → λ` along `ω` give `x(g)x(h) = λ x(gh)`, so `g ↦ x(g)T` is a homomorphism `H → U(M)/T`. Correct.
- **Lifting.** Pulling back `1 → T → U(M) → U(M)/T → 1` gives a central extension of abstract groups. Universal coefficients give `H²(H;T) = Hom(H_2(H;Z),T) ⊕ Ext(H_1(H;Z),T) = 0`, because `H_1 = 0` (perfect) and `H_2 = 0` (Khanh Theorem 4.4 at `r = 1`). So the extension splits, and the section is unique because `Hom(H,T) = 0`. Correct.
- **Nontriviality and faithfulness.** `‖x(g_0) − λ‖_2 >= c > 0` for all `λ`, so `ρ(g_0)` is not scalar. The kernel is trivial by simplicity. Correct.
- **Balanced relators and commutators.** The scalars cancel in words of exponent sum zero. Correct.

### 2.6 Known-case tests

- **Finite simple groups.** They are HS-stable and hyperlinear, but not minimally almost periodic, so the equivalence does not apply. No conflict.
- **`SL_3(Z)`.** It is Kazhdan, residually finite and hyperlinear, hence not strictly HS-stable by Becker–Lubotzky. It is not minimally almost periodic, so the equivalence does not apply. No conflict.
- **A hypothetical infinite simple, finitely presented, minimally almost periodic, hyperlinear Kazhdan group.** The equivalence predicts instability, which agrees with Becker–Lubotzky.
