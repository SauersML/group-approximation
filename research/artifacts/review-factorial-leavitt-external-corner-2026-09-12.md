# Independent review: factorial Leavitt models have external native corner commutants

Reviewer lane `reviewer`, 2026-09-12. `nh-leavitt-hs-stable` requested an adversarial review of `factorial-leavitt-models-have-external-corner-commutants` and its route `factorial-leavitt-models-external-corner-commutant-proof`, landed in a29f19cad. The requested checks are (a)–(c) below. The review also re-checks the central-height lemma the proof consumes, from:
- `research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md`, Sections 1–5;
- `research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md`, Section 3, (8a)–(8b);
- `research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md`, Section 5, (12);
- `research/artifacts/leavitt-regular-trace-cp-reversal-2026-09-08.md`, Section 2, (8).

## Verdict

| item | verdict |
| --- | --- |
| (a) only rounding of the native `L`-heat in the same model is used | **PASS** |
| (b) `z ∈ Z(D)`, `C ⊆ D`, `z ∈ C` ⟹ `z ∈ Z(C)` | **PASS**; the ledger (11) is not needed, see §2 |
| (c) the 6.2(a)-with-dimension-changes direction | **PASS**; the dimension-change clause inherits the corner-rounding bound, not re-read |
| central-height lemma (Section 1 of the central-height artifact) | **PASS**, including the Haar supremum-to-mean inequality |
| item 2 and the consequences | **PASS** |

**Trust surfaces.**
- The Kazhdan SOS certificate for `L` behind the heat estimates (7)–(8a) was not re-derived.
- The exact-expectation corner theorem (Section 10 of `leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md`) was not re-read. It is used only for "even allowing dimension ratios tending to one".
- The Goldbring, Kunnawalkam Elayavalli and Brown citations in the consequences were not re-read.

## 1. (a): what Section 2 of the central-height artifact uses

**Hypothesis.** Section 2 assumes one full canonical microstate sequence and rounded algebras `A_n` with `η_n = ||E_(A_n) − P_n||_(∞→2) → 0`, where `P_n` is the **native `L`-heat of that same sequence**. Nothing else is assumed. The component-selection theorem is mentioned only in the closing paragraph of Section 5, as the separate two-use argument.

**A canonical model supplies admissible data.** Given `π : H → U(∏_ω M_(d_n))` with regular trace, lift generators and words. The finitely many SOS rows have defects `ε_n → 0` along `ω`, and `t_n = min(n, ε_n^(−1/2))` is admissible along `ω`. The conclusion lives in the ultraproduct, so rounding along `ω` suffices.

**Forward defect.** `F_n = Ad(U_n) E_(A_n) Ad(U_n*)`, and `Q_n = Ad(U_n) P_n Ad(U_n*)` is the conjugated heat. All maps involved are contractions for both norms. So `||F_n E_(A_n) − E_(A_n)|| <= ||Q_n P_n − P_n|| + 3η_n`, and the heat inclusion (7) makes the first term `→ 0`. Correct.

**Reverse defect.**
- Let `y = u k_+ u⁻¹ = x_14(a)`, and let `X_n` lift `π(y)`.
- Rounding and (8b) give `E_(A_n) ≈ E_D` uniformly on the unit ball, and hence `F_n ≈ Ad π(u) E_D Ad π(u)*`.
- `k_+` lies in `K`, which commutes with `L`, so `π(k_+) ∈ D`, and `F(π(y)) = π(y)`.
- The conjugation matrix coefficient `g ↦ τ(π(y)* π(g) π(y) π(g)*)` is the indicator of `C_L(y)`, which has infinite index. So `E_D(π(y)) = 0`.
- Therefore `||E_(A_n) F_n(X_n) − F_n(X_n)||_2 → ||π(y)||_2 = 1`, and `ρ_n → 1`. Correct.

**Central-height lemma, Section 1, re-checked.**
- **The flow.** `m_ij = tr(p_i q_j)` is a balanced flow with row and column sums `t_i`.
- **Weights.** `w_i H_ij <= m_ij`, and likewise for `w_j`. Reason: with the orthonormal basis `sqrt(a_i/t_i) e^(i)_rs` of `p_iA`, `Tr_HS(P_iQ_j) <= (a_i/t_i) Σ_rs tr(q_j e_sr q_j e_rs) = (a_i²/t_i) tr(q_j E'(p_i q_j p_i)) <= (a_i²/t_i) m_ij`, where `E'` is the expectation onto the relative commutant of the block.
- **Leakages.** `α_A = Σ_ij (m_ij − w_i H_ij)` is the Haar-mean leakage, from the Schur covariance `E_u |u_i⟩⟨u_i| = w_i P_i`. So `up <= α_A <= δ²`, and `α_B − α_A = Σ_ij (w_i − w_j) H_ij <= down`. Correct.
- **Supremum-to-mean**, `ρ² <= 2α_B` (Section 2 of the regular-trace artifact):
  - `d(u) = (1/2)∫_(U(B')) ||[u,v]||²_2 dv`, because Haar averaging `Ad U(B')` is the expectation onto `B'' = B`;
  - `||[u,v]||² <= 4||v − E_(A')v||²`;
  - `∫_(U(A)) ||[u,v]||² du = 2||v − E_(A')v||²`, by `||[u,v]||_2 = ||uvu* − v||_2`;
  - so `sup_u d(u) <= 2α`;
  - the unit ball is the convex hull of the unitaries, so `ρ² = sup_(U(B)) d_(B,A)`.
  Verified line by line. In `M_2` the constant 2 is exactly the triangle inequality for the Pauli multipliers of a CP map, and it is attained for two-atom masas.
- **Median argument.** `down >= 1/4` forces tail mass `T >= 1/16`, a ramp `f` with `Var_t(f) >= 1/64`, and `Σ m_ij |f(h_i) − f(h_j)|² <= 2·up/(1 − e^(−1/16))` by stationarity. This gives (2). Correct.

## 2. (b): from `Z(D)` to `Z(C)`

- **`z ∈ Z(D)`.** Rounding identifies `E_D` with the map induced by `E_(A_n)`, so `D = ∏_ω A_n`. Then `z = [z_n]` with `z_n ∈ Z(A_n)` lies in `D` and commutes with every `[a_n]`, `a_n ∈ A_n`. So `z ∈ Z(D)`. Also `τ(z) = 0`, `||z||_op <= 1` and `||z||_2 >= 1/8`, and `[π(u), z] = 0` by (6). Correct.
- **`z ∈ C`, the exact route.**
  - `K` (the fourth-coordinate unit group) commutes with `L`, so `π(K) ⊆ D`, and `z`, being central in `D`, commutes with `π(K)`.
  - `z` commutes with `π(u)`, hence with `π(uKu⁻¹)`, and with `π(L)`.
  - `H = <L, uKu⁻¹>` by (9). Checks:
    - `uKu⁻¹` is the full unit group of the corner `q = u(1−p)u⁻¹ = diag(e,e,e,1)`, since `upu⁻¹ = diag(st,st,st,0)`;
    - `x_24(r) = [x_21(b), x_14(ar)]` and `x_42(r) = [x_41(rb), x_12(a)]` hold, using `ba = 1`;
    - `GL_4 = EL_4`.
  - So `z ∈ C`. This is the argument of Section 5 of the central-height artifact.
- **`z ∈ Z(C)`.** `C ⊆ D` because `L ⊆ H`, so `z ∈ Z(D)` commutes with all of `C`. Together with `z ∈ C`, this gives `z ∈ C ∩ C' = Z(C)`. Correct.
- **The swap ledger.** The claim's derivation routes `z ∈ C` through the commutator ledger (11) and `H = <L, w>`. That route is also valid, but it is the finite-level quantitative version. It needs the integrated-retention bounds for `K_±` and the native equality allowance for the spelling of `w`. In the ultraproduct none of this is needed: `(9)` together with `π(K) ⊆ D` suffices. **Recommendation:** cite Section 5 (`(9)` and `(12)` there) as the derivation of `z ∈ C`, and keep (11) as the finite-level remark.

## 3. (c): the 6.2(a) direction

- **What item 2 uses.** Its contrapositive: a factorial `C` excludes rounding, and so excludes `D = ∏_ω A_n` even after negligible dimension changes. So the needed direction is **6.2(a) (possibly with `m_n/d_n → 1`) ⟹ same-dimension uniform rounding of the native `L`-heat**.
- **Same dimensions.**
  - `D = ∏_ω B_n` means `E_(B_n)` induces a normal, trace-preserving map fixing `D` with range `D`, so it equals `E_D`, which is induced by `P_n` by (8b).
  - Equality of the induced maps on all bounded input sequences gives `||P_n − E_(B_n)||_(∞→2) → 0` along `ω` by the witness argument. Correct.
  - The conditions needed for (8b) are met: `ε_n t_n → 0` for the energy term in (8a), and energy decay (6) puts the range in `π(L)'`.
- **Dimension changes.**
  - If `m_n >= d_n`, the compressed maps `F_n = p_n E_(B_n) p_n` induce `E_D`. The corner theorem then rounds them to an expectation in the original corner, with error `25((m_n − d_n)/m_n)^(1/4)`.
  - If `m_n < d_n`, adjoining scalars on a vanishing-trace complement gives unital algebras.
  - This direction is what the claim uses, and it is stated correctly. The corner theorem itself was not re-read, so the clause "even allowing dimension ratios tending to one" carries it as a trust surface. The same-dimension statement does not.
- **Units.** The central-height lemma needs `A_n` unital. That is ensured in both dimension cases by adjoining scalars, as the heat-rounding artifact says.

## 4. Item 2 and the consequences

- **Item 2.** A factor has `Z(C) = C·1`, and a central `z` with `τ(z) = 0` would then be `0`, contradicting `||z||_2 >= 1/8`. Correct.
- **Unstable branch.** Every canonical model with factorial `C` is a negative 6.2(a) instance for its native corner. Correct, since it is item 2.
- **Stable branch.** If every hyperlinear `H` admits a canonical model with factorial `C`, then "no such model" is equivalent to nonhyperlinearity (a nonhyperlinear `H` has no canonical model at all). Internality of `D` in those models would exclude them by item 1. Correct as logic, and it is conditional on the open existence input, as the node says.
- **Required nodes.** The route requires `binary-leavitt-unit-group-has-tt-mod-t` for property (T). Property (T) of `L ≅ EL_3(R)` is available more directly from `elementary-group-property-t-over-free-algebras`. Either one supplies the SOS certificate's existence. No change is needed.
