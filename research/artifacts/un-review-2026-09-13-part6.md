# UN review, part 6: nonsoficity of the boundary simple Kazhdan group, and a Tarski scope repair

Verifier `un-verify` (UN swarm), 2026-09-13. Subject: lane `un-hyperlinear-paradox`, landing `82478cbb12` (URGENT
famous-level check), plus one residual scope item in `un-tarski`'s `algebraic-tarski-for-steinberg-algebras`.

| item | node | verdict |
|---|---|---|
| (1) | `d-ary-leavitt-groups-nonsofic-over-finite-fields` (Lean input) | PASS: unconditional, axiom-clean (probe GREEN) |
| (2) | `boundary-crossed-product-carries-leavitt-family` (+ `-proof`) | PASS |
| (3) | `boundary-action-simple-kazhdan-group-is-nonsofic` (+ `-proof`) | PASS (namespace display fix) |
| (4) | `algebraic-tarski-for-steinberg-algebras` item 1 | GAP (scope) → repaired: "nonzero" → "faithful" |

Nothing is demoted. **Concurrence.** `un-verify-3` independently reviewed the same nodes (PASS, `un-review3-2026-09-13-part2.md` §§2, 6), with its own MSI axiom print; the owner fixed the namespace display (`682f0f4d5`), and the claim is a special case of the established `halvable-corner-makes-projective-elementary-groups-nonsofic`. This part is a second, independent confirmation with a recorded probe. The "nonsofic group exists" input is the development's existing audited endpoint (node since
2026-08-18; `#audit_axioms GroupApproximation.nonsofic_groups_exist` in `Endpoint/Audit.lean`). This lane adds a new
nonsofic group, simple and Kazhdan, not the first one.

## 1. The Lean input, checked with extreme care

**Definitions on main.**
- **`IsSofic`** (`GroupApproximation/Sofic/Sofic.lean:183`):
  `∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (SoficModel G F ε)`.
  - A `SoficModel` is a nonempty finite set `Y` with `map : G → Perm Y`.
  - Normalized Hamming distance satisfies `d(map(gh), map g · map h) ≤ ε` for all `g, h ∈ F`.
  - Separation: `1 − ε ≤ d(map g, map h)` for `g ≠ h ∈ F`.
  - This is the standard local definition (multiplicativity on all pairs of `F`, stronger than the product-restricted
    convention, equivalent to it by the file's own comment and the standard argument).
- **`elementaryGroup ι R`** (`Leavitt/ElementaryGroup.lean:69`): `Subgroup.closure` of the units
  `1 + Matrix.single i j a` for `i ≠ j`. This is `EL_n(R)`.
- **`CompleteMatrixFamily A ι`** (`Leavitt/MatrixSelfSimilarity.lean:19`): `left, right : ι → A` with
  `right i * left j = δ_ij` and `Σ left i * right i = 1`. This is the unital `d`-ary Leavitt family, with
  `s_i = left i` and `t_i = right i`.

**Endpoint.** `GroupApproximation.CompleteMatrixFamily.elementary_not_isSofic` (`Leavitt/AryEndpoints.lean`):
- variables: `(k : Type) [Field k] [Finite k] {A : Type} [Ring A] [Algebra k A] [Countable A] [Nontrivial A]`,
  `F : CompleteMatrixFamily A (Fin (n+2))`, `(m : ℕ) (hm : 0 < m)`;
- conclusion: `¬ IsSofic (elementaryGroup (Fin (m+1)) A)`;
- no hypothesis binder stands for a cited result: every argument is an instance, the family itself, or `0 < m`.

It goes through `FamilyRankFour.elementary_not_isSofic`, whose signature is recorded in `metadata/CLAIM_SIGNATURES.md`
(instances plus `LeavittFamily A`, `0 < m`) and which carries `#audit_axioms` in the root-imported
`Endpoint/Audit.lean` (a build failure outside the classical axioms).

**Axiom closure (fresh).** MSI probe via `pc/pcprobe.sh` (lane slot `pc-review`, overlay
`GroupApproximation/UnVerify/NonsoficAxioms.lean`, not landed), tag `0913-150110-6922`, base `4179e5714`.
BUILT, EXIT=0, PROBE GREEN. Printed closures:
- `CompleteMatrixFamily.elementary_not_isSofic`: `[propext, Classical.choice, Quot.sound]`;
- `FamilyRankFour.elementary_not_isSofic`: `[propext, Classical.choice, Quot.sound]`;
- `isSofic_of_injective`: `[propext, Classical.choice, Quot.sound]`.

So the input is a machine-checked, unconditional theorem about the standard notion.

**Node and route.** The d-ary node's route `d-ary-leavitt-nonsofic-via-binary-corner` has `requires: []` and cites
only the Lean modules, and its statement matches the declaration. Its "universal algebra, not presented `L_k(1,d)`"
caveat concerns only the specializations. The generic `CompleteMatrixFamily` form applies to any algebra with a family.

## 2. The Leavitt family in `R_∂` (recomputed)

Conventions: `u_g P_U u_g⁻¹ = P_(gU)`, so `P_U u_g = u_g P_(g⁻¹U)`. For `c = c_i` write `P = P_(C(c))` and
`Q = P_(C(c⁻¹))`. The inputs are:
- (I1) `c·C(c⁻¹) = ∂F_d∖C(c)`;
- (I2) `c·C(c′) = C(cc′)` for `c′ ≠ c⁻¹`;
- (I3) the `2d` cylinders partition `∂F_d`.

**`t_i s_i = 1`.** Expand `(P + u_cQ)(P + u_(c⁻¹)(1−P)) = P + P u_(c⁻¹)(1−P) + u_cQP + u_cQu_(c⁻¹)(1−P)`.
- `P u_(c⁻¹)(1−P) = u_(c⁻¹) P_(C(cc))(1−P) = 0`.
- `QP = 0`.
- `u_cQu_(c⁻¹)(1−P) = P_(c·C(c⁻¹))(1−P) = (1−P)`.
- Sum: `1`.

**`s_i t_i = P + Q`.**
- `P u_c Q = u_c P_(c⁻¹C(c)) Q = u_c P_(∂∖C(c⁻¹)) Q = 0`.
- `(1−P)P = 0`.
- `u_(c⁻¹)(1−P)u_cQ = P_(c⁻¹(∂∖C(c)))Q = P_(C(c⁻¹))Q = Q`.

**`t_i s_j = 0` for `i ≠ j`.** With `e = c_j` all four terms vanish:
- `P_cP_e = 0`;
- `P_c u_(e⁻¹)(1−P_e) = u_(e⁻¹)P_(C(ec))(1−P_e) = 0`;
- `Q_cP_e = 0`;
- `Q_c u_(e⁻¹)(1−P_e) = u_(e⁻¹)P_(C(ec⁻¹))(1−P_e) = 0`.

**`Σ s_i t_i = Σ (P_(C(c_i)) + P_(C(c_i⁻¹))) = 1`** by (I3).

This matches `CompleteMatrixFamily` with `left = s` and `right = t`. `R_∂` is a countable nontrivial `k`-algebra
(`k` finite, `∂F_d` second countable), so every instance argument of the endpoint is met. Injectivity of
`L_k(1,d) → R_∂` holds because `L_k(1,d)` is simple and the map is nonzero.

## 3. Corner embedding and centre

- **The corner ring.** `e = s_1t_1` is idempotent, and `1 − e = Σ_(i≥2) s_it_i ≠ 0`. The map `θ(x) = s_1xt_1` is a
  ring isomorphism `R → eRe`:
  - multiplicative, since `θ(x)θ(y) = s_1x(t_1s_1)yt_1 = θ(xy)`;
  - `θ(1) = e`;
  - inverse `y ↦ t_1ys_1`, since `s_1(t_1ys_1)t_1 = eye = y`.
- **The embedding.** `Φ(X) = X + (1−e)I_N` is an injective homomorphism `EL_N(eRe) → EL_N(R)` with
  `e·I + rE_ij ↦ 1 + rE_ij`.
- **Scalars.** If `Φ(X) = λI` with `λ ∈ k^×`, compressing by `1−e` gives `(λ−1)(1−e) = 0`, so `λ = 1`. So
  `ψ = Φ∘EL_N(θ)` meets `k^×I_N` trivially and injects into `EL_N(R)/C` for every `C ≤ k^×I_N`.
- **Nonsoficity of the quotient.** Subgroups of sofic groups are sofic (`isSofic_of_injective`, axiom-clean), so
  `EL_N(R)/C` is nonsofic.
- **The centre.** `Z(EL_N(R_∂)) ⊆ Z(R_∂)^× I_N = k^× I_N` for `N ≥ 3` (part 1 §4, with the scalar-centre theorem;
  the boundary groupoid is minimal and effective, part 3 §4). So `S_∂` is nonsofic.

Display fix applied: the route cited `LeavittFamily.elementary_not_isSofic`; the declaration is
`GroupApproximation.CompleteMatrixFamily.elementary_not_isSofic`.

## 4. `algebraic-tarski-for-steinberg-algebras`, item 1: scope repair

- **What un-verify-3 found.** Its review (`un-review3-2026-09-13-part1.md` §1) passed the chain, proving Step 1 for
  a nonzero rank function **on simple `R`**: the rank-zero set is a proper ideal, hence zero.
- **The gap.** The claim's item 1 is stated for **minimal** `𝒢` with a **nonzero** rank function and no
  effectiveness hypothesis, so `R` need not be simple. A nonzero, non-faithful rank function on a non-effective
  minimal groupoid algebra gives, via `U ↦ rk(1_U)`, only an invariant probability measure. Stable finiteness from
  that is the open characteristic-`p` direction (`invariant-measure-gives-rank-function-any-field`, Kaplansky
  firewall).
- **Repair.** Item 1 now reads "faithful". The claim's own sentence already records that nonzero rank functions are
  faithful when `𝒢` is effective. Items 2–3 and the characteristic-zero equivalence are unaffected, since there the
  rank function is faithful by construction.
