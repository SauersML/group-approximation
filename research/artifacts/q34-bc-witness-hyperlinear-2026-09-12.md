# Is the Bowen--Chapman witness hyperlinear? Lane `q34-bc-witness-hyperlinear`, 2026-09-12

Question (root `q3-4-resolved`): is the nonsofic group built in the repo hyperlinear? A proof that it is would answer
Pestov Q3.4 negatively. Pin: `d58fa0f32`.

## 0. Outcome

- **Proved, `kt-wreath-models-never-round-on-the-vertex`.** No trace-preserving matrix-ultraproduct model of the
  Kun--Thom wreath `W` restricts to an actor model whose vertex has an (H1) rounding. So (H1) at wreath-extendable
  models is exactly nonhyperlinearity of `W`. The (H1) node records this converse as "not on main".
- **Proved, `bowen-chapman-witness-is-kt-double-at-q2-r3-d3`.** The Lean witness `SymmetricDouble Ambient Peripheral`
  is the Kun--Thom double at `(q, r, d) = (2, 3, 3)`. Its hyperlinearity is equivalent to:
  - hyperlinearity of `W`;
  - `RE/C`;
  - hyperlinearity of the free action;
  - existence of a wreath-extendable actor model, every one of which fails (H1).
- **Not proved:** hyperlinearity or nonhyperlinearity of the witness. `q3-4-resolved`, `hyperlinear-nonsofic-group`,
  `hyperlinear-nonsofic-free-action` and `non-hyperlinear-group` stay OPEN.
- **No `invalidates:`.** No live route is killed by the obstruction (§7).

## 1. The Lean witness is the Kun--Thom double at (2, 3, 3)

Declarations, at the pin:

| Lean declaration | File:line | Content |
|---|---|---|
| `Laurent` | `BowenChapman/LaurentPair.lean:34` | `AddMonoidAlgebra (ZMod 2) (Fin 3 → ℤ)` = `F_2[x^(±1)]` |
| `Poly` | `:38` | `AddMonoidAlgebra (ZMod 2) (Fin 3 → ℕ)` = `F_2[x_1, x_2, x_3]` |
| `polyToLaurent`, `polyToLaurent_injective` | `:60`, `:68` | the inclusion `R_+ → R` and its injectivity |
| `Actor` | `:85` | `elementaryGroup (Fin 3) ℤ` = `EL_3(Z)` |
| `exponentAction`, `substitution` | `:88`, `:119` | `v ↦ Mv` on exponents; `x^v ↦ x^(Mv)` on `Laurent` |
| `actorAction` | `:146` | entrywise substitution on `EL_3(Laurent)` |
| `Ambient` | `:189` | `EL_3(Laurent) ⋊ Actor` |
| `peripheralHom`, `Peripheral`, `peripheralHom_injective` | `:193`, `:197`, `:217` | `EL_3(Poly) ↪ Ambient` and its range |
| `SymmetricDouble` | `Sofic/WeakMFNonsoficDouble.lean` | `PushoutI` of `doubleMap`: two copies of `G` over `Γ.subtype` |
| `symmetricDouble_fg_surjunctive_not_isSofic` | `BowenChapman/Endpoint.lean:43` | finitely generated, surjunctive, not sofic |

Identification:
- `EL_3(Z) = SL_3(Z)`, since `Z` is Euclidean. Kun--Thom Theorem E takes `G = EL_r(R) ⋊ SL_d(Z)` with monomial
  substitution.
- Substitution through the standard representation is the Lean action. Substitution through the contragredient
  is the Lean action composed with `φ(M) = (M^T)^(-1)`.
- For `β = α ∘ φ`, the map `(l, s) ↦ (l, φ(s))` is an isomorphism `L ⋊_β S → L ⋊_α S`:
  `(l α_(φ(s))(l'), φ(s)φ(s')) = (l β_s(l'), φ(ss'))`. It is the identity on `L`, so it fixes `Γ ⊆ EL_3(R)` and
  extends to the pushouts.
- `polyToLaurent` is injective, so `EL_3(Poly) ≅ Peripheral` is the Theorem E vertex `EL_3(R_+) ⊆ EL_3(R)`.

## 2. Status audit at the pin (MSI, `cairn why`, job `q34h-why0`)

| Node | Status |
|---|---|
| `nonunit-projection-bounded-by-root-spectral-mass` | ESTABLISHED via `nonunit-projection-root-mass-proof` |
| `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` | ESTABLISHED via `shallow-nonunit-root-mass-proof` |
| `vertex-rounding-deep-nonunit-root-mass-vanishes` | ESTABLISHED via `deep-nonunit-root-mass-two-attractor-proof` |
| `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` | ESTABLISHED via `unit-type-vertex-rounding-ccr-proof` |
| `kun-thom-wreath-carries-rigid-defect` | ESTABLISHED via `kun-thom-wreath-carries-rigid-defect-proof` |
| `kt-wreath-hyperlinear-iff-double-hyperlinear` | ESTABLISHED via `kt-wreath-hyperlinear-iff-double-proof` |
| `kt-q2-double-hyperlinear-iff-relative-embeddable` | ESTABLISHED via `kt-q2-double-gao-relative-embedding-proof` |
| `kt-free-action-hyperlinear-iff-wreath-hyperlinear` | ESTABLISHED via `kt-free-action-hyperlinear-iff-wreath-proof` |
| `kt-pair-group-double-is-nonsofic` | ESTABLISHED via `kt-group-double-nonsofic-citation` |
| `hs-stable-vertex-rounding-for-every-model` (H1) | OPEN, no live routes into it |
| `theorem-e-vertex-rounds-to-unit-type-representations` | OPEN |
| `hyperlinear-wreath-model`, `hyperlinear-nonsofic-free-action`, `hyperlinear-nonsofic-group` | OPEN |
| `non-hyperlinear-group`, `q3-4-resolved` | OPEN |

## 3. Pointwise audit: every premise is used at one model

The (H1) node's own audit says that the rigidity inputs, the projection bound, the shallow and deep root-mass
claims, and `compressor-transport-exactifies-under-vertex-rounding` "all begin 'let sigma satisfy (H1) with roundings
pi_n'". Here is what each one uses at that `σ`.

- **Rigidity** (items 1–4). Item 1 is root torsion of the given `π_n`. Item 2 is the algebra of `R_+/I_n`.
  - Item 3 is the excess for `σ(A)`, `A` a nonnegative compressor.
  - Item 4 is (CCR) for every nonnegative strict compressor, with `G = <Γ, e_ij(1)>`.
  - The only unitaries are `σ(A)`.
- **Projection bound.** A finite-dimensional statement about one `π_n`. It uses no actor.
- **Shallow mass.**
  - `η_n` comes from the intertwining defect of `σ_n(A)`, where `A` has all entries `>= 1`.
  - `η_n^t` comes from the defect of `σ_n(t)` with `t = diag(x_1, x_1, x_1^(-2), 1, …)`.
  - The relative Kazhdan pair `(S, R_+^2)` sits inside `Γ`.
  - All of these are data of `σ` and `π_n`.
- **Deep mass.**
  - Transports `D_(A^k)` and `D_B` come from `σ(A^k)` and `σ(B)`, with `A = (min(i, j))` and `B` the reversal
    conjugate.
  - Unit-scaling invariance of `μ_n` is a property of `π_n`.
  - `ν_n` and `η_n^±` are defects of the same `σ`.
- **Rigid defect.** Pure group theory of `Γ < G < W`.

No premise asks for (H1) at a second model: not at a conjugate model, not at an amplification. So the chain runs at
one `σ` and one rounding.

## 4. The obstruction

Run the chain at `σ̃|G`, where `σ̃ : W → U(∏_U M_n)` is trace-preserving.
1. Shallow and deep mass vanish, so `τ(1 − P_n) → 0`.
2. Item 4 then says `σ̃(G)` normalizes `N = σ̃(Γ)' ∩ ∏_U M_n`.
3. `σ̃(e_Γ) ∈ N`, so `σ̃(e_(tΓ)) = σ̃(t) σ̃(e_Γ) σ̃(t)^* ∈ N` commutes with `σ̃(γ)`. Hence
   `σ̃(e_(γtΓ)) = σ̃(e_(tΓ))`.
4. But `γ ∉ tΓt^(-1)` gives `γtΓ ≠ tΓ`, and trace preservation gives `||σ̃(e_(γtΓ)) − σ̃(e_(tΓ))||_2^2 = 2`.

Diagonal form: some `ε > 0` has `A_ε ∉ U`, by a diagonal choice of `π_n` at `ε = 1/k(n)`. See the route
`kt-wreath-models-never-round-on-the-vertex-proof`.

## 5. The equivalence and the lane conflict

At `(2, 3, 3)`: `E` hyperlinear ⇔ `D` hyperlinear ⇔ `W` hyperlinear ⇔ `RE/C` ⇔ free action hyperlinear ⇔ a
wreath-extendable actor model exists ⇔ some wreath-extendable model fails (H1).

| Lane | Open node | Effect at `(2, 3, 3)` |
|---|---|---|
| non-hyperlinear chain | (H1) `hs-stable-vertex-rounding-for-every-model` (9919a5637) | if established, `E` is not hyperlinear |
| non-hyperlinear chain | `laurent-vertex-rounds-for-every-model`; `K_i` (T) (44267adad) | the (T) handle needs `r >= 5` and misses `r = 3` |
| congruence projections | `theorem-e-congruence-projections-vanish-at-regular-trace` (1d9a1ceda) | limits a proof of (H1); decides nothing |
| hyperlinear-nonsofic | `hyperlinear-wreath-model` → free action | if established, `E` is hyperlinear |
| hyperlinear-nonsofic | double routes through `kt-pair-group-double-is-nonsofic` | same bit, through `D` |
| finitary lift | `kun-thom-finitary-action-lifts-to-normalizer` | gives a `W`-model in `R^ω`, so `E` is hyperlinear (§6) |

**Resolution of the tension in the directive.** The non-hyperlinear chain targets `W` on the Theorem E pair, and the
Bowen--Chapman witness is `D` at `(2, 3, 3)`.
- They are different groups with the same bit, by the established equivalences.
- The conflict is exact: both lanes cannot succeed at one parameter.
- (H1) restricted to wreath-extendable models is equivalent to the target itself. So the restriction does not make
  the target easier.

## 6. Scope

- **Models valued in `R^ω`.**
  - The conditional expectations `E_k : R → M_(2^k)` embed `R` trace-preservingly into `∏_V M_(2^k)`.
  - So `R^ω` embeds into a matrix ultraproduct over `N × N` with the product ultrafilter.
  - The premises are asymptotic statements along an ultrafilter and never use the order of the index set. This was
    checked by reading, not re-audited line by line.
  - Consequence for the finitary lift. A lift `u : G → N_(R^ω)(R)` with (KFL1) gives the `W`-model
    `(e, g) ↦ λ(e) u_g`, where `e_x` is the transposition `(x, 0) ↔ (x, 1)` in `Sym_fin(X × {0, 1})`.
  - Its vertex has no (H1) rounding in matrix coordinates, for every choice of the embedding `R ⊆ ∏ M_(2^k)`.
  - Caveat: the coordinates of `u` are elements of `R`, not matrices. The statement concerns the composite model.
- **Models of the double.** Excluded. The rigid defect uses a lamp centralizing `Γ`, and `D` has no such element.
  The `RE/C` equivalence rebuilds the model, so the vertex restriction of a `D`-model is not controlled.
- **Laurent sibling.** A rounding on `Δ = EL_r(F_q[x^(±1)])` restricts to one on `Γ`. So wreath-extendable models
  fail it too.
- **Parameters.** The obstruction holds at every `(q, r, d)` with `r, d >= 3`. The Lean identification is at
  `(2, 3, 3)` only.

## 7. Routes checked as `invalidates:` targets

| Route or claim | Why it is not killed |
|---|---|
| `amenable-charge-route` / `wreath-amenable-near-representation` | a Kahl--Schneider near representation, not a matrix model with a rounding vertex |
| `positive-core-dilation-splice` | its gate is Connes embeddability of the dilated algebra (Gao--Junge Problem 1); no genuine vertex microstates |
| double routes (`hyperlinear-nonsofic-from-kt-ce-stabilizer`, `-reduced-cstar-mf`, `-mf-amalgam-trace`) | algebra-level; the obstruction is specific to `W` |
| `kun-thom-finitary-action-lifts-to-normalizer` | the obstruction gives a necessary condition (§6), not a refutation |
| `induced-charge-extension` | already dead |
| (H1) itself | not refuted: the obstruction is conditional on a wreath model existing |

Invalidation is active only through an established invalidator. Here the only candidate target would be a route that
extends a rounding vertex model to `W`. No such live route exists on main. The "Extend a coordinatewise-genuine actor
model" attempt on the new claim records that approach as dead.

## 8. Model tests

- **Genuine actor models.** `G` is residually finite, so finite-quotient regular representations give
  trace-preserving models. (H1) holds exactly there, with `P_n = 1` (the "Genuine actor models" attempt on
  `theorem-e-vertex-rounds-to-unit-type-representations`).
  - The obstruction says none of them extends to `W`.
  - This agrees with `ccr-holds-for-all-genuine-fd-coordinate-models` combined with the rigid defect.
  - It also agrees with Kun--Thom nonsoficity.
- **Normal vertex.** If `Γ ⊴ G` there is no strict compressor, and step 3 of §4 has nothing to act on. No false
  conclusion.
- **Amenable calibration.** Take `BS(1, 2) = Z[1/2] ⋊ Z` with `Γ = Z`. `Γ` is infranormal (`tΓt^(-1) = 2Z`) and not
  normal.
  - The wreath is amenable, hence hyperlinear.
  - (H1) holds at every model, since a single unitary is a genuine representation of `Z`.
  - The rigid defect exists.
  - So normalization (step 2 of §4) must fail there, and it does: the finite Steinberg images, the root-mass bounds
    and property (T) are absent.
  - The content of the obstruction is the Theorem E rigidity premises, not the lamp computation.
- **Leavitt calibration.** The general (H1) contains the nine-leaf Leavitt pair. There it is equivalent to
  nonhyperlinearity of `L_(F_2)(1, 2)^×` (`leavitt-pair-vertex-rounding-is-nonhyperlinearity`). The new claim is the
  Theorem E analogue at wreath-extendable models.
- **Where a parameter could matter.**
  - `q = 2` and `r = d = 3` enter none of the equivalence proofs.
  - The shallow bound `q·η_n + η_n^t` vanishes along `U` for each fixed `q`. The deep error `12 q^(-(L+1))`
    vanishes as `L → ∞` for every `q >= 2`. Neither needs anything at `q = 2`.
  - The `K_i` (T) handle needs `r >= 5`.

## 9. What remains

- **Decide the bit at `(2, 3, 3)`.**
  - A hyperlinearity proof must produce wreath models whose vertex stays a uniform distance from every genuine
    representation of `Γ`.
  - A nonhyperlinearity proof through (H1) must use actor models that extend to no wreath model. Otherwise it only
    restates the target.
- **Transfer to double models.** Open. A pointwise vertex obstruction for `D` would need a replacement for the lamp
  centralizing `Γ`.
