# lx-review: model test of the named Props on the LIX-strong chain (2026-09-12, origin c3b58d90c)

Question for each Prop / structure: is it TRUE at the real objects, for every stage `j` including stage 0
(`lixDD n 0` empty), for every corner unitary it quantifies over, and for every `k` with `p ∤ k`?  Does any
field over-ask?  Is anything vacuous?  Soundness itself is not at risk here: every consumer theorem is compiled
and sorry-free, so a producer that satisfies a Prop yields a true conclusion.  The risk is an UNSATISFIABLE or
needlessly expensive Prop that stalls a lane.

## Verdicts

| Prop / structure (file) | at the real objects | notes |
|---|---|---|
| `LIX.Gen.LemmaTwoFor n (lixDD n j) (KGen.bVecK n (k−1))` (Analysis/LIXLemmaTwoPropGeneric:96), `p ∣ n`, `p ∤ k` | TRUE | stage 0: complement of a degree-`k` section of `S^{2n+1}` is the pullback of the generator of `π_{2n}U(n) = ℤ/n!` along a degree-`k` map; trivial iff `n! ∣ k`, and `p ∣ n` gives `p ∣ n!` |
| `LemmaTwoHoldsAtPowers n` (ProblemLIXStrongAssemblyCor4:40) | TRUE | |
| `Gen.StepCHalf` (LIXLemmaTwoGenGlue:142) | TRUE | |
| `KGen.KZeroLocalData` (LIXKGenStepCHalfTop:51), `p = 2` | TRUE | excision to `k+1` disjoint balls makes `Σ ρ_i` an isomorphism, so the components are unique and each is the local Thom class at a local homeomorphism |
| `Gen.WuStepDData` (LIXStepDGenData:80), `p = 2` | TRUE | `Y` has no odd cohomology, so `γ_k = a_k + t x b_k`; `sq_b` is instability at degree `2k − 2n − 2`; the rank-two instance is the landed mod-2 answer |
| `KGen.KZeroStepCDataOf` (LIXKGenOfStepC:134) incl. `LocalClassesAgree` | TRUE | all `k+1` local indices are `+1` (below); `u` existential absorbs the sign convention between `c_r` and the Euler class |
| `Gen.RealBundleModP` (LIXStepDGenReal:191) | TRUE | Wu leading coefficient a unit (`isUnit_wuLeading`, compiled); `IsDecomposable` needs integer coefficients only, which the universal Wu polynomial has |
| `Gen.RealTorusModP` (LIXStepDGenReal:130) | TRUE for normalized operations, FALSE for raw ones | over-asks, finding F1–F2 |
| `ParityP.PowerData` (ParityPWuCartan:229) | same | finding F1 |
| `Gen.ModPStepDData.pH_zero` (LIXStepDGenModP:97) | same | finding F1 |
| `LemmaTwoPowersTwoLocalData`, `LemmaTwoPowersTwoWuData`, `LemmaTwoPowersModPData` (e1cd56947) | TRUE | finding F3 on `htop` |
| `[ExpChar (evenPart (ZMod p) (Y j)) p]` | TRUE | `Y j` nonempty (stage 0: a point), so `ZMod p → H⁰` is injective |
| stage 0 everywhere | satisfiable | `gen : Fin 0 → _`, `sliceClass = 1`; `z_inj` needs `σ₁, σodd ≠ 0` (sphere top classes) |

## Findings

**F1. `P⁰ = id` on all classes is an over-ask (RealTorusModP.PN_zero, ModPStepDData.pH_zero, PowerData.p_zero_apply).**
The raw operations `D_{(q−2i)(p−1)}` from the equivariant diagonal satisfy `P⁰ = ν(q)·id` on `H^q`, with
`ν(q) = (−1)^{m q(q−1)/2} (m!)^q`, `m = (p−1)/2`.  Model test (`tools/review_constants.py`, MSI, 16 odd primes
3..59, 3712 checks, 0 failures): `ν(1) = m!`, `ν(2) = −1`, `ν(2k) = (−1)^k`, `ν(q+q') = (−1)^{m qq'} ν(q) ν(q')`,
`ν(q)` a unit.  These are the programme's `c_1`, `c_2`, `c_{2k}`, `κ_top`.  Normalizing to `P⁰ = id` needs `ν(q)`
PROVED in every degree used.  What the consumers use:
* `pH_zero` only inside `pH_z_mul_of_cartan` at `u = z`; `pH_z_mul` only at `r = b(i+1)` with
  `PR i (b(i+1)) = 0` (ParityPData.lean:471).  A unit factor on `P⁰ z` is harmless.
* `PowerData.p_zero_apply` on the flag algebra (pShift, `P n 1`, wuMonomialP).  Raw operations give
  `P⁰ y = −y`, `P¹ y = y^p`, `P^{≥2} y = 0`, exact Cartan on even classes (the ratio `(−1)^{m qq'}` is `1` when a
  degree is even), `P⁰ 1 = 1`.
Proposal: a `λ`-generalized `PowerData` (`P⁰ y = λ y`, `λ` a unit; leading coefficient `λ κ^i wuCoeff p i`) and
`pH_zero_z : ∃ c, IsUnit c ∧ PH 0 z = c * z` (or the weak `pH_z_mul`).  The one irreducible constant computation is
then `λ ≠ 0` on the generator of `H²(ℂP^N; F_p)` (Euler classes of line bundles by naturality).  The Frobenius
satisfies every other axiom with `λ = 0`, so `λ ≠ 0` must be computed (degree-one `T² → ℂP¹` and
`κ_top(1,1)·c_1² = −1`).

**F2. `RealTorusModP.cartan` on odd classes.**  Raw Cartan at odd × odd carries `(−1)^{m qq'}`, which is `−1` at
`t·x` when `p ≡ 3 mod 4`.  The field is consumed on even classes (`toModPStepDData`) and at `t·x` only to get
`P^{>0} z = 0` (`PN_zClass`).  Proposal: `cartan_even` plus `P_z : ∀ i > 0, PN i z = 0`, from naturality along
`N → S¹ × S^{2n+1}` (cohomology zero above degree `2n + 2`); drop `P_t`, `P_x`.

**F3. `htop` in `LemmaTwoPowersModPData` is quantified over every `W`.**  It is consumed only through
`stepCHalf_of_eq_zero_imp`, and a Step C half evaluates only at mapping tori.  Satisfiable only if producers
define `γfun W k := TotalHOf.of (2k) (degreewise class)` for every `W`.  Restrict to mapping tori, or document the
construction constraint for the producers.

**F4. `LocalClassesAgree` holds, and a route that avoids rotating the bundle.**  Near the zero `ζ_i e₀`,
`ψ_k(ζ_i w) = ζ_i^{k+1} ψ_k(w) = −w^{k+1}/|w|^k`: the local map at `z_0` precomposed with the rotation `ρ^i`,
orientation-preserving; the frame factor `G(z_i, y₀)` is complex-linear, hence orientation-preserving and
homotopic to `1` in `GL_r(ℂ)`.  So every local index is `+1` and the images agree over any field.  Route: identify
each `xloc_i` with a positive unit multiple of the standard generator of `H^{2r}(ℂ^r, ℂ^r∖0)` through that zero's
linear-frame homotopy, then compare the absolute images of the standard generators along `ρ^i ≃ id` on `N`
(absolute homotopy invariance only), provided the per-zero charts are `ρ^i`-conjugate.

**F5. Challenge prose.**  `Palomar/LIXStrongChallenge.lean`'s module docstring says of the plain LIX surface that
"one element of order two is all it exhibits"; that theorem exhibits a nontrivial element, its order is not
computed.  Statements: faithful and non-vacuous (`v ^ k` is the `Submonoid` power in `unitary A`, `pathComponent`
the subtype topology, `cornerDiag A 2 v = diag(v, 1)`, the power clause at `k = 1` gives `v ∉ U₀`, `Fin 2` and the
spectral order are pinned).  `IsK1Injective` is defined and unused; defensible for byte-identity with the LIX
surface, visible to a registry reviewer.

**F6. Stale seam note.**  rescue-lix's "positivity of `lixDD` was not checked on main" is stale:
`LIX.Gen.lixDD_pos` (Analysis/LIXLemmaTwoPropGeneric:68), already used by e1cd56947.

## Landings reviewed

`e1cd56947` (lx-endpoint, unverified): three named Props introduced, no existing statement changed, the commit
message names the content.  `40801adec`, `19b478821` (board notes): no Prop.

Sent to owners 2026-09-12: lx-torusP (F1, F2), lx-splitK (F1), lx-slice2 (F1), lx-pzero (F1), lx-endpoint (F3, F5,
F6), lx-stepcK-agree (F4).

Follow-ups: lx-endpoint narrowed `htop` to mapping tori (assemblies PROBE GREEN 0912-101459-43218) and fixed the
docstring.  lx-stepcK-agree's frozen-field rotation route for `LocalClassesAgree` (`R_c`, `β ∘ R_c = β`,
homotopy `H(τ, p) = (R_{c(τ)} p, P(R_{c(τ)} p)(0 ⊕ β p))`) was checked against dadc8f5df: no flaw.

## Round 2: the odd-primary narrowing (origin c1b23d84a)

lx-design narrowed the consumer interfaces (design `notes/lix-strong-swarm/design-oddp.md`).

**Complete against their proof sites.**  `ParityP.PowerDataN` and `wu_field_of_splittingN`: p_mul_y at `u = ∏ y`,
`p_one_pos` for `p_one_eq_zero`, `p_zero_one` and the derived `p_zero_prod` for `p_prod`, `hP` only at `γ (i+1)`
(WuTransport:235).  `ParityPDataN.pH_z_mul_zero` at ParityPDataNarrow:151.  `EvenReducedPowers` (a5f0a1992):
`mul_single` needs no unit on `c`, and its consumer needs none; `z ∈ Good` via `good_of_components`, because the
degree-0 component of `Ptot z` vanishes (restrict to a point); `zero_cp = μ⁻¹ μ`.

**R1. The real odd-`p` chain still uses the strong forms.**  `LemmaTwoPowersModPData` →
`lemmaTwoFor_powers_of_stepC_realModP` → `RealBundleModP.toModPStepDData` (`pH_zero := T.PN_zero`,
`cartan := T.cartan`) → `ModPStepDData.toParityPData` (LIXStepDGenModP:142, `pH_z_mul_of_cartan`) → ParityPData:471.
`Gen.RealTorusModP` at e6b92af13 still has `PN_zero` on the whole even part of `N` and an unconditional `cartan`;
design-oddp.md's "landed spellings" entry for lx-torusP does not match origin.  `ModPStepDDataN` exists only in
the shared tree, unrouted.

**R2. Red at tip, unwired.**  `LIXStepDGenTorusPModel.RealTorusModP.ofEven` uses `ops.zero N` (field removed) and
`ops.cartan N` (now guarded by `Good`).  `LIXStepDGenBundleP` (142, 179) and `LIXStepDGenBundlePLix` (78, 127) use
`T.PN_even` (removed).

**R3. Strong splitting on the bundle path.**  lx-bundleP consumes `HasSplittingP` and `realWu_of_splitting` (strong
`PowerData`, `hP` for all `x`).  lx-splitK's producers give `HasSplittingPN`; `realWu_of_splittingN` does not exist.

**R4. Producer route for `pH_z_mul_zero`.**  Use `mul_single` at `z` plus naturality.
`pH_z_mul_zero_of_cartan` needs Cartan at `z × ι r` for arbitrary even `r`, hence `ι r ∈ Good`, hence
generation of `H^*(∏ ℂP; F_p)` by degree-two classes, which the design avoids.

Sent 2026-09-12: lx-torusP (R1, R2, R4), lx-bundleP (R2, R3), lx-slice2 (R1, R4), lx-design (all).
