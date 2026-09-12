# `sp-oddside-n` — the mod-2 `k`-zero Step C at general rank `n`

Lane of `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`.  Clone `quant-collapse`, cores 30–35.
Owns `GroupApproximation/CharClass/LIXKGen*.lean` **only**; edits no existing file, and in
particular none of `sp-oddside`'s `LIXK*.lean` and none of `sp-tower`'s `LIXShapeGeneric`.

Namespace: `GroupApproximation.CharClass.KGen`.  Deliberately **not** `Gen`, which is
`sp-tower`'s; a rank parameter under two owners in one namespace is exactly the
one-name-two-objects collision `FLEET_TRAPS` records twice and that no probe can see.
Every declaration takes the rank `n` first, as `sp-tower`'s do.

Status key: **GREEN** = a `✔ … Built <module>` line cited from a log named here, taken
under a purge whose `source-newer=` and `import-newer=` counts are quoted beside it ·
**AUTHORED, UNVERIFIED** = written, never near a compiler · **PLANNED** = in the file list,
not written.

---

## 0. The plan (written 2026-09-10, before authoring)

### 0.1 What the reading pass settled, and what it changed

Six facts, each **VERIFIED (read)** at the declaration named.  Two of them cut the
deliverable down substantially and one of them redirects the first sub-deliverable.

1. **`CharClass/CohomologySphere.lean` is already generic in the sphere dimension.**  The
   launch message asked me to check whether it covers only odd `m ≤ 5`.  It does not:
   `sphere_coh_isZero_of_gt (n k : ℕ) (h : n < k)`, `sphere_coh_isZero_of_lt`,
   `sphere_coh_isZero_of_ne`, `sphere_coh_top_finrank`, `sphereTopEquiv`,
   `sphereCohZeroEquiv` and `CohomologyShapes.hasSphereCohomology_sphere` are all stated
   for the vendored `Sphere n = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)` at
   **every** `n`, with `1 ≤ n` where the top class needs it.  So there is no sphere
   cohomology to generalise.
   Likewise `ThomKunnethSphere.kunnethFactor_sphere (n : ℕ)`,
   `kunnethFactor_sphere_compl`, `puncturedAcyclic_sphere` and
   `ThomToolkitInstance.puncturedAcyclic_sphere'` are generic in the dimension **and** in
   the real inner-product space.
2. **What *is* rank-two-bound sits one level up, and it is one homeomorphism.**
   `CharClass/LIXStepESphereModel.lean` supplies
   `unitVectorsThreeHomeo : ↥(unitVectors (Fin 3)) ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 6)) 1)`
   by hand, with `cxToEuc` an explicit `![…]` literal in six real coordinates, and
   `LIXStepESpheresDischarged.lean` reads four consequences off it
   (`isZero_cohomology_sphereFive`, `kunnethFactor_unitVectorsThree`, its punctured
   companion, `hbase_lix`).  None of the five survives a rank change.  **That is the first
   sub-deliverable**, and it is the whole of it.
3. **`sp-oddside`'s counting engine is rank-free and I reuse it verbatim.**
   `LIXKCount.lean` is abstract in `ModuleCat K` with no space anywhere;
   `LIXKStepC.lean` is abstract in `{N} [TopologicalSpace N] {twoR} {z₀}`;
   `LIXKPunctured.lean`'s `isZero_punctured_finite` is abstract in `{N} [T1Space N] {d}`.
   So the `k`-zero *engine* costs this lane nothing at all, and the finite-puncture
   induction — which I had budgeted as work — is already generic.  What my punctured layer
   has to produce is exactly one hypothesis of it:
   `∀ z, PuncturedAcyclic (↥sphereOne × Gen.baseM n dd) (KGen.lixTopDegree n dd) z`.
4. **`sp-oddside`'s scalar layer is rank-free too.**  `kUnity`, `kBase`, `kRoot`,
   `kRoot_pow`, `norm_kRoot`, `kRoot_injective`, `exists_kRoot_of_pow_eq_neg_one`,
   `joinC_eq_pow_of_norm_one`, `joinC_eq_neg_one_iff` and the three
   `norm_eq_one_of_*` lemmas are statements about `ℂ` and about `Fin (k+1)`, not about the
   sphere.  I import `LIXKMap.lean` and define no second copy of any of them.  The only
   things that carry `Fin 3` are the five vector-level definitions
   (`eOne`, `negEOne`, `psiVec`, `kZeroVec`, `kRot`) and the four theorems that `fin_cases`
   over `Fin 3` (`eOne_normSq`, `re_neg_eOne_two`, `kZeroVec_mem`,
   `psiVec_eq_neg_eOne_iff`).
5. **`sp-tower`'s `Gen` shape layer gives me the ambient at rank `n` outright.**
   `Gen.VIdx n dd`, `Gen.baseM n dd`, `Gen.Vmat n`, `Gen.Hmat`, `Gen.cVec`,
   `Gen.cVec_eq_zero_iff`, `Gen.Vmat_mulVec_left/right`, `Gen.continuous_Vmat`,
   `Gen.isMTSectionData_manuscriptData n`.  My section file is theirs with the two fields
   `a`, `b` replaced, exactly as `sp-oddside`'s `LIXKSection` is `LIXSectionManuscript`
   with the two fields replaced.
6. **`LemmaTwoZero.mtSection_manuscript_eq_zero_iff` is rank-free as well as `a`/`b`-free.**
   It is stated for abstract `a b : M → ι → ℂ`, `c : M → κ → ℂ` over an abstract index pair
   and uses only `a m ≠ 0`, `∑‖a m i‖² = 1`, `∑‖b m i‖² = 1`, `χ(1/2) = 1`.  `ι := Fin (n+1)`
   and `κ := HIdx dd` is a legal instantiation with nothing to prove.  So the zero-locus
   theorem at rank `n` is the same single substitution `sp-oddside` made at rank two, and
   `LemmaTwoZero.lean` is reused verbatim at every rank.

### 0.2 The one place the rank is not free: the constant section is at index `0`

`sp-tower`'s `Gen.eLast n = Pi.single (Fin.last n) 1`, and their docstring's reason for it
("the analysis side's Householder frames are built around `Fin.last n`; any other choice
inserts a permutation between the two sides of Step A") is correct for the one-zero tower.
The `k`-zero geometry cannot use it, and the reason is the same at rank `n` as at rank two:
`±e_last` are the suspension points of the clutching coordinate `Re (x (Fin.last n))`, a
hemisphere-preserving self-map of `S^{2n+1}` is a **cone** at a suspension point, and a
cone is not a local homeomorphism.  So

```text
  KGen.eZero n := Pi.single (0 : Fin (n + 1)) 1 ,
```

whose antipode lies on the equator `{Re (x (Fin.last n)) = 0}` as soon as
`(0 : Fin (n+1)) ≠ Fin.last n`, i.e. as soon as `0 < n`.  **`0 < n` is carried on the
theorems that need it and on no definition.**  The permutation is absorbed on the Step A
side (`sp-design` §1.3: `G' = G·(P ⊕ 1)` with `P e₀ = e_last`, still a corner unitary of
`V`, and `EHmat^{e₀} = (P⊕1) EHmat^{e_last} (P⊕1)ᴴ`), which is `sp-tower`'s and not mine;
in my files it is the binder `hGe`, exactly as `sp-oddside` carries it at rank two.

### 0.3 File list

All new, all leaves at first, prefix `CharClass/LIXKGen*`.  The dependency order is the
authoring order.

| # | file | proves | depends on |
|---|---|---|---|
| A | `LIXKGenSphere.lean` | the rank-generic model bridge: `KGen.cxIdx n`, `cxToEuc n`, `eucToCx n`, `normSq_cxToEuc n`, **`KGen.unitVectorsHomeo n : ↥(unitVectors (Fin (n+1))) ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2n+2))) 1)`**, `isZero_cohomology_sphereOdd n`, `kunnethFactor_unitVectors n` and its punctured companion, `puncturedAcyclic_unitVectors n`, `KGen.hbase n` | `ThomKunnethSphere`, `CohomologyShapes`, `LIXStepEBase` (for the two `_of_homeo` shapes, which are generic in `E` — only their `Fin 3` is not) |
| B | `LIXKGenPunctured.lean` | `KGen.baseNilHomeo n`, `KGen.baseSnocHomeo n`, `KGen.lixTopDegree n dd`, **`KGen.puncturedAcyclic_lixBase n`** over `↥sphereOne × Gen.baseM n dd`, and its finite-puncture consequence through `sp-oddside`'s `isZero_punctured_finite` | A, `LIXShapeGeneric`, `ThomProjectivePunctured`, `ThomKunnethProjective`, `ThomPuncturedPi`, `LIXKPunctured` |
| C | `LIXKGenMap.lean` | `KGen.eZero n`, `negEZero n`, **`KGen.psiVec n k`**, `kZeroVec n k j`, `kZero n k j`, **`psiVec_eq_neg_eZero_iff n`**, `kRot n k m`, `psiVec_kRot n`, `kRot_kZeroVec_zero n`; and the four `n = 2` bridges to `sp-oddside`'s names | `LIXShapeGeneric`, `LIXKMap` (for the scalar layer) |
| D | `LIXKGenSection.lean` | `KGen.aVecK n`, `bVecK n k`, `isMTSectionData_manuscriptDataK n`, `lixKSection n k G`, `lixKZero n k dd j`, **`lixKSection_eq_zero_iff n`**, `lixKZeroSet n k dd` with finiteness and non-emptiness | C, `LIXShapeGeneric`, `LemmaTwoGlue` |
| E | `LIXKGenChart.lean`, `LIXKGenDeriv.lean`, `LIXKGenLocalHomeo.lean` | the local model at `−e₀` on `S^{2n+1}`, generic in `n`, in `sp-design` §1.3's coordinate-free form: a unit vector `a` and an ℝ-linear isometry `L` onto `a^⊥_ℝ`; strict derivative `(dw, du) ↦ (1/2)·L dw − du·a`, a linear isomorphism; inverse function theorem | B, D |
| F | `LIXKGenStepCWired.lean` | the rank-`n` instantiation, shaped like `sp-oddside`'s `LIXKStepCWired`, over `LIXKCount`/`LIXKStepC`/`LIXKStepCTwo` cited at rank `n` | all of the above |

### 0.3a The design of file E, and it removes a differentiation nobody wants

Scoped by reading `LIXSectionChart.lean` (237 lines), `LIXSectionDeriv.lean` (203),
`LIXSectionLocalHomeo.lean` (102), `LIXSphereChart*.lean` (266) and `LIXHsqEta.lean` (337)
in full.  The rank generalisation of the chart layer is mechanical — the source of the
chart at `−e₀` is `ℝ × (Fin n → ℂ)` (the imaginary part of coordinate `0`, plus the other
`n` coordinates entire), the chart is
`(c, v) ↦ Fin.cons ((c : ℂ) * I − (weight : ℂ)) v` with
`weight (c,v) = √(1 − (c² + ∑ ‖v j‖²))`, and the derivative at the origin is
`(dc, dv, dy) ↦ Fin.cons ((dc : ℂ) * I / 2 − (dy : ℂ)) (fun j => dv j / 2)`, injective and
surjective by the same explicit-inverse arguments with `Fin.cases` in place of `fin_cases`.
No determinant, no orientation, no inner product, exactly as at rank two.

**What is NOT mechanical, and the design that avoids it.**  At `k` zeros the section near
`z_j` is `(1−τ)e₀ + τ·Ψ_k(x)`, so the naive route needs the derivative of `Ψ_k` at `z_j` —
i.e. of `z ↦ z^{k+1}/|z|^k` at a nonzero point — and then an inverse function theorem for
it.  That is a `Complex.arg` calculation with a branch cut running through the target `−1`,
and it would be paid `k+1` times.  **Do not differentiate `Ψ_k`.  Chart the sphere at `z_j`
so that `Ψ_k` becomes the identity in the charts.**  Explicitly: `joinC k` has a continuous
local section on the half-plane `{Re w < 0}`,

```text
  κ_j (w)  :=  |w| · exp ( i · (arg (−w) + π + 2πj) / (k+1) ) ,      κ_j(−1) = ζ_j ,
```

whose defining `arg` is evaluated at `−w`, i.e. off the cut precisely where `w` is near
`−1`; and `joinC k (κ_j w) = w` because `|w| e^{i·arg(−w)} = −w`.  Define the chart at `z_j`
as `chart_j := Function.update (sphereChartVec n ·) 0 (κ_j (sphereChartVec n · 0))`.  Then

```text
  Ψ_k ∘ chart_j  =  sphereChartVec n      (on the chart's domain, for every j),
```

so the section read in `chart_j` is **literally `trivialBlockChart n`, the same map at every
`j`** — which is exactly what the model test measures when it reports the `k+1` local
derivatives as one matrix with spread `≤ 1.9e−10`.  The derivative is then computed once, at
`−e₀`, and neither `Ψ_k` nor `κ_j` is ever differentiated: `κ_j` is needed only to be a
homeomorphism onto a neighbourhood of `z_j`, for which continuity of `arg` off the cut and
the two composition identities suffice.

This is a claim about the design, not a discharged obligation; it needs `sp-design`'s
sign-off before I author it, and it applies verbatim at `n = 2`, so `sp-oddside` should have
it for their `KLocalNonzero`.  Told them by `SendMessage`.

**Model-tested, and my first version of the test was wrong in a way that matters.**
`scratch/sp-oddside-n/oddside_n_kappa_modeltest.py`, 84 checks, 0 failures after the
correction.

| test | claim | result |
|---|---|---|
| K1 | `κ_j(−1) = ζ_j`, i.e. the chart is centred at `z_j` | pass, error `≤ 9e−16`, `k ≤ 7` |
| K2 | `joinC k (κ_j w) = w` on the **whole** half plane `{Re w < 0}` | pass, worst `1.9e−14` |
| K3 | `κ_j (joinC k z) = z` on the open **sector** of half-width `π/(k+1)` around `ζ_j` | pass, worst `1.3e−15`, `k ≤ 7` |
| K3b | and it FAILS just outside that sector | pass — 91 to 332 failures per `k`, i.e. the hypothesis is load-bearing |
| K4 | `κ_j` is continuous on `{Re w < 0}` (the cut of `arg(−w)` is the positive reals) | pass, no jump above `4e−6` at step `1e−6` |
| K5 | the `k+1` branches are distinct | pass, minimum angular separation `2π/(k+1)` |
| K6 | **`Ψ_k ∘ chart_j = sphereChart`**, on the sphere, at rank `n` | pass, worst `6.8e−15`, `n ∈ {2,3,4}`, `k ≤ 5` |
| K6b | `chart_j` lands on the unit sphere | pass, worst `‖·‖² − 1` of `6.7e−16` |

The correction, because it changes the Lean statement.  My first K3 asked for
`κ_j ∘ joinC k = id` on a Euclidean ball of radius `0.2` around `ζ_j`, at every `k`.  That
is **false** for `k ≥ 6`: the sector half-width is `π/(k+1)`, which is `0.449` at `k = 6`
and `0.393` at `k = 7`, so a `0.2` perturbation can carry the image across into a
neighbouring branch — 7 violations of 2800 at `k = 6` and 13 of 3200 at `k = 7`, each with
error `≈ 1`, which is exactly the distance to the next root.  **The right hypothesis is the
sector, not a ball, and it must be carried into Lean**; the ball version would have been an
over-claim that the `k = 1` and `k = 2` cases hide.  Note which half survives unconditionally:
`joinC k ∘ κ_j = id` needs no hypothesis beyond `Re w < 0` at all, and that is the half the
chart identity `Ψ_k ∘ chart_j = sphereChart` uses — so `chart_j` is injective for free (a map
with a left inverse is injective), and the sector is needed only for the *inverse* map, i.e.
for `chart_j` to be a homeomorphism onto an OPEN neighbourhood of `z_j`.

### 0.3b File E, scoped but deliberately NOT authored yet

Two reasons, both worth stating rather than leaving as silence.  First, `sp-design` has not
signed off on §0.3a, and the programme note's rule is that no Lean is authored for a
statement whose proof is not agreed at lemma-list precision.  Second, and this is the
one I would defend independently: **authoring a large file in idioms that the first probe
has not yet validated multiplies one style error by the size of the file.**  Files A–D use
the `Fin`-splitting, `WithLp`, `Fintype.sum_equiv` and `.comp'` idioms for the first time in
this lane; until a `Built` line says they elaborate, a fifth file in the same idioms is
unverified mass rather than progress.

What is scoped, so the next resume does not re-derive it.  The rank-`n` chart of `S^{2n+1}`
at `−e₀` has source `ℝ × (Fin n → ℂ)` (the imaginary part of coordinate `0`, plus the other
`n` coordinates entire) and reads

```text
  sphereChartVec n (c, v)  =  Fin.cons ((c : ℂ) * I − (weight : ℂ)) v ,
  weight (c, v)            =  √(1 − (c² + ∑ⱼ ‖vⱼ‖²)) ,
  eulerLinearModel n (dc, dv, dy) = Fin.cons ((dc : ℂ) * I / 2 − (dy : ℂ)) (fun j => dvⱼ / 2)
```

with injectivity and surjectivity by the same explicit-inverse arguments the rank-two file
uses (the surjectivity witness at rank `n` is `((2·(z 0).im, fun j => 2 · z j.succ), −(z 0).re)`),
`Fin.cases` in place of `fin_cases` throughout, and no determinant, orientation or inner
product anywhere.  **One decision is open and should be made with a compiler in reach, not
without one:** whether `eulerLinearModel n` is a structure instance with `map_add'`/
`map_smul'` proved by `simp only [Pi.add_apply, Fin.cons_zero, Prod.fst_add, Prod.snd_add]`
plus `push_cast; ring` (the rank-two file's shape, but its `simp; ring` is exactly the
pattern `FLEET_TRAPS` records as stranding `ring` when `simp` happens to close the goal), or
assembled from bundled pieces — `LinearMap.pi (Fin.cases c₀ cⱼ)` with
`c₀ = mulLeft ℝ (I/2) ∘ₗ ofRealLm ∘ₗ fst ∘ₗ fst − ofRealLm ∘ₗ snd` — which has no field
proofs at all and therefore no `simp` to strand, at the cost of four more Mathlib names to
get right.  I would take the bundled route and pay the names.

Names checked at the pin `81a5d257` so the next resume does not re-check them:
`LinearMap.pi` (`LinearAlgebra/Pi.lean:56`) with `LinearMap.pi_apply` (`:62`),
`LinearMap.proj` (`:87`) with `proj_apply` (`:100`),
`Complex.ofRealCLM : ℝ →L[ℝ] ℂ` (`Analysis/Complex/Basic.lean:326`, with `ofRealCLM_apply`;
note the table there lists `ofRealCLM`, and a bare `ofRealLm` is NOT what to reach for),
`LinearEquiv.toContinuousLinearEquiv` (`Topology/Algebra/Module/FiniteDimension.lean:371`,
which is what the rank-two file already uses),
`Fin.cons_zero`/`Fin.cons_succ` (`Data/Fin/Tuple/Basic.lean:120,123` — both proved by
`simp [cons]`, so do NOT assume they are `rfl` in a `show`),
`continuous_finsetSum` (`Analysis/Seminorm.lean:1165`; the `continuous_finset_sum` spelling
is deprecated and therefore a hard error under `-DwarningAsError=true`, `FLEET_TRAPS` line 11).
`LinearMap.mulLeft` I did NOT find where I expected it; the substitute is the scalar action
`(Complex.I / 2 : ℂ) • Complex.ofRealCLM`, which needs `SMulCommClass ℝ ℂ ℂ` and should be
checked before it is written.

### 0.4 The obligations, as named `Prop`s

Two are `sp-oddside`'s and I cite them rather than restate them; the rest are mine.  The
`Prop`s go in with docstrings before any proof, per §3 of the programme note.

| `Prop` | meaning | owner |
|---|---|---|
| `LocalSplit` (`LIXKCount`) | `x = ∑ i, ρ_i(x_i)` | `sp-oddside`, rank-free, cited |
| `LocalClassesAgree` (`LIXKCount`) | `j_i(x_i) = c` for every `i` | `sp-oddside`, rank-free, cited; at `p = 2` discharged from an `F₂`-line having one nonzero element |
| `KGen.SphereModel n` | `Nonempty (↥(unitVectors (Fin (n+1))) ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2n+2))) 1))` | **this lane**, file A |
| `KGen.PuncturedBase n dd` | `∀ z, PuncturedAcyclic (↥sphereOne × Gen.baseM n dd) (KGen.lixTopDegree n dd) z` | **this lane**, file B |
| `KGen.KZeroLocus n k` | the section vanishes exactly on the `k+1` points `(southPole, (ζ_j e₀, basePoint))` | **this lane**, file D |
| `KGen.LocalNonzero n k` | `x_{i₀} ≠ 0` — the one-zero computation at `−e₀`, at rank `n` | **this lane**, file E; the heavy item |
| `Gen.HasStepAUnitary`-with-`Ψ_k` | `∀ m, G m *ᵥ (e₀, 0) = (Ψ_k x, 0)` | `sp-tower`/`sp-powers`; a binder here, never discharged here |

### 0.5 Which bridges are `rfl`, predicted

Stated before probing, so the prediction is falsifiable.  `sp-tower`'s rule is the
discriminator: a bridge that crosses only `Fin 3` versus `Fin (2+1)` and a numeral versus
`Fin.last`/`0` is a kernel-level literal question and is `rfl`; a bridge that crosses a
**`Decidable` instance written two different ways** is not.

| bridge | prediction | reason |
|---|---|---|
| `KGen.eZero 2 = eOne` | `rfl` | both `Pi.single 0 1`, one `DecidableEq (Fin 3)` on both sides |
| `KGen.psiVec 2 k = psiVec k` | `rfl` | both `Function.update x 0 (joinC k (x 0))` |
| `KGen.kZeroVec 2 k j = kZeroVec k j` | `rfl` | both `Pi.single 0 (kRoot k j)` |
| `KGen.kRot 2 k m = kRot k m` | `rfl` | both `Function.update x 0 (kUnity k ^ m * x 0)` |
| `KGen.lixTopDegree 2 dd = lixTopDegree dd` | `rfl` | `2*(∑ dd) + (2*2+2)` versus `2*(∑ dd) + 6`, numeral arithmetic |
| `KGen.aVecK 2 = aVecK`, `KGen.bVecK 2 k = bVecK k` | `rfl` | follow `eZero`/`psiVec` |
| `KGen.unitVectorsHomeo 2 = unitVectorsThreeHomeo` | **not `rfl`, and not stated** | different constructions (an index `Equiv` versus a `![…]` literal); the statements agree, the terms do not, and nothing needs them to |
| `KGen.hbase 2` typechecks as `hbase_lix` | yes | `PuncturedAcyclic (↥sphereOne × ↥(unitVectors (Fin (2+1)))) (2*2+2) w`; both indices are literals |

The last row is the cheap cross-check that the generic statement really is the rank-two one,
and it costs one line.  I state it.

### 0.6 Model tests — **ALL PASS**, 254 checks, 0 failures

`scratch/sp-oddside-n/oddside_n_modeltest.py` on MSI (source in this session's scratchpad
`sp/`), run at ranks `n ∈ {2, 3, 4}` and `k ≤ 6`, in **my** coordinates (`Fin (n+1) → ℂ`
with the `Function.update` spelling) rather than `sp-design`'s or `sp-oddside`'s, so a
coordinate slip between the three spellings cannot hide.

| test | claim | result |
|---|---|---|
| A1 | `Ψ_k` preserves every coordinate's modulus | pass, `n ≤ 4`, `k ≤ 6` |
| A2 | the `k+1` claimed points are zeros | pass, residual `≤ 3.7e−15` |
| A2b | they are distinct | pass, minimum separation `1.0` at `k = 5` |
| A2c | **all lie on the equator** `Re (x (Fin.last n)) = 0` | pass, exactly `0` |
| A2d | **none is a suspension point `±e_last`** | pass, distance `1.414` at every rank |
| A3b | no stray zero, by descent from the 20 lowest-residual samples of 40000 | pass, 0 strays |
| A4 | `Ψ_k ∘ ρ^m = Ψ_k`, and `ρ^j z_0 = z_j` | pass, `0` violations, orbit residual `0` |
| B1 | **the `k+1` local derivatives of the section are literally one matrix** in the `ρ^j`-transported frames | pass, spread `≤ 1.9e−10` |
| B2 | each is invertible | pass, smallest singular value `0.5000` at every rank and every `k` |
| C1–C4 | `cxIdx n : (i,b) ↦ 2i+b` is a bijection with inverse `(k/2, k%2)`, and `∑ y_k² = ∑ ‖x_i‖²` under it | pass, `n ≤ 6` |

Three things worth recording beyond "pass".

* **The determinant is `−(k+1)/2^{2n+1}`**: `−0.0625 = −2/32` at `n = 2, k = 1`, which is
  `sp-oddside`'s measured `det J = −(k+1)/32` at rank two on the nose.  Two lanes, two
  coordinate systems, the same number — this is the cross-lane check that the rank-`n`
  section really is theirs at `n = 2`.
* **`sp-oddside`'s vacuity trap was loaded into the test from the start**: the derivative is
  evaluated at circle coordinate `y = 0` (`τ = 1/2`), which is where the zero is, and the
  source dimension asserted is `2n+2` (`2n+1` sphere plus one circle) with invertibility
  rather than a rank claim.  At `y = −1` the derivative degenerates to `−e₀ dy` and B1 would
  pass at every `k` while saying nothing.
* **One check is weaker than it looks and I am not counting it.**  A3, "no low-residual
  random sample is far from the `k+1` zeros", reported `0 of 0`: on a high-dimensional
  sphere no random sample gets within `1e−3` of the zero set at all, so the check is
  vacuous.  A3b, the descent, is the one that carries the content.  The mathematics is in
  any case immediate — the residual is `|joinC_k(x₀) + 1|² + ∑_{i≥1} |x_i|²`, so it
  vanishes only when `x_i = 0` for `i ≥ 1` and `joinC_k(x₀) = −1` — and that is exactly the
  shape the Lean proof of `psiVec_eq_neg_eZero_iff` takes.

### 0.6a The tests as originally planned

On MSI under `scratch/sp-oddside-n/`, in **my** coordinates (`Fin (n+1) → ℂ` with the
`Function.update` spelling), at rank `n = 3` as the launch message directs and at `n = 2`
as the calibration:

1. the zero count — `Ψ_k x = −e₀` has exactly `k+1` solutions on `S^{2n+1}`, all of the form
   `ζ_j e₀`, none of them on the wall, all on the equator `{Re (x n) = 0}`, with a random
   descent search for strays;
2. the local derivative — the derivative of `(u, x) ↦ (1−τ)e₀ + τ Ψ_k(x)` **at the zero,
   i.e. at circle coordinate `u = 0` (`τ = 1/2`)**, is the same matrix at all `k+1` zeros
   once the source frame is transported by `ρ^j`, and is of full rank `2n+1`.
   `sp-oddside`'s trap is loaded into this test from the start: at `u = −1` the derivative
   degenerates and the test passes vacuously, so `‖S(zero)‖ = 0` and the rank are both
   asserted in the same run;
3. the index arithmetic of file A — that `cxIdx n : Fin (n+1) × Fin 2 ≃ Fin (2n+2)` given by
   `(i, j) ↦ 2i + j` is a bijection and that `∑_k y_k² = ∑_i |x_i|²` under it, for `n ≤ 6`.
   This is the one that decides whether the `Fin` arithmetic in file A is stated the way
   `omega` can close it.

---

## GREEN (with job counts)

Nothing yet.  A warm-up probe of the rank-two closure I build against is running on the
cold clone `quant-collapse` (`laneprobe-20260910-143021.log`,
`purged 2852 stale artifact sets (source-newer=177, import-newer=2675) of 4732 oleans`); it
is not a claim about any file of mine and will not be cited as one.

## AUTHORED, UNVERIFIED

Four files, all leaves, nothing imports them, no `sorry` (lexical scan: 0 hits).

| file | contents |
|---|---|
| `CharClass/LIXKGenSphere.lean` | `KGen.cxFwd/cxBwd/cxIdx`, `reIm` with `sum_reIm_sq`, `cxToEuc`/`eucToCx` with both round trips, `normSq_cxToEuc`, the two continuities, **`KGen.unitVectorsHomeo n`**, `isZero_cohomology_sphereOdd`, `kunnethFactor_unitVectors` and its punctured companion, `puncturedAcyclic_unitVectors`, `isZero_cohomology_circle`, **`KGen.hbase n`**, `hbase_two_eq_hbase_lix` |
| `CharClass/LIXKGenPunctured.lean` | `KGen.lixRank`, `KGen.lixTopDegree` with `lixTopDegree_eq_two_mul_lixRank`, `baseNilHomeo`, `baseSnocHomeo`, **`KGen.puncturedAcyclic_lixBase n`**, `puncturedAcyclic_lixBase_topDegree`, **`KGen.puncturedVanish_finite`**; bridges `lixTopDegree_two`, `puncturedAcyclic_lixBase_two` |
| `CharClass/LIXKGenMap.lean` | `KGen.eZero`, `last_ne_zero`, `re_neg_eZero_last`, `negEZero`; `psiVec` with modulus/continuity/`psiVec_apply_last`/`psiVec_zero_eq`; `kZeroVec`, `kZero`, `kZero_injective`, `re_kZeroVec_last`; **`psiVec_eq_neg_eZero_iff`**; `kRot`, `psiVec_kRot`, `kRot_kZeroVec_zero`; six `n = 2` bridges |
| `CharClass/LIXKGenSection.lean` | `KGen.aVecK`, `bVecK`, `isMTSectionData_manuscriptDataK`, `lixKSection`, `lixKZero`, **`lixKSection_eq_zero_iff`**, `lixKZeroSet` with finiteness and non-emptiness, `lixKSection_ne_zero_of_notMem`; six `n = 2` bridges |

Import closure of the four together: **188 `GroupApproximation` modules**, and
`ChernTotalRing` is not among them — the coefficient-generalisation front that has been
reddening other lanes is outside this deliverable entirely.

## NEEDS

* **`sp-oddside`**: `LIXKCount`, `LIXKStepC`, `LIXKStepCTwo`, `LIXKPunctured` to keep their
  rank-free shape.  If any of them gains a rank-two hypothesis my wiring breaks silently,
  because it cites them at rank `n`.  Asked by `SendMessage`.
* **`sp-oddside`**: whether `LIXKRelativeMV` (the `LocalSplit` route) is rank-free.  If it is,
  I budget nothing for it.
* **`sp-tower`**: whether they own a rank-generic `lixRank`/`lixTopDegree` and a rank-generic
  `baseSnocHomeo`/`baseNilHomeo`, or whether those are mine.  Asked; I proceed as if they
  are mine and will delete my copies if theirs land first.
* **`sp-tower`**: `Gen.cVec` to stay indexed by the point of `Y` alone.
* **`sp-design`**: their §1.3 ruling — the local model at `−e₀` done generically in a unit
  vector `a` plus an ℝ-linear isometry `L` onto `a^⊥`, not as a `Fin`-relabelling — is what I
  am writing.  `sp-oddside` asked for the same ruling and recommended the same answer.

## TRAPS

Both appended to `notes/lix-lane-reports/FLEET_TRAPS.md`.

* `CharClass/CohomologySphere.lean` being generic in the dimension while
  `CharClass/LIXStepESphereModel.lean` is not is the shape of trap that costs a lane a day:
  the file whose NAME says "sphere" is fine and the file whose name says "the LIX Step E
  base" is where the rank is welded in.  Grep for the `![…]` literal, not for the word
  sphere.  My launch message budgeted the sphere cohomology as the first sub-deliverable and
  it was already done; the actual work was one homeomorphism and four re-citations.
* A local inverse of a `k`-fold map lives on a **sector**, not on a ball, and the difference
  is invisible at small `k`.  My first `κ_j` test asked for `κ_j ∘ joinC k = id` on a
  Euclidean ball of radius `0.2` at every `k`; it passed at `k ≤ 5` and failed at `k = 6, 7`,
  because the sector half-width is `π/(k+1)` and a `0.2` perturbation carries the image into
  a neighbouring branch.  Test a `k`-indexed local statement at a `k`-dependent radius, and
  check which of the two compositions actually needs the hypothesis: here `joinC k ∘ κ_j = id`
  needs none beyond `Re w < 0`, so only the openness of the image does.
* `LemmaTwoZero.lean`'s parametricity is worth stating out loud, because two lanes have now
  independently confirmed it and a third might not: `mtSection_manuscript_eq_zero_iff` is
  free in the RANK as well as in `a`, `b` and `c`, because it is stated over abstract index
  types `ι`, `κ`.  Nothing in the zero-locus layer had to be generalised at any point of this
  deliverable.
