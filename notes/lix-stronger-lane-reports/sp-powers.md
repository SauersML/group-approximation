# Lane `sp-powers` — §1.3 items 1–3 of `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`

Clone: `cs-simplicity` (cores 80–87).  Owns: `GroupApproximation/Analysis/LIXPowers*.lean`
only; edits no existing file.  Model tests: this session's scratchpad
`sp/powers_modeltest.py`, mirrored on MSI at
`/projects/standard/hsiehph/sauer354/nonsofic_existence/scratch/sp-powers/`.

---

## 0. ψ_k — AGREED with `sp-design`

`sp-design.md` §2.1, written before this file existed, proposes
`Ψ_k(x) = (x₀^k/|x₀|^{k−1}, x₁, …, x_n)` on `S^{2n+1} ⊂ ℂ^{n+1}` with
`ρ = diag(ω, 1, …, 1)`.  That is the same map as the proposal below, arrived at
independently and for the same reason (`Σψ_k` is the same formula as `ψ_k`).  **There is
one `ψ_k` and it is this one.**  Their coordinates are adopted here; two points where their
version is sharper or corrects mine:

* the ρ-plane must **contain** `e₁` — it is the `x₀`-plane — not merely be non-orthogonal
  to it, which is what I first wrote.  The fixed set of `ρ` is `{x₀ = 0}` and `±e₁` are as
  far from it as possible.
* the local identity at the `k` preimages is **pre**composition,
  `ψ_k = (ψ_k near q₀) ∘ ρ^{−j}`; the program note's §1.3.2 has it as postcomposition.
  Both lanes derived the same correction.

Their §2.4 route to `u^k ≃ u ∘ ψ_k` is the same construction as §3 below — normalise `u` to
be `1` on the wall `W₀ = {x₀ ∈ ℝ_{≥0}}`, then the clamped-angle family — with two
refinements I have sent them: write the reparametrisation as a *self-map of `E`* rather than
a formula in `(t, w)`, which removes their gluing step (d) entirely because the map is
already continuous across the wall; and note that their step (a) silently owes
**path-connectedness of `U(n)`**, which Mathlib does not supply, and which may be avoidable
by contracting the wall to a point where `u` is already `1` (at `n = 2` the north pole lies
in the wall and `hopfSuspension` is exactly `1` there — model test A2).

**Proposal (as first written, now the agreed map).**  Write the equatorial space of
`S^{2n+1}` as
`E = ℂ ⊕ ℝ^{2n-1}` (at `n = 2`: `ℝ⁵ = ℂ_{a₀a₁} ⊕ ℝ³_{a₂a₃a₄}`), a point `y = (z, v)`, and
put

```text
Ψ_k (z, v) = (z^k / |z|^{k-1},  v)          ψ_k := Ψ_k restricted to S^{2n}
```

(in Lean, `Analysis/LIXPowersJoinPower.lean`, indexed as `joinPow e₁ e₂ k` with the shift
`z^{k+1}/|z|^k` so that `k = 0` is the identity and no `1 ≤ k` side condition is carried).

Four virtues, in the order the program needs them:

1. **`Ψ_k` is norm-preserving on all of `E`**, because `|z^k/|z|^{k-1}| = |z|`, and it is
   positively homogeneous.  So *the cone of `ψ_k` is `Ψ_k` itself*, `Σψ_k` is the chart map
   `(t, ν) ↦ (t, Ψ_k ∘ ν)` — the clutching coordinate `Re (x n)` is fixed *by construction*
   — and item 3 collapses to `coneMat Ω (Ψ_k y) = coneMat (Ω ∘ Ψ_k) y`, three rewrites.
   This is the property no other candidate had, and it is why I recommend this one.
2. **ρ-equivariance.**  `ρ (z, v) = (ω z, v)`, `ω = exp(2πi/k)`, has order `k` and
   `Ψ_k ∘ ρ = Ψ_k`.  Fixed set: the subsphere `{z = 0} ≅ S^{2n-2}`.
3. **Zero count and local branches.**  For `q = (z₀, v₀)` with `z₀ ≠ 0`, `ψ_k^{-1}(q)` is
   the free ρ-orbit of `(|z₀|·(z₀/|z₀|)^{1/k}, v₀)`: exactly `k` points, a local
   homeomorphism at each, and **all `k` local Jacobians equal `+k`** — the same
   orientation, which is what §1.3.4 needs when it says every local contribution is
   literally equal.  Model-tested at `k = 2, 3, 6` on `S⁴` (tests B4–B6).
4. Degree `k` (the join of `z ↦ z^k` with the identity of `S^{2n-2}`).  Nothing downstream
   uses the degree, so it is never proved.

**CONSTRAINT ON THE NOTE'S §1.3.2, settled.**  Requirement 3 needs `−e₁ ∉ {z = 0}`.  The
program note says the ρ-plane is "a plane **not containing** `e₁`"; that is the wrong side.
The weakest correct form is "not *orthogonal* to `e₁`" (what I first wrote); the form
`sp-design` adopts, and the one this lane now uses, is the strongest and simplest: the
ρ-plane **is** the `e₁`-plane, so the fixed set of `ρ` is `{x₀ = 0}` and `±e₁` are as far
from it as a point can be.  With `e₁` orthogonal to the ρ-plane instead, `ψ_k^{-1}(−e₁)` is
a single point and `ψ_k` is not a local homeomorphism there.  Both lanes reached this
independently.

## 0.1 Renormalising the seam generator is FREE — and cheaper than I first said

**SUPERSEDED, and the correction matters.**  I first reported that the load-bearing
observation was the homotopy `θ ↦ (A_θ ũ)^k · ũ^{-k}`, which contracts `u^k ũ^{-k}` to `1`
even when the correction `a` is not central.  That argument is correct, and it is the right
argument *if the gauge lemma asks for a disc unitary*.  It does not: the gauge lemma I
landed asks only for a **ball unitary** — continuous and unitary on the closed unit ball,
with no condition at the centre — and `IsDiscUnitary.map_zero` is never used by it.  With
that, no homotopy is constructed anywhere and **path-connectedness of `U(n)` is not owed by
the program**.

The renormalisation, in full (`Analysis/LIXPowersNormalise.lean`):

* `wallRetract e₁ e₂ (z, v) = (−|z|, v)` is norm-preserving and positively homogeneous,
  hence an `IsRadialMap`, hence `A := U ∘ wallRetract` is a **ball unitary** for free.
* `ũ := Aᴴ · U` is a ball unitary, and `ũ ≡ 1` on the wall because `wallRetract` is
  idempotent — which is precisely the hypothesis `pinchIdentification_angleRepar` takes.
* `clutch(u) ≅ clutch(ũ)`: gauge factor `A`.
* `clutch(u ∘ ψ) ≅ clutch(ũ ∘ ψ)`: gauge factor `A ∘ ψ`, again a ball unitary because `ψ`
  is radial.
* `clutch(u^m) ≅ clutch(ũ^m)`: gauge factor `u^m · (ũ^m)ᴴ`, a product of ball unitaries.

The mathematical content is only that `U ∘ wallRetract` factors through the wall, which is
a disc, so it extends over the ball by the very same formula.  Nothing about `π₀(U(n))`
enters.  The two candidate corrections I tabulated earlier (the scalar `d`, and the `σ₃`
correction on the ρ-fixed sphere) are no longer needed for anything: `wallRetract` supplies
the normalisation the join power actually wants, on the nose.

## 0.15 Cross-lane: two corrections sent to `sp-design`

`sp-design.md` §2.5 records the convergence and adopts both of my refinements, but it
adopts them against an earlier version of my argument.  Two corrections sent:

* **The `θ ↦ (A_θ ũ)^k ũ^{−k}` homotopy is withdrawn**, not weakened.  What
  `clutchEquiv_normGen_pow` actually does is take the gauge factor `C := u^m · (ũ^m)ᴴ`, a
  product of ball unitaries, with `u^m = C · ũ^m` on the ball, and apply the left gauge
  lemma once.  No homotopy, and the "easy to get wrong because `A` is not central" caveat
  goes with it.
* **The wall is the NEGATIVE real axis in the Lean**, not the positive one: Mathlib's
  `Complex.arg` cuts on the non-positive reals and that is where my clamp saturates.  Their
  `π(x) = (|x₀|, x₁, …)` must read `(−|x₀|, x₁, …)` when citing my file, or the `ũ` they
  specify is `1` on the wrong disc and the pinch identification does not fire.  This is also
  why the target carries the sign, `joinCneg k = (−1)^k · joinC k`.

Their `F_p` warning about `RelativeLineHomotopy` being mod-2-only **does not touch this
lane**: checked by imports, not by reasoning.  No file of mine imports or mentions it, none
uses cohomology, and every comparison in the chain is matrix algebra plus point-set topology
— explicit partial isometries checked by multiplying blocks.  There is no relative pullback
anywhere in it.

Independent confirmation worth recording: their canonical-basis computation gives
`d(ψ_k)_{q_j} = diag(k, 1, …, 1)` at every `j`, and my oriented-frame computation gives
`det = +k` at every `j`.  Two different methods, same answer, including that all `k` local
degrees are `+1`.

## 0.2 What I need from you if you pick a different ψ_k

Exactly this, and nothing else:

* a continuous `Ψ : E → E` with `‖Ψ y‖ = ‖y‖` and `Ψ (r • y) = r • Ψ y` for `r ≥ 0`
  (Lean: `Powers.IsRadialMap`);
* a family `P : ℕ → ℝ → E → E`, continuous in `(θ, y)` for each index, with `P j 0 = id`
  and `‖P j θ y‖ ≤ 1` for `‖y‖ ≤ 1`;
* the identification `∀ y, ‖y‖ = 1 → reparProd W P 1 y k = W (Ψ y)`
  (Lean: `Powers.PinchIdentification W P Ψ k`).

Everything else on my side is already generic in that data and green.

---

## 0.3 FINDING: the clutching layer has no consumer, and `clutch u ≅ F` is unproved

Checked before writing the export, in both directions:

* `clutchMat`, `coneMat` and `clutchOfChart` occur **only** in `Analysis/LIXClutching.lean`
  and in this lane's own `LIXPowers*` files.  No `CharClass` file mentions them.
* Only three files import `LIXClutching`: `LIXGeneratorUnitary`,
  `LIXObstructionComplementUnitary`, and this lane's `LIXPowersGauge`.  `LIXGeneratorUnitary`
  does not use `clutchMat` at all.

So the live Corollary-4 chain (`LIXLemmaSixField` → `LIXLemmaSixCompare` →
`LIXLemmaSixCor4`) never touches the clutching layer: it goes from a null-homotopy of the
stage unitary straight to a unitary field conjugating `EHmat` to `FHmat`.  And
`clutch u ≅ Fproj` is **not proved anywhere** — `LIXGeneratorUnitary`'s module docstring
says why, the hemisphere sections whose seam discrepancy is `u` being exactly what is not
constructed there.

**But it is off the critical path** (checked after the first version of this section, which
did not say so).  `CharClass.FHmat m = Vmat m − sProj m` with
`sProj m = fromBlocks (rankOneProj (bVec m)) 0 0 0` and `bVec m = m.1`, the tautological
point of `S⁵`, and `FHmat_eq_fromBlocks` already proves `FHmat = (1 − b bᴴ) ⊕ H`.  So the
manuscript's object is defined **directly from the section**, and `FHmat_k` of §1.6 is the
same definition with `b = x ∘ Σψ_k`.  Nothing on that side goes through clutching, so
**nobody has to prove `clutch u ≅ Fproj`**; the gap is real and irrelevant.

**Consequence for this lane.**  The hypothesis `hP` of `clutchEquiv_pow_of_clutch_eq` and of
the export is a live undischarged input, not a formality, and nobody owes it.  Two
interfaces are possible and they cost differently:

| interface | statement | cost |
|---|---|---|
| **(a) clutched**, what is built | `clutch(u^{k+1}) ≅ clutch(u) ∘ Σψ_k` | every step is a gauge step; `U(n)` never enters; **needs `clutch u ≅ F ⊕ H`** |
| **(b) bare homotopy**, what Corollary 4 would consume | `u^{k+1} ≃ u ∘ ψ_k` through unitaries | plugs into `LIXLemmaSixField` unchanged; **needs `A ≃ 1` for `A = U ∘ wallRetract`** |

(b) does *not* follow from (a): `u = A·ũ`, and the bare homotopy needs `A` contracted while
the clutched statement does not.  But the contraction is cheap and concrete, not a general
theorem: the wall is a disc, so contracting it gives an explicit homotopy from `A` to the
constant `u(wall centre)`, and what remains is one explicit path from **one explicit matrix**
to `1` — at `n = 2` a diagonal one, a line of Lean.  So the correct footnote to "`U(n)`
path-connectedness is struck" is: struck for (a), and for (b) replaced by one concrete path,
never the general theorem.

**SETTLED by the lead, 2026-09-10: (b) is the primary export and (a) is off the critical
path.**  The Corollary-4 chain glues the two hemisphere frames of `LIXGeneratorUnitary` into
a unitary field `G` with `G e₃ = x`; for the `k`-th power the same construction with the
frames pulled back along `Σψ_k` has seam `u ∘ ψ_k` and takes `e₃` to `x ∘ Σψ_k`.  So what it
consumes is the homotopy of *maps*, which is `Analysis/LIXPowersHomotopy.lean`.

**And the `ũ`-to-`u` step is never built**, so the `U(n)` footnote is withdrawn for good:
the endpoint witness is `ũ ⊕ 1_H` rather than `u ⊕ 1_H`, and nothing downstream
distinguishes them (`ũ = Aᴴ u` with `A` a ball unitary, so `ũ ⊕ 1` still contracts in
`U(n+1)`, `ũ ∉ U₀` iff `u ∉ U₀`, and the frames gauged by `A` on one hemisphere have seam
`ũ` and still take `e₃` to `x`).  Interface (b) is therefore **complete** as
`exists_homotopy_pow_comp_normGen`.

Consumers: **`sp-tower`** for the C*-side (they own `LIXGeneratorUnitary` and the stage
unitary); `sp-oddside` consumes nothing from this lane, only the substituted section
`b = x ∘ Σψ_k` on the `CharClass` side.

## 1. What `LIXClutching` already had, and what it did not

Checked line by line (1194 lines).

* **The gauge lemma is not there in the needed generality.**  What is there is the `b = 1`
  case, `exists_partialIsometry_of_isDiscUnitary` (l.859).  There is no statement comparing
  `clutch (a·b)` with `clutch (b)` for a non-constant `b`.
* `seamMat_conjTranspose_mul_self` / `seamMat_mul_conjTranspose` (l.261, l.326) are stated
  for **arbitrary** `f g κ m` with four hypotheses and the single seam relation
  `κᴴ gᴴ m = fᴴ`, so the *algebra* of the general gauge lemma is free; only the four
  continuity arguments had to be redone.
* `IsDiscUnitary.map_zero` is **never used** by `exists_partialIsometry_of_isDiscUnitary`,
  and it is not used by the gauge lemma either — hence the separate, weaker
  `IsBallUnitary`.  It *is* used by `isDiscUnitary_discOfHomotopy`.
* `IsSuspensionChart.comp` (l.1154) is the chart half of item 3 but not the
  clutching-function half.

## 2. The gauge lemma: why the factor goes on the RIGHT

With `f = ‖ν‖·(b·a)` and `g = ‖ν‖·b` at the equatorial direction `d`, the seam relation
forces, for the gauge `κ = Ω(seamPoint)` — *the same gauge as in `LIXClutching`, not a
conjugated one* —

```text
m = b(d) · Ω(seamPoint) · Ω(d)ᴴ · b(d)ᴴ
```

which on the collar `t ≤ −1/2`, where the seam parameter plateaus at `1` and
`seamPoint = d`, collapses to `b(d) b(d)ᴴ = 1`.  So `m` is **locally constant** near the
south pole (cheaper than the original file's argument), and `g` is already the target
`coneMat B ν`, so no final conjugation step is needed at all.

Putting the gauge factor on the left instead forces a conjugated gauge
`κ = b(d)ᴴ Ω(seamPoint) b(d)`, whose continuity at the *north* pole then needs
`Ω 0 = 1` plus an entrywise conjugation estimate.  The left version is therefore derived
as a corollary instead, from `a·b = b·(bᴴ a b)`.

## 3. Eckmann–Hilton: the unconditional half, and where basepoints really enter

The half the powers argument consumes has **no hypothesis on `u` at all**:

> Let `P j` be a continuous family of self-maps of the closed unit ball, one per factor
> `j < k`, with `P j 0 = id`.  Then `u^k` is homotopic through unitaries to the ordered
> product `∏_{j<k} (u ∘ P j 1)`.

The homotopy is `H θ y = ((u y)^k)ᴴ · ∏_{j<k} u (P j θ y)`; all the content is in the
*choice* of `P`.  Basepoints enter exactly once and only to **rename** the answer: to
collapse the ordered product into a single composite `u ∘ ψ_k`.  That is
`Powers.PinchIdentification`, a named `Prop`, owned by `sp-design`.

Two concrete families, both fully model-tested:

* **the vertical slab family** `σ_{j,θ}(s) = clamp((1+θ(k−1))s + θ(k−1−2j), −1, 1)` with
  `R_σ(y) = √(1−σ(s)²)·‖y‖·dir(y − ⟨e,y⟩·e) + σ(s)·‖y‖·e`, `s` the *normalised* height
  `⟨e,y⟩/‖y‖` (so that `R_σ` is radial, not merely a self-map of the sphere).  Each `R_{σ_{j,1}}` *is* an honest
  continuous self-map of `S^m` (C1–C3).  But the **vertical pinch itself is discontinuous**
  at every interior interface — slab `j`'s top goes to `N`, slab `j+1`'s bottom to `S`, a
  jump of `2` (C4) — so it cannot serve as `ψ_k` for item 3, only `u ∘ (pinch)` is
  continuous.  With `u(N) = u(S) = 1` the ordered product is exactly the single pinched
  composite (D6); without it the discrepancy is exactly the central factor
  `u(S)^{k−1−i}`, which is `−1` on the odd slabs and `+1` on the even ones (D4).
* **the angle family** `A_{j,θ}(z, v) = (|z| e^{i c_{j,θ}(arg z)}, v)`,
  `c_{j,θ}(φ) = clamp((1+θ(k−1))(φ+π) − 2πθj, 0, 2π) − π`.  Here the two ends of the pinch
  interval are the *same set* (the negative real axis), so the interfaces match
  automatically: the family is norm-preserving, the identity at `θ = 0`, and continuous
  both across the cut and at `z = 0` (E1–E4), the homotopy is unitary with `H_0 = u^k`
  (E6, E7, E8), and **the pinch identification holds exactly**, `∏_j u(A_{j,1} y) =
  u(Ψ_k y)`, when `u ≡ 1` on the wall `W₀` (E5) — and fails for the raw generator (E9).

**Recommendation: the angle family with `Ψ_k`.**  It is the only pair for which `ψ_k` is a
genuine continuous self-map *and* the identification is a formula.

## GREEN (with job counts)

**Single-log confirmation, DISCHARGED.**  Probe `cs-simplicity`, 2026-09-10, after the
clone was wiped and re-copied fresh and after I deleted every artifact of my own modules
(they were absent in the fresh clone anyway, so all ten had to build from source).  One log,
four `Built` lines, no `Replayed` on any module of mine:

```text
✔ [7099/7131] Built GroupApproximation.Analysis.LIXPowersGauge       (51s)
✔ [8671/8679] Built GroupApproximation.Analysis.LIXPowersNaturality  (31s)
✔ [8672/8679] Built GroupApproximation.Analysis.LIXPowersEH          (30s)
✔ [8673/8679] Built GroupApproximation.Analysis.LIXPowersJoinPower   (30s)
```

**PENDING RE-CONFIRMATION (lead, fleet-wide, 2026-09-10).**  That probe predates the
`laneprobe.sh` purge patch.  `sp-oddside` found that the artifacts copied into every clone
include oleans OLDER than their sources (233 of 5478 modules in one clone), and lake replays
those **silently, with no line in the log at all**, so the symptom is a red or an
inconsistency in a file that is itself correct.  My closure imports `Analysis/LIXClutching`,
which `sp-tower` may have edited today, so the four `Built` lines above could have been
compiled against a stale dependency even though the modules themselves genuinely built.
The helper now purges every artifact set whose `.lean` is newer than its `.olean` before
building.  **Do not cite the block above until it is reproduced under the patched helper**;
that re-run is queued.

Once reproduced, that is the evidence the fleet rule asks for, and it replaces the
three-log account this section used to carry.  The same probe stopped at `LIXPowersAngle`, so `Pinch`, `Normalise`,
`Homotopy`, `Chain` and `Export` were never reached and remain unverified.

**On hard links, since the release note said zero.**  `find <clone>/.lake/build -type f
-links +1` returns 3418 files, and the first one I sampled *is* shared by inode with the
main tree — but it is in `Audit/`, link count 21, dated three weeks earlier.  Checking the
dependencies that actually matter, `LIXClutching`, `LIXBlockProjections` and
`CharClass/LemmaTwoStatement` are all **distinct copies with link count 1**.  So
`GroupApproximation` is clean and the residue is elsewhere; "zero hard links" and "hard
links exist" are both true of this clone, of different subtrees.  My own modules are the
easy case regardless, being new files with no main-tree olean to alias.

Contents, by deliverable:

* **item 2 (gauge lemma)** — `exists_partialIsometry_of_gauge_right`,
  `exists_partialIsometry_of_gauge_left`, `IsBallUnitary`, `gaugeCorr`.
* **the disc form of a null-homotopy** — `discOfHomotopy`, `isDiscUnitary_discOfHomotopy`
  (plateau on the inner half-ball: continuity at the centre is free, no compactness, `E`
  may be infinite-dimensional).
* **the lane's export** — `exists_partialIsometry_of_homotopy`: *homotopic clutching
  functions clutch equivalent projections*, no functional calculus, no local triviality.
* **item 1 (Eckmann–Hilton)** — `reparProd`, `exists_partialIsometry_pow_reparProd`,
  `PinchIdentification`, `exists_partialIsometry_pow_pullback`,
  `exists_partialIsometry_pow_pullback_map`.
* **item 3 (naturality)** — `IsRadialMap`, `coneMat_comp_radial`,
  `isSuspensionChart_comp_radial`, `clutchMat_comp_radial`,
  `clutchMat_comp_radial_pullback`, `splitSusp`, `isDiscUnitary_comp_radial`.

* **ψ_k itself** — `joinC`, `norm_joinC`, `continuous_joinC`, `joinC_smul`; the
  orthonormal-plane machinery `planeC/planeE/planeRest/planeSub` with
  `isRadialMap_planeSub`; and `joinPow`, `isRadialMap_joinPow`, `joinPow_zero`.  Stated for
  an orthonormal real pair `e₁, e₂` spanning the rotation plane; `sp-design`'s `x₀`-plane
  is the instance `e₁ := e₀`, `e₂ := i·e₀`.

No `sorry` anywhere (lexical scan: 0 hits in all four files).  Every file is imported only
by the lane's own files.  **Axioms checked**, by a temporary `#print axioms` block probed
and then removed: all 14 of

`exists_partialIsometry_of_gauge_right`, `_gauge_left`, `isDiscUnitary_discOfHomotopy`,
`exists_partialIsometry_of_homotopy`, `exists_partialIsometry_pow_reparProd`,
`_pow_pullback`, `_pow_pullback_map`, `clutchMat_comp_radial`,
`clutchMat_comp_radial_pullback`, `isSuspensionChart_comp_radial`,
`isDiscUnitary_comp_radial`, `isRadialMap_joinPow`, `isRadialMap_planeSub`, `joinPow_zero`

depend on exactly `[propext, Classical.choice, Quot.sound]`.  (`#print axioms` prints the
list across three lines when the declaration name is long, so a one-line grep sees only
some of them — count `depends on axioms` and grep the *following* lines.)

## AUTHORED, UNVERIFIED

Written during the probe hold (lead, 2026-09-10, cs-simplicity cold).  Both are
model-tested against the *exact* Lean formulas before authoring
(`sp/angle_modeltest.py`, tests F1–F16, all passing) but neither has been near a compiler.

* `Analysis/LIXPowersAngle.lean` — **the angle reparametrisation family**, the concrete `P`
  the Eckmann–Hilton step consumes.  `angleClamp`, `angleRaw`, `angleParam` (the clamped
  pinch angle, with `θ` clamped *inside* the definition so the family is continuous for
  every real `θ`), `angleC` with `norm_angleC`, `angleC_param_zero`, `angleC_smul` and
  `continuous_angleC`; the wall map `wallC` and the radial retraction `wallRetract`; the
  family `angleRepar` on `E` with `isRadialMap_angleRepar`, `angleRepar_param_zero`,
  `continuous_angleRepar`, `norm_angleRepar`, `angleRepar_eq_wallRetract`; and the general
  collapse lemma `reparProd_eq_single`.
* `Analysis/LIXPowersPinch.lean` — **the pinch identification**.  `joinCneg`/`joinPowNeg`
  (the join power rotated to the pinch basepoint, still an `IsRadialMap`), `slabIndex` with
  the three slab bounds, the exponential bridge `angleC_slab_eq_joinCneg`, and
  `pinchIdentification_angleRepar`, which is the instance of `Powers.PinchIdentification`
  that `exists_partialIsometry_pow_pullback` consumes.  With it, §1.3 items 1–3 close for
  the agreed `ψ_k`, modulo the one remaining hypothesis: `W` is the identity matrix on the
  wall.

* `Analysis/LIXPowersNormalise.lean` — **the renormalised generator**, deliverable 2.
  `ClutchEquiv` with `symm`/`trans` (the same shape as `CharClass.ContinuousMvNEquiv`, so
  the `Analysis/` files need not import `CharClass`); the plane-coordinate lemmas
  `planeC_add`, `planeC_planeE`, `planeC_planeRest`, `planeC_planeSub`,
  `planeRest_planeSub`, `planeSub_comp`, and `wallC_idem`/`wallRetract_idem`; then
  `wallPart`, `normGen`, `isBallUnitary_normGen`, `normGen_wall`, `wallPart_mul_normGen`,
  and the three gauge transports `clutchEquiv_normGen`, `clutchEquiv_normGen_pow`,
  `clutchEquiv_normGen_comp`.  **No homotopy is constructed and `U(n)` is never mentioned**
  (§0.1).

* `Analysis/LIXPowersChain.lean` — **the powers chain, assembled** (lead's deliverable 3,
  abstract half).  `norm_equator_mul`, `isClutchDatum_coneMat_of_ballUnitary`,
  `clutchMat_idem`, then `clutchEquiv_pow_pullback` — *the projection clutched by `u^{k+1}`
  is Murray--von Neumann equivalent to the projection clutched by `u` read at `Σψ_k`*, with
  no hypothesis on the generator beyond unitarity on the closed ball — plus the composite
  form `clutchEquiv_pow_comp`, the transported form `clutchEquiv_pow_pullback_map`, and the
  hand-off `clutchEquiv_pow_of_clutch_eq`.

**The vocabulary half of deliverable 3 is deliberately not authored here.**
`CharClass.ContinuousMvNEquiv` (LemmaTwoStatement.lean:98) and `Powers.ClutchEquiv` are the
*same* definition unfolded — `∃ w, Continuous w ∧ (∀ m, wᴴw = P m) ∧ (∀ m, wwᴴ = Q m)` — so
the bridge is `Iff.rfl`.  Writing it in an `Analysis/` file would put a `CharClass` import
(and `LemmaTwoParity`'s whole closure) under the clutching layer for the sake of one line.
It belongs in the file that already imports `CharClass`, i.e. `sp-oddside`'s.  What they
then need on top is `clutch u = FHmat`-with-the-transported-section, which is `Fin 3`-bound
until `CharClass.VIdx`/`baseM` go generic in `n` (`sp-tower`'s NEEDS).
`clutchEquiv_pow_of_clutch_eq` takes exactly that as its one hypothesis.

**A defect the assembly caught, which no probe would have.**  `reparProd` asks for
continuity of `P j` at *every* index `j : ℕ`, but `angleRepar e₁ e₂ k j` is continuous only
for `j ≤ k`: past `k` the top clamp end stops saturating at intermediate `θ` and the map
jumps across the cut.  The fix is `angleFam e₁ e₂ k j := angleRepar e₁ e₂ k (min j k)`,
which agrees with the intended family on every index the ordered product reaches, plus
`reparProd_congr` to move between the two.  This is worth generalising: **a hypothesis
quantified over all of `ℕ` will silently demand more than the construction provides, and
only assembling the chain exposes it.**

* `Analysis/LIXPowersHomotopy.lean` — **THE PRIMARY EXPORT.**  `exists_homotopy_pow_comp`:
  for a generator that is `1` on the wall, an explicit `G` with `G 0 = U^{k+1}`,
  `G 1 = U ∘ ψ_k` on the sphere, unitary at every `θ` and continuous in `(θ, y)`; and
  `exists_homotopy_pow_comp_normGen`, the same with no hypothesis on the generator beyond
  ball-unitarity.  The homotopy is the ordered product of the `k+1` angle
  reparametrisations.  No clutching, no contraction, no `U(n)`.
* `Analysis/LIXPowersExport.lean` — **the vocabulary bridge** (deliverable 3, second half).
  `clutchEquiv_iff_continuousMvNEquiv` is `Iff.rfl`; `continuousMvNEquiv_pow_of_clutch_eq`
  and `continuousMvNEquiv_pow_pullback_map` restate the chain in `CharClass` vocabulary.
  Index-generic on purpose: the `n = 2` specialisation is not a renaming, because the
  clutched projection has rank `4` in `Matrix (Fin 2 ⊕ Fin 2)` while `FHmat` has rank
  `3 + m` in `Matrix (VIdx dd)`, and the reindexing between them is *determined by* the
  missing identification (§0.3).  The rank is pinned exactly once, in the caller's choice of
  `P` and index type, and nowhere in the geometry.

**The single risky proof** is `continuous_angleC` at the branch cut.  Mathlib's
`Complex.arg` cuts on the non-positive reals, which is exactly where the clamp saturates,
so the cut costs one lemma instead of a change of coordinates: at a negative real the two
one-sided limits of `arg` are `π` and `−π`, `angleParam` is saturated at both, and
`exp (iπ) = exp (−iπ) = −1`.  The proof splits the neighbourhood as
`𝓝[{0 ≤ im}] ⊔ 𝓝[{im < 0}]` and uses
`Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero` and its `im < 0` twin, both
present at the pin `81a5d257`.

**The θ-clamp is load-bearing on one side only**, and the model test now says which
(`sp/branch_modeltest.py`, G1–G8, all passing).  Both clamp ends saturate for *every*
`θ > 0` and `j ≤ k`, so the family is continuous across the cut without any upper clamp;
it is `θ < 0` that breaks it, and there the break is real (45 of 140 sampled `(k, j, θ)`
triples jump by `2`).  So `min 1` in `angleClamp` is tidiness — it makes `angleParam k j θ`
constant in `θ` past `1` — and `max 0` is the part the continuity proof needs.  I keep both;
the note is here so that nobody later "simplifies" away the wrong one.

**One convention to flag to `sp-design`.**  My pinch basepoint is the *negative* real axis,
because that is where Mathlib puts the `arg` cut; theirs is the positive one.  The two
differ by the rotation `z ↦ −z` of the plane, which is why the target carries a sign,
`joinCneg k = (−1)^k · joinC k`, and why their retraction `x ↦ (|x₀|, x₁, …)` becomes
`x ↦ (−|x₀|, x₁, …)` here.  All the `ψ_k` properties are unaffected: `joinPowNeg` is
`joinPow` composed with a fixed rotation of the plane, so the `k` preimages and their common
orientation are the same set and the same sign, rotated.

## NEXT, in order (what a resume should do)

1. **Probe `LIXPowersAngle`, `LIXPowersPinch` and `LIXPowersNormalise`** as soon as the
   lead releases the clone, deleting all my modules' remote artifacts first so one log
   carries every `Built` line.
   Expect iteration in `continuous_angleC` (the cut) and in the real-arithmetic bounds of
   `slabIndex`; the mathematics is model-tested, the Lean is not.  Note that interpolating
   without `Complex.arg` is not an option to fall back on: at `θ = 0` the family must be the
   identity and at `θ = 1` the `(k+1)`-tupling, so the exponent `1 + θk` is genuinely
   fractional in between.
2. **DONE, authored** (`LIXPowersNormalise.lean`): the renormalisation, with the
   `U(n)` question closed negatively — it is not needed, see §0.1.
3. **DONE, authored** (`LIXPowersChain.lean`): the abstract half of the export.  The
   vocabulary half is one `Iff.rfl` in a file that already imports `CharClass`, plus the
   `clutch u = FHmat` identification, which is `Fin 3`-bound until `CharClass.VIdx`/`baseM`
   go generic in `n`.
4. Instantiate `isRadialMap_joinPow` at `sp-tower`'s generic-`n` equatorial space once it
   exists, and hand `sp-oddside` the `Φ` of `clutchMat_comp_radial_pullback`.

## OPEN QUESTION (asked, blocking nothing yet)

`IsBallUnitary U` asks for `U` continuous on all of `E` and unitary on the **closed ball**.
`Gen.genU n` is a formula in a unit vector, and `continuous_genU2` is proved only along
sphere-valued inputs, so `sp-tower` may not be able to supply it.  **My proofs do not need
the ball**: `angleFam`, `wallRetract` and `joinPowNeg` are all norm-preserving, so from a
unit vector the construction never leaves the unit sphere.  The minimal honest hypothesis is
`Continuous U` plus unitarity **on the sphere**, and if even global continuity is awkward
(the Householder denominators can vanish off the sphere) it localises to a shell
`1/2 < ‖y‖ < 2`, which the norm-preserving maps also never leave.  Asked `sp-tower` which of
the three they can supply; it is a mechanical edit in four files once known, and a wasted
probe round if guessed.

## NEEDS

* `sp-design`: nothing blocking.  For information: their §2.4(a) contraction and its
  appeal to path-connectedness of `U(n)` can be deleted from the route (§0.1), and their
  wall becomes the *negative* real axis to match Mathlib's `arg` cut.
* `sp-tower`: the generic-`n` seam generator, whenever it exists, so the renormalisation
  is written once rather than at `n = 2`.

## TRAPS

* A lane's private warm clone can lose every **untracked** `.lean` file between two probes
  (a clone re-warm wipes them).  The symptom is `Lean exited with code 1` with
  `no such file or directory (error code: 4294967294)` after a 200 ms "Building" line — it
  reads like a toolchain fault and is not one.  `laneprobe.sh` re-rsyncs on every call, so
  the fix is to run it again.  Consequence: **a green probe is not evidence the node still
  holds your file a minute later**, so a green claim must cite the probe that produced it.
  Appended to `notes/lix-lane-reports/FLEET_TRAPS.md`.
* `-DwarningAsError=true` makes `linter.unusedVariables` a hard error for a
  **structure-instance field** written `fun y hy => …` where `y` reaches the body only
  through the implicit argument of `hy`'s type.  The same shape inside a tactic block does
  *not* fire, so one file can carry both and only one reddens.  Write `fun _ hy => …`.
  Appended to `FLEET_TRAPS.md`.
* Authoring Lean during a probe hold: a self-review pass over the two new files, done with
  no compiler, caught six defects that would each have cost a probe round —
  `Nat.cast_le (α := ℝ).mpr h` (the ascription binds to the wrong term; it is
  `(Nat.cast_le (α := ℝ)).mpr h`), `induction (k + 1)` on a non-variable term, three uses of
  `positivity` on goals whose nonnegativity lives in a *hypothesis* it cannot see
  (`0 ≤ 2π · angleClamp θ · ((k:ℝ) − j)` needs `j ≤ k` and `mul_nonneg`, not `positivity`),
  and `rw [ContinuousAt]` where a `show` of the unfolded `Filter.Tendsto` is what actually
  works.  The pattern worth keeping: when writing blind, the defects are concentrated in
  *tactic* steps that depend on the ambient context, never in the statements.
* A third wrong test expectation, same shape as the first two: I asserted that the angle
  family must be discontinuous across the cut for `θ > 1` without the upper clamp, and it
  is not — at `φ = π` the raw angle is `2π(1 + θ(k−j)) ≥ 2π` for *every* `θ > 0` and
  `j ≤ k`.  The formula was right and the expectation was wrong.  Three for three: when a
  model test fails, suspect the assertion before the formula, because the formula has
  usually already been derived on paper and the assertion has not.
* Two of my own model tests were wrong before they were right, and both failures looked
  like real mathematics: (i) the sign of a local Jacobian is meaningless unless the tangent
  frames at source and target are oriented by the *ambient* orientation — the raw QR frames
  gave alternating signs and read as "the branches disagree"; (ii) a single sample point
  for "H₁ differs from the single composite" landed on an even-parity slab, where the
  central factor is `+1`, and read as "no discrepancy at all".  Sample every residue class
  the formula distinguishes, not one point.
