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

## 0.1 Renormalising the seam generator is FREE — the load-bearing observation

Any homotopy `u^k ≃ u ∘ ψ_k` built by *reparametrising the argument* — the only kind that
is a formula — is frozen where the reparametrisation is trivial, and there it degenerates
to a basepoint condition on `u`.  For `Ψ_k` in the angle coordinate that set is the **wall**
`W₀ = {(z,v) : z ∈ ℝ_{≥0}}` (`sp-design`'s name for it), and the condition is `u ≡ 1` on `W₀`.  The `n = 2`
generator fails it (model test A4/A5, E9).

This is **not fatal**, because renormalising `u` costs nothing.  If `u = a·ũ` with `a` a
disc unitary, then all three of

* `clutch(u) ≅ clutch(ũ)` — the gauge lemma, item 1;
* `clutch(u^k) ≅ clutch(ũ^k)` — because `θ ↦ (A_θ ũ)^k · ũ^{-k}` is a homotopy from
  `u^k ũ^{-k}` to `1`, so `u^k ũ^{-k}` is null-homotopic *even though `a` need not be
  central*;
* `clutch(u ∘ ψ_k) ≅ clutch(ũ ∘ ψ_k)` — because `a ∘ Ψ_k` is again a disc unitary
  (`isDiscUnitary_comp_radial`: `Ψ_k` maps the closed ball to itself and fixes `0`)

hold.  So the chain may be run with **any** disc-unitary renormalisation of `u`, and the
only remaining question for `sp-design` is which `ũ` is cheapest to write.  Two
candidates, both model-tested at `n = 2`:

| correction | what it fixes | test |
|---|---|---|
| the **scalar** `d(y) = exp(iπ(‖y‖ − ⟨e, y⟩)/2)` (a disc unitary, `d(0) = 1`) | `u(N) = u(S) = 1`, which is what the *vertical slab* pinch needs | D5, D6 |
| `a(y) = exp(−i θ(y) σ₃)`, `θ(y) = ‖y‖ · arccos(clamp(⟨e,y⟩/‖y‖))` (disc unitary: `θ(0) = 0`, `|θ| ≤ π‖y‖`) | `u ≡ 1` on the ρ-fixed sphere `{z = 0}` | A6 |

Neither is yet the `W₀` normalisation the join power wants; that is the open item, and it
is the only thing between the current green Lean and a discharged `PinchIdentification`.

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

Probe `cs-simplicity`, 2026-09-10, one probe, all four modules:
`Build completed successfully (2378 jobs)`, `EXIT=0`, `PROBE GREEN`, empty error index.
Every `✔ … Built <module>` line, no `Replayed`.  The clone's copies were checked
`md5sum`-identical to the local files after the probe (see the first TRAP below for why
that check is not optional here):

```text
ad50e1d1b5df5823c3e966e12cec8c77  LIXPowersGauge.lean
09412f4b9ba8ed57abb4d0b7909cba17  LIXPowersNaturality.lean
a0f9c186c0c2c1b41026fef2466673b0  LIXPowersEH.lean
34f6693d82ba2d8112aba9bfccd03676  LIXPowersJoinPower.lean
```

| module | in that probe |
|---|---|
| `Analysis/LIXPowersGauge.lean` | ✔ |
| `Analysis/LIXPowersNaturality.lean` | ✔ |
| `Analysis/LIXPowersEH.lean` | ✔ |
| `Analysis/LIXPowersJoinPower.lean` | ✔ |

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

* nothing.

## NEXT, in order (what a resume should do)

1. **Author the angle family** `A_{j,θ}` as a `ℕ → ℝ → E → E` in the `planeSub` vocabulary
   and discharge `PinchIdentification` for `joinPow`.  This is the last piece of §1.3 items
   1–3 and it is the *only* one with real Mathlib risk: the map goes through
   `Complex.arg`, whose cut is the non-positive reals, which is exactly where the clamp
   ends meet.  Three continuity obligations: away from `ℝ_{≤0}` (composition,
   `Complex.continuousAt_arg`), on `ℝ_{<0}` (both one-sided limits give `−|z|`, since
   `e^{iπ} = e^{−iπ}`), and at `0` (damped by `|z|`).  Everything else is already generic
   and green.  The alternative, interpolating without `arg`, does not exist: at `θ = 0` the
   family must be the identity and at `θ = 1` the `k`-tupling, so the exponent
   `1 + θ(k−1)` is genuinely fractional in between.
2. **The renormalisation `ũ`.**  `sp-design`'s retraction `π(x) = (|x₀|, x₁, …, x_n)` is
   itself an `IsRadialMap`, so `u ∘ π` is a ball unitary for free and the *gauge* step needs
   no contraction at all.  The contraction `u ∘ π ≃ 1` is needed only for the `u^k ↔ ũ^k`
   step, and there the open question is whether the wall can be contracted to a point where
   `u` is already `1` (at `n = 2` the north pole lies in the wall and `hopfSuspension` is
   exactly `1` there) — if it can, the program never owes path-connectedness of `U(n)`.
3. Instantiate `isRadialMap_joinPow` at `sp-tower`'s generic-`n` equatorial space once it
   exists, and hand `sp-oddside` the `Φ` of `clutchMat_comp_radial_pullback`.

## NEEDS

* `sp-design`: a ruling on item 2 above (the contraction target for the wall), and
  confirmation that they are happy for me to author the angle family in the `planeSub`
  vocabulary rather than in their `(t, w)` coordinates — the two agree, but the Lean
  continuity burden is much smaller in mine.
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
* Two of my own model tests were wrong before they were right, and both failures looked
  like real mathematics: (i) the sign of a local Jacobian is meaningless unless the tangent
  frames at source and target are oriented by the *ambient* orientation — the raw QR frames
  gave alternating signs and read as "the branches disagree"; (ii) a single sample point
  for "H₁ differs from the single composite" landed on an even-parity slab, where the
  central factor is `+1`, and read as "no discrepancy at all".  Sample every residue class
  the formula distinguishes, not one point.
