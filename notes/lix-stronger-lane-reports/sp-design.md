# `sp-design` — the mathematics of the stronger LIX theorem

Lane report for `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`.  I write no Lean; every claim
below is tagged **VERIFIED (read)** (I read the Lean statement named), **VERIFIED (model)**
(a numeric model test, command and output recorded), or **PROPOSED** (mathematics I assert
and have not yet mechanised or model-tested).

Sections: 1. where the zero is · 2. the k-fold map `ψ_k` · 3. Step D mod `p`, uniform ·
4. signs over `F_p` for the k-zero Step C · 5. summary and risks.

---

## 1. Where the zero is

### 1.1 The formula, for abstract block data `(a, b, c)`

The transported section is `CharClass/MappingTorusSection.lean`'s

```lean
def mtSection (V G : M → Matrix n n ℂ) (y t : Z → ℝ) (ξ η : Z × M → n → ℂ) (p : Z × M) :
    n ⊕ n → ℂ :=
  if 0 ≤ t p.1 then mappingTorus V G y t p *ᵥ Sum.elim (ξ p) 0
  else mappingTorus V G y t p *ᵥ Sum.elim 0 (η p)
```

with the two fields of `CharClass/LemmaTwoZero.lean`, `ξ = blockNorth a` and
`η = blockSouth a b c χ y`, i.e. on the northern half the constant `(a(m), 0)` and on the
southern half the manuscript's path (2.10)

```text
  τ  :=  southParam y z = (1 + y z)/2          (τ = 1/2 exactly at the south pole y = 0)
  blockSouth (z, m)  =  ( (1−τ)·a(m) + τ·b(m) ,  χ(τ)·c(m) )   ∈  ℂ^ι ⊕ ℂ^κ.
```

**The zero locus.**  `CharClass/LemmaTwoZero.lean: mtSection_manuscript_eq_zero_iff` —
under the hypotheses `a m ≠ 0`, `∑_i ‖a m i‖² = 1`, `∑_i ‖b m i‖² = 1`, `χ(1/2) = 1`
(and `IsMTSectionData`, `IsCircleChart y t`):

```text
  mtSection … (z, m) = 0   ⟺   t z = −1  ∧  y z = 0  ∧  b(m) = −a(m)  ∧  c(m) = 0 .
```

VERIFIED (read).  In words: **the zero sits over the south pole of the circle, at the base
points where `b` is the antipode of `a` and the transverse section vanishes.**  The
antipodality is forced, not assumed: `LIXSectionPath.unitVectors_seam_eq_zero_iff` says a
straight segment between two *unit* vectors passes through `0` iff they are antipodal and
`τ = 1/2`.  This is exactly the note's §1.2 requirement "confirm from `LemmaTwoZero.lean`
that the zero of the transported section for abstract block data is where `b = −a`":
**confirmed**, and with `τ = 1/2 ⟺ y = 0 ⟺` south pole as the circle half of it.

Note the shape of the dependence.  `mtSection` multiplies by `mappingTorus V G y t p`, but
the *zero locus* does not see `G` at all: `mtSection_eq_zero_iff_of_north_ne_zero` reduces
it to the vanishing of `blockNorth`/`blockSouth`, which involve only `a, b, c, χ, y`.  Only
the seam condition `G *ᵥ (a,0) = (b,0)` (`IsMTSectionData`) uses `G`.  This is why moving
`a` costs nothing in Step A and why the k-zero variant will not need `G` to be symmetric
(see §4.3).

### 1.2 The concrete instance at `n = 2`, and the local model

`CharClass/LIXSectionManuscript.lean` fills in `M = S⁵ × Y`, `Y = ∏_j ℂP^{d_j}`,
`V = 𝟏³ ⊕ H`:

| field | definition | file |
|---|---|---|
| `a` | `aVec m = eThree = Pi.single 2 1` (constant) | `LIXSectionManuscript.lean` |
| `b` | `bVec m = (m.1 : Fin 3 → ℂ)`, the tautological point of `S⁵` | `LIXSectionManuscript.lean` |
| `c` | `cVec m = ` the `(i+1)`-st **column** of the `j`-th `ℂP^{d_j}` projection | `LIXSectionManuscript.lean` |

and gets `manuscriptSection_eq_zero_iff_concrete`: the zero is
`(south pole, −e₃, (basePoint)_j)`, packaged by `LemmaTwoGlue.lixSection_eq_zero_iff` as
`p = (southPole, lixZeroPoint dd)` with `lixZeroPoint dd = (negEThree, baseYPoint dd)`, and
named `LemmaTwoStepC.lixZero dd = (southPole, lixZeroPoint dd)`.  VERIFIED (read).

**The local model.**  `CharClass/LIXSectionChart.lean` charts `S⁵` at `−e₃` by

```text
  sphereChartVec (w₀, w₁, c)  =  ( w₀ , w₁ , c·i − √(1 − (‖w₀‖² + ‖w₁‖² + c²)) )   ∈ ℂ³
```

(source the plain product `ℂ × ℂ × ℝ`, five real dimensions = the real tangent space
`{ξ : Re ξ₂ = 0}` of `S⁵` at `−e₃`), and the circle by its horizontal coordinate `u`, so
the trivial block of the section reads

```text
  trivialBlockChart (w, u)  =  (1 − τ(u))·e₃ + τ(u)·sphereChartVec w ,     τ(u) = (1+u)/2 .
```

`LIXSectionDeriv.lean` proves the strict derivative at the origin is

```text
  eulerLinearModel (dw₀, dw₁, dc, du)  =  ( dw₀/2 , dw₁/2 , (dc/2)·i − du )
```

— **VERIFIED (read)**, and `eulerLinearEquiv` proves it bijective by exhibiting the inverse
(no determinant, no orientation).  `LIXSectionLocalHomeo.eulerLocalHomeo` is the inverse
function theorem applied to it.  The transverse block's local model is the `ℂP` chart, and
`LIXHsqEta.lixEtaLin_eq_blockSouth` glues the two into the full local model over
`ChartSrc × ∏_j ℂ^{d_j}`.  Top degree `lixTopDegree dd = 2·(∑ d_j) + 6 = 2·lixRank dd`.

The coordinate-free form of the chart is already in the tree, at `LIXSectionDeriv.lean:79`:

```text
  sphereChartVec w  =  chartLinearCLM w  −  chartWeight w • eThree ,
```

i.e. *(an ℝ-linear isometric parametrisation of the real orthocomplement of `e₃`) minus
(the radial weight) times `e₃`*.  Only `chartLinearMap` — the literal
`![w₀, w₁, c·i]` — knows which coordinate `e₃` is.  This is the hinge for §1.3.

### 1.3 Moving the constant section to `e₁`: confirmed, with one correction

The note's §1.2 claim is **confirmed on the mathematics and confirmed on the Lean statements
that matter, with one caveat about the phrase "nothing else changes"** (the chart layer does
change, by a relabelling of `Fin 3`; see the file list below).

Why `e₃` cannot stay.  The clutching/suspension coordinate is `Re (x 2)`:
`Analysis/LIXLemmaSixGenerator.lean` defines
`equatorEmb a = (a₀ + i a₁, a₂ + i a₃, i a₄)` and proves `re_equatorEmb_two`, so
`S⁴ = {x ∈ S⁵ : Re (x 2) = 0}` and the two suspension points are `±e₃`.  VERIFIED (read).
Any map `Σψ` of `S⁵` that preserves the hemispheres fixes `±e₃` and is a cone there, so with
`a = e₃` the zero of the `k`-th power section would sit at the one point `−e₃` and would not
be a local homeomorphism.  With `a = e₁ = Pi.single 0 1` we have `Re (e₁ 2) = 0`, so `e₁` and
`−e₁` lie **on the equator**, and `(Σψ_k)^{-1}(−e₁)` is the `k`-point set of §2.

What is unchanged, verified by reading the statements:

* `LemmaTwoZero.mtSection_manuscript_eq_zero_iff` is stated for an abstract `a` and uses only
  `a m ≠ 0` and `∑ ‖a m i‖² = 1`.  `eOne = Pi.single 0 1` satisfies both by the same
  two-line proofs as `eThree_normSq` / `eThree_ne_zero`.  **VERIFIED (read).**
* `LIXSectionManuscript.bVec_eq_neg_aVec_iff` and `cVec_eq_zero_iff` use only that `aVec` is
  constant.  **VERIFIED (read).**
* Step A's interface `LemmaTwoStatement.HasStepAUnitary` is
  `∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0`; nothing in
  `LemmaTwoStepA.lean` / `LemmaTwoUnitary.lean` uses which unit vector `aVec` is except the
  one `simp [aVec, eThree]` at `LemmaTwoStepA.lean:142` inside `eProj_eq_rankOneProj`.
  **VERIFIED (read).**  The Corollary-4 producer builds frames taking `e₃ ↦ x`; to hit
  `G' *ᵥ (e₁,0) = (x,0)` post-compose on the right with the constant unitary `P` of `ℂ³`
  with `P e₁ = e₃` (extended by `1` on `H`): `G' = G·(P ⊕ 1)`.  `G'` is still continuous and
  still a corner unitary of `V`, and
  `G' EHmat^{e₁} G'ᴴ = G EHmat^{e₃} Gᴴ = FHmat`.  **PROPOSED** (elementary; one Lean lemma).
* `Analysis/LIXLemmaSixCompare.lean` touches `e₃` only through `eThree_normSq`.
  **VERIFIED (read).**
* Lemma 2 itself is *the same statement*: `EHmat^{e₁} = (P ⊕ 1) EHmat^{e₃} (P ⊕ 1)ᴴ` because
  `rankOneProj e₁ = P (rankOneProj e₃) Pᴴ`, and Murray–von Neumann equivalence of continuous
  fields is invariant under conjugating one side by a constant unitary.  So
  `¬ ContinuousMvNEquiv FHmat EHmat^{e₁}` and `¬ ContinuousMvNEquiv FHmat EHmat^{e₃}` are
  equivalent, and the C*-endpoint is untouched.  **PROPOSED** (elementary).

What *does* change — the files that hard-code `e₃` or the coordinate index `2`:

| file | what is hard-coded | fix |
|---|---|---|
| `CharClass/LIXSectionManuscript.lean` | `eThree`, `aVec`, `negEThree` | new `eOne`, `aVec := eOne`, `negEOne` |
| `CharClass/LemmaTwoStatement.lean` | `eProj = fromBlocks (rankOneProj eThree) 0 0 0`; `EHmat_eq_fromBlocks` | `rankOneProj eOne` |
| `CharClass/LemmaTwoStepA.lean:142` | `simp [aVec, eThree]` | `simp [aVec, eOne]` |
| `CharClass/LIXSectionChart.lean` | `sphereChartVec = ![w₀, w₁, c·i − √…]`; `sphereChartVec_zero`; `trivialBlockChart`; `eulerLinearModel/Equiv` | radial correction moves to coordinate `0`: `![c·i − √…, w₀, w₁]`, derivative `![(dc/2)i − du, dw₀/2, dw₁/2]` |
| `CharClass/LIXSectionDeriv.lean` | `chartLinearMap = ![w₀, w₁, c·i]`, and every `simp [eThree]` | `![c·i, w₀, w₁]`; the coordinate-free identity at line 79 survives verbatim |
| `CharClass/LIXSectionLocalHomeo.lean` | `trivialBlockChart_zero` proof | same proof, `eOne` |
| `CharClass/LIXSphereChartHomeo.lean` | `sphereLower = {Re z₂ < 0}`, `sphereChartVec_two_re/_im`, `sphereChartInv = (z₀, z₁, Im z₂)` | `{Re z₀ < 0}`, `(Im z₀, z₁, z₂)` |
| `CharClass/LIXSphereChart.lean` | the radial clamp (index-free) + the `![…]` literal | reindex the literal only |
| `CharClass/LIXHsqEta.lean:185,191` | `eThree` inside the `show` of the trivial block | follows `aVec` |
| `CharClass/LemmaTwoGlue.lean` | `lixZeroPoint = (negEThree, baseYPoint)` | `(negEOne, baseYPoint)` |
| `CharClass/LIXBaseInstances.lean` | docstring only | docstring |

**Recommendation to `sp-oddside` (PROPOSED).**  Do not do this as a `Fin 3` relabelling.
Do it once, generically: parametrise the chart layer by

* a unit vector `a : Fin (n+1) → ℂ` with `Re (a n) = 0` (so `−a` is on the equator), and
* an ℝ-linear isometry `L : ℝ^{2n+1} ≃ {ξ : Re ⟪ξ, a⟫ = 0}`,

and define `sphereChart_a w = L w − √(1 − ‖w‖²) • a`, so that
`trivialBlockChart (w,u) = (1−τ)a + τ·sphereChart_a w` has strict derivative
`(dw, du) ↦ (1/2)·L dw − du·a` at the origin — which is a linear isomorphism because `L` is
an isomorphism onto `a^⊥_ℝ` and `a ∉ a^⊥_ℝ`.  At `a = e₃` and `L = chartLinearMap` this is
*literally* the tree's `eulerLinearModel` (checked against `LIXSectionChart.lean` and
`LIXSectionDeriv.lean:79`), so the `n = 2` mod-2 instance stays green by instantiation, and
`a = e₁` costs one `L`.  The generic form also serves `sp-tower`'s general `n`, where the
`![…]` literal has no analogue at all.

---

## 2. The `k`-fold map `ψ_k`

### 2.1 The formula

Work on `S^{2n+1} = {x ∈ ℂ^{n+1} : ∑_i |x_i|² = 1}` with the clutching coordinate
`Re (x n)`, equator `S^{2n} = {Re (x n) = 0}`, constant section `a = e₁`.  Define

```text
  Ψ_k (x)  =  ( x₀^k / |x₀|^{k−1} ,  x₁ , … , x_n ) ,      Ψ_k(0, x₁,…,x_n) = (0, x₁,…,x_n)
  ρ (x)    =  ( ω x₀ , x₁ , … , x_n ) ,                    ω = e^{2πi/k}
  ρ_t (x)  =  ( e^{2πit/k} x₀ , x₁ , … , x_n ) ,           t ∈ [0,1],  ρ_0 = id, ρ_1 = ρ .
```

In polar form `x₀ = r e^{iθ}` this is simply `r e^{iθ} ↦ r e^{ikθ}`: **keep the modulus of
the first coordinate, multiply its argument by `k`, fix everything else.**  In Lean it is
one `Function.update`, and Lean's junk conventions make the `x₀ = 0` branch automatic:
`0^k / ‖0‖^{k−1} = 0/0 = 0` for `k ≥ 2` and `x₀/1 = x₀` for `k = 1`, so `Ψ_1 = id` on the
nose.  `ψ_k := Ψ_k` restricted to the equator.

**The suspension is free.**  `Ψ_k` preserves `|x₀|`, `x₁, …, x_n` and hence both
`∑|x_i|²` and `Re (x n)`.  So `Ψ_k` *is* `Σψ_k`: no suspension construction, no hemisphere
case split, no `EuclideanSpace`.  This is the main reason to prefer it over a pinch map.
VERIFIED (model): claims A, B below.

### 2.2 The four requirements

| # | requirement | status |
|---|---|---|
| (i) | `ψ_k` continuous | **PROPOSED**, one line: continuous away from `x₀ = 0`, and `‖x₀^k/|x₀|^{k−1}‖ = ‖x₀‖ → 0`, so continuous at `x₀ = 0` too. |
| (ii) | `ψ_k ∘ ρ = ψ_k`, `ρ` of order `k` | **PROPOSED** (`(ωx₀)^k = ω^k x₀^k = x₀^k`), **VERIFIED (model)** for `n ≤ 4`, `k ≤ 7`, 400 random points each: 0 violations. |
| (iii) | `ψ_k^{-1}(−e₁)` = one free `ρ`-orbit, `ψ_k` a local homeomorphism at each | **PROPOSED** in closed form, **VERIFIED (model)**: see §2.3. |
| (iv) | `u ∘ ψ_k ≃ u^k` | **PROPOSED** with a complete elementary route: §2.4. |

### 2.3 The zeros: closed form and local model

```text
  ψ_k^{-1}(−e₁)  =  { ζ e₁ : ζ^k = −1 }  =  { q_j := e^{iπ(2j+1)/k} e₁ : j = 0,…,k−1 } ,
  q_j = ρ^j q₀ ,   q₀ = e^{iπ/k} e₁ .
```

All `k` points lie on the equator (their `x_n` coordinate is `0`), all are distinct, none
lies on the "wall" `W₀ = {x : x₀ ∈ ℝ_{≥0}}` (that would need `(2j+1)/k ∈ 2ℤ`, odd = even),
and at `k = 1` the set is `{−e₁}`, the existing single zero.  VERIFIED (model): closed-form
residual `≤ 3.2e−15`, free `ρ`-orbit `True`, on-equator `True`, off-wall `True`, and a
random search over the equator refined by descent produced **0 strays** (`n ∈ {2,3}`,
`k ≤ 6`).

**The local model, in canonical bases.**  At `q_j` the real tangent space of `S^{2n}` is
`ℝ·(i q_j) ⊕ V`, where `V = {(0, x₁,…,x_{n−1}, i s)}` is the "rest" space, and the same
recipe at the target `−e₁` gives `ℝ·(−i e₁) ⊕ V`.  In these bases

```text
  d(ψ_k)_{q_j}  =  diag(k, 1, 1, …, 1)      for every j.
```

VERIFIED (model), `n ∈ {2,3,4}`, `k ≤ 7`: `max|J − diag(k,1,…,1)| ≤ 1.9e−10`, `det J = k`
exactly for all `j`.  So every local degree is `+1`, `deg ψ_k = +k`, **and no local degree
is ever computed by a determinant** — the matrix is literally the same at every `q_j`.

The invariant form, which is what `sp-oddside` should state and what makes §1.3.4 work, is
the *identity of maps* (note §1.3.2(iii), with the composition order corrected):

```text
  near ρ^j q₀ :   ψ_k  =  ( ψ_k near q₀ ) ∘ ρ^{−j}        (PRE-composition)
```

which is an immediate consequence of `ψ_k ∘ ρ = ψ_k`.  **The note's §1.3.2 writes
`ψ_k = ρ^{−i} ∘ (ψ_k near q₀)`, i.e. post-composition; that is wrong and the correction
matters**, because it is precomposition by a homeomorphism of the *base* that lets
naturality of `j` plus absolute homotopy invariance do the work in §4.  VERIFIED (model):
`Ψ_k(x) = Ψ_k(ρ^{−j} x)` for `x` in a `0.01`-neighbourhood of `ρ^j q₀`, `n ∈ {2,3}`,
`k ≤ 6`, 200 samples each: 0 violations.

**The section's derivative at the `k` zeros is one matrix.**  With `a = e₁`,
`b = Ψ_k ∘ x`, `S(u,x) = (1−τ)e₁ + τ Ψ_k(x)`, `τ = (1+u)/2`, read in the canonical source
basis at `q_j` transported by `ρ^j`: the `(2n+2) × (2n+1)` derivative is the **same matrix
for every `j`**, of full rank `2n+1`, smallest singular value `0.5`.  VERIFIED (model),
`n ∈ {2,3}`, `k ≤ 6`: spread over the `k` zeros `≤ 2.3e−10`, rank `= 2n+1` at every zero.
This is the linear-algebra shadow of §4's "every local contribution is literally equal".

### 2.4 Requirement (iv): `u^k ≃ u ∘ ψ_k`, elementarily

The obstruction the note flags is real: `deg ψ_k = k` plus `[S^m, S^m] ≅ ℤ` (Hopf) would
give (iv) at once, but Hopf's theorem is exactly the kind of literature input the program
forbids.  Here is a route with no degree theory in it at all.  All **PROPOSED**; the
bookkeeping step (c) is **VERIFIED (model)**.

Write `W₀ = {x ∈ S^{2n} : x₀ ∈ ℝ_{≥0}}` (the "wall"), and
`Θ(e^{iθ}, w) = (√(1−‖w‖²) e^{iθ}, w)` for `w` in the closed unit ball `D^{2n−1}` of the
rest space, so that `ψ_k(Θ(e^{iθ}, w)) = Θ(e^{ikθ}, w)`.

**(a) Normalise `u` on the wall, for free.**  `π(x) := (|x₀|, x₁,…,x_n)` is a *continuous*
retraction `S^{2n} → W₀` (no `arg`, no case split).  Put `ũ := (u ∘ π)^{-1} · u`; then
`ũ ≡ 1` on `W₀`.  And `u ≃ ũ`: `u ∘ π` factors through the convex `W₀`, so the straight-line
contraction of `W₀` gives `u ∘ π ≃` a constant `c ∈ U(n)`, and `U(n)` is path-connected so
`c ≃ 1`.  Hence `u = (u∘π)·ũ ≃ ũ`.  No homotopy extension property, no cofibration.

**(b) Powers and compositions respect homotopy, trivially.**  If `H` is a homotopy `u ≃ ũ`
then `H^k` (pointwise `k`-th power) is a homotopy `u^k ≃ ũ^k`, and `H ∘ (ψ_k × id)` is a
homotopy `u ∘ ψ_k ≃ ũ ∘ ψ_k`.  So it suffices to prove (iv) for `ũ`.

**(c) The explicit Eckmann–Hilton homotopy.**  With `ũ ≡ 1` on `W₀`, set
`γ_w(t) := ũ(Θ(e^{2πit}, w))` for `t ∈ [0,1]`; then `γ_w(0) = γ_w(1) = 1` for every `w`, and
`γ_w ≡ 1` for `‖w‖ = 1`.  Define, for `s ∈ [0,1]`,

```text
  H_s (t, w)  =  ∏_{j=1}^{k}  γ_w ( clamp₀¹ ( ((1−s) + s k)·t − s·(j−1) ) )      (ordered)
```

Then `H_0(t,w) = γ_w(t)^k = ũ(x)^k`, `H_1(t,w) = γ_w({k t}) = ũ(ψ_k(x))`, and for every `s`
the value at `t ∈ {0,1}` is `1`.  VERIFIED (model), `k ≤ 5`, 30 random based loops in
`U(3)`, 25 sample times each: the concatenation identity, both endpoints of the
interpolation, and basedness all hold to `1e−8`; **0 violations**.

**(d) Continuity across the wall.**  `H_s` is written in the coordinates `(t, w)`, i.e. via
`arg x₀`, which is discontinuous exactly on `W₀`.  But as `t → 0⁺` and as `t → 1⁻` every
factor tends to `γ_w(0) = γ_w(1) = 1`, so `H_s` extends by the value `1` across `W₀` and is
continuous on `S^{2n} × [0,1]`.  This is the one gluing argument in the route: continuity on
the closed complement of the wall's interior, plus the constant value `1` on the wall.

Chain: `u^k ≃ ũ^k = H_0 ≃ H_1 = ũ ∘ ψ_k ≃ u ∘ ψ_k`.

**Note for `sp-powers`.**  `notes/lix-stronger-lane-reports/sp-powers.md` did not exist when
this was written, so there is nothing yet to converge with.  I propose `Ψ_k` above as *the*
`ψ_k` and will reconcile on the lead's ping.  The two properties I would not trade away are
(1) `Σψ_k` is the same formula as `ψ_k` (no suspension construction) and (2) `ρ` is a
*linear* unitary `diag(ω,1,…,1)` with the explicit isotopy `diag(e^{2πit/k},1,…,1)` to the
identity — §4 needs that isotopy, and a pinch map's combinatorial `ρ` would not give it.

**Correction to the note.**  §1.3.2 asks for `ρ` "a rotation by `2π/k` in a plane not
containing `e₁`".  That is the wrong side: with `ψ_k` invariant under `ρ`, the preimages of
the *target* `−e₁` are a free `ρ`-orbit only if `−e₁` is **not** in the fixed set of `ρ`, so
the rotation plane must be the one **containing** `e₁` — here the `x₀`-plane.  The fixed set
of `ρ` is `{x₀ = 0}`, and `±e₁` are as far from it as possible.

---
