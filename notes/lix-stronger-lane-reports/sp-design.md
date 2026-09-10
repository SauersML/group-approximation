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

**(a) Normalise `u` on the wall, for free — and with no `U(n)`-connectedness.**
`π(x) := (|x₀|, x₁,…,x_n)` is a *continuous* retraction `S^{2n} → W₀` (no `arg`, no case
split), and it is norm-preserving and positively homogeneous, so it is an
`Powers.IsRadialMap` in `sp-powers`' sense and extends to the closed ball.  Put
`A := u ∘ π` and `ũ := Aᴴ·u`; then `ũ ≡ 1` on `W₀` because `π` is idempotent, `A` is a
**ball unitary** (continuous and unitary on the closed unit ball) for free, and
`u = A·ũ`.  `sp-powers`' left gauge lemma consumes a ball-unitary factor directly, so
`clutch(u ∘ ψ_k) ≅ clutch(ũ ∘ ψ_k)` (because `A ∘ Ψ_k` is again a ball unitary,
`isDiscUnitary_comp_radial`).  For the powers, **no homotopy is built at all**: the gauge
factor `C := u^m·(ũ^m)ᴴ` is a product of ball unitaries, hence a ball unitary, and
`u^m = C·ũ^m` on the ball, so the left gauge lemma applies in one step
(`clutchEquiv_normGen_pow` in `Analysis/LIXPowersNormalise.lean`).  *(Corrected on
`sp-powers`' instruction: an earlier draft of this paragraph cited their
`θ ↦ (A_θ ũ)^k ũ^{−k}` homotopy.  That argument is correct but it is the right argument only
for a gauge lemma stated for a DISC unitary; theirs asks only for a ball unitary, they have
withdrawn the homotopy, and the "easy to get wrong because `A` is not central" caveat goes
with it.)*  **Path-connectedness of `U(n)` is not needed anywhere and is struck from the
obligation list** (lead's ruling).  No homotopy extension property, no cofibration, no
contraction of `A` to a constant.

**The wall is the NEGATIVE real axis, not the positive one.**  `sp-powers`' clamp saturates
where Mathlib's `Complex.arg` cuts, on the non-positive reals, so their retraction is
`π(x) = (−|x₀|, x₁,…,x_n)` and their target carries the sign `joinCneg k = (−1)^k·joinC k`.
The two conventions differ by `z ↦ −z` in the `x₀`-plane.  Everything above holds verbatim
with `W₀ = {x : x₀ ∈ ℝ_{≤0}}`; **use their convention**, because a `ũ` normalised on the
wrong disc will not make the pinch identification fire.

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

**(d) Continuity across the wall** — *withdrawn as a separate obligation, see §2.5.*  `H_s` is written in the coordinates `(t, w)`, i.e. via
`arg x₀`, which is discontinuous exactly on `W₀`.  But as `t → 0⁺` and as `t → 1⁻` every
factor tends to `γ_w(0) = γ_w(1) = 1`, so `H_s` extends by the value `1` across `W₀` and is
continuous on `S^{2n} × [0,1]`.  This is the one gluing argument in the route: continuity on
the closed complement of the wall's interior, plus the constant value `1` on the wall.

Chain: `u^k ≃ ũ^k = H_0 ≃ H_1 = ũ ∘ ψ_k ≃ u ∘ ψ_k`.

### 2.5 Convergence with `sp-powers`: agreed, this is the `ψ_k`

`sp-powers` arrived independently at the **same** map (their "join power"), with the same
reason for preferring it: `Σψ_k` is the same formula as `ψ_k`, so the clutching coordinate
is fixed for free and there is no suspension bookkeeping.  **Agreed formula, both lanes:**

```text
  Ψ_k (x₀, x₁, …, x_n) = ( x₀^k / |x₀|^{k−1} , x₁, …, x_n ) ,      Ψ_k(0, …) = (0, …)
  ρ = diag(ω, 1, …, 1) ,  ω = e^{2πi/k} ,   ρ_t = diag(e^{2πit/k}, 1, …, 1)
```

with `a = e₁`, target `−e₁`, zeros `q_j = e^{iπ(2j+1)/k} e₁`.  Two points settled:

* **The `ρ`-plane contains `e₁`.**  `sp-powers` had written "not orthogonal to `e₁`"; the
  sharp statement is that the rotation plane **is** the `x₀`-plane, i.e. it contains `e₁`.
  Both lanes now use that.  (The program note's "a plane not containing `e₁`" is wrong; see
  the correction at the end of §2.4.)
* **Composition order**: `ψ_k = (ψ_k near q₀) ∘ ρ^{−j}` near `ρ^j q₀`, i.e. precomposition.
  Derived independently by both lanes.

`sp-powers`' Lean interface, already green on their probe, consumes exactly the data I
specify: `Powers.IsRadialMap Ψ` (continuous, `‖Ψ y‖ = ‖y‖`, `Ψ(r•y) = r•Ψ y` for `r ≥ 0`)
plus a reparametrisation family.  `Ψ_k` satisfies `IsRadialMap` — norm preservation is
`|x₀^k/|x₀|^{k−1}| = |x₀|` and positive homogeneity is immediate — so items 1–3 of the
note's §1.3 are discharged generically in `Ψ`.

**Their refinement to my (c)/(d), adopted.**  Write the reparametrisation as a self-map of
the equatorial space, `A_{j,θ}(z,v) = (|z| e^{i c_{j,θ}(arg z)}, v)`, rather than as a
formula in `(t,w)`.  Then the wall continuity is a property of *one* map instead of of a
product of `k` matrix-valued factors, and my step (d) disappears: both ends of the clamp
give the same *point of the sphere*, not merely the same matrix value.  I withdraw step (d)
as a separate obligation.  `sp-powers` measured the jump across the cut at `2.9e−8` and the
identification `∏_j u(A_{j,1} y) = u(Ψ_k y)` at `2.9e−15` once `u ≡ 1` on the wall, against
a failure of `2.0` for the raw generator — which is the same "normalise first" conclusion as
my (a).

**Two properties neither lane will trade away**: (1) `Σψ_k` is the same formula as `ψ_k`;
(2) `ρ` is a *linear* unitary with the explicit isotopy `ρ_t` to the identity — §4's Half A
needs that isotopy, and a pinch map's combinatorial `ρ` would not give it.

**Correction to the note.**  §1.3.2 asks for `ρ` "a rotation by `2π/k` in a plane not
containing `e₁`".  That is the wrong side: with `ψ_k` invariant under `ρ`, the preimages of
the *target* `−e₁` are a free `ρ`-orbit only if `−e₁` is **not** in the fixed set of `ρ`, so
the rotation plane must be the one **containing** `e₁` — here the `x₀`-plane.  The fixed set
of `ρ` is `{x₀ = 0}`, and `±e₁` are as far from it as possible.

---

## 3. Step D mod `p`, uniform in the stage

### 3.1 What the certificates say

I extended `tools/lix_modp_fast.py` to label every constraint row by
`(j, i, μ)` — the index `j` of the Wu relation `P(γ_j(W)) = E_j(γ(W))`, the reduced-power
component `P^i` of it (the weight-`j + i(p−1)` piece; `i` is determined by `j` and the
weight of `μ`), and the monomial `h^μ` of `H^*(Y)` the `z`-part is read on — and to run a
*triangular propagation*: repeatedly find a row whose support, after deleting the unknowns
already forced to zero, is a single unknown.  Tool:
`notes/lix-stronger-lane-reports/tools/lix_modp_certificates.py` (node copy
`scratch/lix_modp_certificates.py`).

The certificates are uniform and they name one family of relations.  Writing
`𝔟_k` for the weight-`k` part of the unknown `b` and `m = ∑ d_j`:

| case | elimination order printed by the tool |
|---|---|
| `n=2 p=2 d=[2]` | `j=2,P¹ → 𝔟₀`; `j=3,P² → 𝔟₂` |
| `n=2 p=2 d=[2,4]` | `j=2,P¹ → 𝔟₀`; `j=3,P² → 𝔟₂`; `j=4,P³ → 𝔟₄`; `j=5,P⁴ → 𝔟₆` |
| `n=3 p=3 d=[3]` | `j=2,P¹ → 𝔟₀`; `j=3,P² → 𝔟₃` |
| `n=5 p=5 d=[5]` | `j=2,P¹ → 𝔟₀`; `j=3,P² → 𝔟₅` |
| `n=6 p=2 d=[6]` | `j=4,P³ → 𝔟₀`; `j=5,P⁴ → 𝔟₂`; `j=6,P⁵ → 𝔟₄`; `j=7,P⁶ → 𝔟₆` |
| `n=6 p=3 d=[6]` | `j=3,P² → 𝔟₀`; `j=4,P³ → 𝔟₃`; `j=5,P⁴ → 𝔟₆` |

In every case the relation that kills `𝔟_k` is `(j, i) = (i+1, i)` with `k = ip − n`.
**The whole system is used through its diagonal `j = i+1` only** — which is exactly the
sub-family the `F₂` tree already isolates (`CharClass/WuDiagonal.lean`'s `wu_diagonal`).
VERIFIED (model).  In the two negative controls the same tool shows why they fail:
at `n=2, p=3` (so `p ∤ n`) the diagonal family kills `𝔟_k` only for `k ≡ 1 mod 3`, and the
target functional is supported in `k ≡ 0 mod 3`; at `n=6, p=7` (so `p ∤ d` as well) `γ(V)`
is not Frobenius-supported at all and the target spans every residue.

### 3.2 The uniform theorem

State it in the shape the `F₂` tree already uses, `CharClass/ParityEven.lean`'s
`ParityData`.  Let `H = H^*(Y; F_p)`, `z = t·x` of weight `n+1` with `z² = 0`, and

```text
  γ_k(W) = ι(a_k) + z·ι(b_k) ,     a_k of weight k ,   b_k of weight k − (n+1) .
```

> **Theorem (Step D mod `p`, uniform).**  Suppose
> * **(A)** `a_0 = 1` and `a_q = 0` whenever `p ∤ q`;
> * **(I)** `P^i(b_k) = 0` whenever `i > k − (n+1)` (instability);
> * **(W)** for every `i ≥ 0`, `P^i(γ_{i+1}) = Q_i(γ)` where `Q_i` is the universal
>   weight-`(ip+1)` polynomial, and `Q_i = u_i·γ_{ip+1} + (a sum of products of at least two
>   `γ`'s)` with `u_i` a **unit**.  (`u_i = 1` when `P(h) = h + h^p`; `u_i = κ^i` under
>   `sp-steenrod`'s normalisation `P(h) = h + κh^p`, see §3.4a.  State the hypothesis with
>   the unit, not with `1`: it costs one multiplication in the inductive step and buys
>   independence from their normalisation constant.)
>
> Then `b_N = 0` for every `N ≡ 1 (mod p)`.  Consequently, if `a_q = 0` for `q > m` and
> `r ≡ 1 (mod p)`, then `γ_r(W) = 0`.

*Proof.*  Take the `z`-component of (W) at index `i`, and put `N = ip + 1`.

*Left side.*  `b_{i+1}` has weight `i+1−(n+1) = i − n < i`, so (I) kills `P^i(b_{i+1})`;
`P(z) = z` and Cartan give `P^i(z·ι(b_{i+1})) = z·ι(P^i b_{i+1}) = 0`.  So the `z`-part of
the left side is `0`.

*Right side.*  In a monomial `γ_{α_1}⋯γ_{α_s}` of `Q_i` the `z`-part replaces exactly one
factor by its `b` and the others by their `a`.  (Read `u_i` in place of the leading `1`
throughout; since `u_i` is a unit the induction is unchanged.)  By (A) the term survives only if
`α_{t'} ≡ 0 (mod p)` for every `t' ≠ t`, hence `α_t ≡ N ≡ 1 (mod p)`; and if `s ≥ 2` then
the other indices are `≥ p`, so `α_t ≤ N − p`.  The single `s = 1` monomial is `γ_N` with
coefficient `1`.  So the relation reads

```text
   0  =  u_i·b_N  +  (an H-combination of b_α with α ≡ 1 mod p and α ≤ N − p).
```

Induction on `i`: at `i = 0` there is no second term (`N − p = 1 − p < 0`), so `b_1 = 0`;
in general every `b_α` appearing is `b_{i'p+1}` with `i' < i`, zero by hypothesis.  Hence
`b_N = 0` for every `N = ip+1`, i.e. every `N ≡ 1 (mod p)`.

*Conclusion.*  `γ_r(W) = ι(a_r) + z·ι(b_r) = 0 + 0`. ∎

**Uniformity.**  Nothing above mentions `Y`, the number of factors, `m`, or the stage.  The
two arithmetic inputs are supplied once, for every stage of the tower `d_j = n·2^j`
(`j < s`, so `m = n(2^s − 1)`), by the single hypothesis `p ∣ n`:

* `p ∣ d_j = n·2^j` for every `j`, which is (A) via Frobenius (§3.3, L1/L3a);
* `r − 1 = n + m = n·2^s ≡ 0 (mod p)`.

So the proof is stage-independent by construction, which is what the note demands.  The
`n = 2, p = 2` instance is the existing `F₂` proof verbatim: "`N ≡ 1 mod 2`" is "`N` odd"
(`ParityEven.b_odd_eq_zero`) and "`r ≡ 1 mod 2`" is "`m` even"
(`ParityEven.gamma_top_eq_zero`).

### 3.3 The lemma list, and where each is checked

Over an abstract graded-commutative `F_p`-algebra `A` generated in weight `1` by
`h_1,…,h_l`, with `R = A[z]/(z²)`, `deg z = 2(n+1)`, a total `P = ∑_i P^i` that is a ring
homomorphism with `P^0 = id`, `P^i` of weight `i(p−1)`, `P(h_i) = h_i + h_i^p`, `P(z) = z`,
and instability `P^i(x) = 0` for `weight(x) < i`:

| # | statement | status |
|---|---|---|
| **L0** | *Wu for a split bundle.*  If `γ = ∏_s(1+y_s)` with `P(y_s) = y_s + y_s^p` then `P(γ_a) = E_a(γ)` for every `a`, `E_a` the universal polynomial with `E_a(e(y)) = e_a(y+y^p)`. | VERIFIED (model), all `a ≤ r`, every case in the table below |
| **L1** | *Frobenius.*  `p ∣ d_i` ∀`i` ⟹ `γ(V) = ∏_i (1 + h_i^p)^{d_i/p}`. | VERIFIED (model) |
| **L2** | `P(γ(V)) = ∏_i (1 + h_i^p + h_i^{p²})^{d_i/p}`. | VERIFIED (model) |
| **L3a** | `γ_a(V) = 0` unless `p ∣ a`.  (This is hypothesis (A).) | VERIFIED (model) |
| **L3b** | `P^i(γ_a(V)) = 0` unless `p ∣ i`.  *Proof:* `γ_a(V)` lies in the subalgebra generated by the `h^p`, `P` preserves that subalgebra by L2, so `P(γ_a(V))` is supported in weights `≡ 0 mod p`; the weights `a + i(p−1)` are distinct for distinct `i`, so each `P^i(γ_a(V))` is a single weight component. | VERIFIED (model) |
| **L4a** | *The linear part of the universal Wu polynomial.*  Modulo products of two or more `e`'s, `E_b(e) ≡ ∑_i (−1)^{i(p−1)} C(b−1,i)·e_{b+i(p−1)}`.  In particular the `e_{ip+1}`-coefficient of `E_{i+1}` is `C(i,i) = 1`, which is (W). | VERIFIED (model) against the exact `E` computed by Newton's identities, for every `b ≤ r`, all cases below.  **Proof, over ℤ:** `φ : f(y) ↦ f(y+y^p)` is a ring endomorphism of the symmetric functions, so it descends to the indecomposables `Q(Λ)`; there `p_M = (−1)^{M−1}M·e_M` and `φ(p_b) = ∑_i C(b,i)·p_{b+i(p−1)}` by the binomial theorem, whence the `e_{b+i(p−1)}`-coefficient of `φ(e_b)` is `(−1)^{i(p−1)}·C(b,i)·(b+i(p−1))/b = (−1)^{i(p−1)}·[C(b−1,i) + p·C(b−1,i−1)]`, which is `(−1)^{i(p−1)}C(b−1,i)` mod `p`. |
| **L4** | *The `z`-part of the Wu relation.*  With `γ(W) = γ(V)(1+zb)` and `z² = 0`, the relation at index `j` is equivalent to `P(B_{j−n−1}) = ∑_{a+b'=j, b'≥1} ∑_{i'} (−1)^{i'(p−1)} C(b'−1,i')·P(γ_a(V))·𝔟_{b'−n−1+i'(p−1)}`, `B = γ(V)b`.  Uses `E_j(e·e') = ∑_{a+b=j}E_a(e)E_b(e')` and L0. | VERIFIED (model): my rows and `lix_modp_fast.py`'s rows span the same `F_p`-space in every case below |
| **L5** | *The diagonal relation.*  At `j = i+1` the left side vanishes by instability and the weight-`(ip−n)` component is `𝔟_{ip−n} + (terms in `𝔟_{k'}`, `k' < ip−n`, `k' ≡ ip−n mod p`)`, leading coefficient `1`. | VERIFIED (model): leading coefficient exactly `−1` in the tool's `lhs − rhs` normalisation, i.e. `+1` in the relation, and the support condition holds, in every case below |
| **L6** | *Induction.*  `p ∣ n` ⟹ `ip − n ≡ 0 mod p`, and as `i` runs from `n/p` to `(m+n)/p`, `ip − n` runs over `0, p, …, m`; so `𝔟_k = 0` for every `k ≡ 0 mod p`, `0 ≤ k ≤ m`. | VERIFIED (model): the propagation is exactly triangular at every step |
| **L7** | *Assembly.*  `γ_r(W) = z·B_m = z·∑_{p∣a} γ_a(V)·𝔟_{m−a}`, and `p ∣ m`, so every index `m−a ≡ 0 mod p`; by L6 all vanish. | VERIFIED (model): the target functional's support is inside the killed set |

Tools: `tools/lix_modp_uniform_check.py` (L0–L7, symbolic over `F_p`),
`tools/lix_modp_certificates.py` (the elimination order),
`tools/paritydata_p.py` (L4a/L5/L6/L7 in the `ParityData` shape of §3.2, run against the
exact universal `E_{i+1}`).

Cases checked, **ALL LEMMAS OK in every one**, no exceptions:
`(2,2,[2]), (2,2,[4]), (2,2,[2,4]), (3,3,[3]), (3,3,[6]), (3,3,[3,6]), (4,2,[4]),
(4,2,[8]), (4,2,[4,8]), (5,5,[5]), (6,2,[6]), (6,2,[12]), (6,3,[6]), (6,3,[12]),
(7,7,[7]), (9,3,[9]), (10,2,[10]), (10,5,[10]), (11,11,[11]), (12,2,[12]), (12,3,[12]),
(15,5,[15]), (4,2,[2,4,8]), (6,2,[6,12])` — twenty-four cases, including a three-stage
tower and one with `135` unknowns, with no exception.  The remaining deeper towers were
still running after two and a half hours and I stopped them: the theorem is proved and
the marginal case adds nothing.

And the **`ParityData`-shaped statement of §3.2 itself** — hypotheses (A), (I), (W) checked
against the exact universal `E_{i+1}` computed by Newton's identities, the `z`-part shown to
have the claimed shape, and the conclusion `r ≡ 1 mod p` verified — passes in every case:

```text
cases with a failure: 0 of 17
```

with the killed indices coming out exactly as the theorem says, `N ≡ 1 (mod p)`, and `r`
always among them.  Examples: `n=3 p=3 d=[3,6]`, `r = 13`, killed `[1,4,7,10,13]`;
`n=5 p=5 d=[5,10]`, `r = 21`, killed `[1,6,11,16,21]`; `n=11 p=11 d=[11]`, `r = 23`, killed
`[1,12,23]`; `n=6 p=2 d=[6,12]`, `r = 25`, killed `[1,3,5,…]`.

### 3.4a The unknown normalisation constant does not reach Step D (task (a) for the lead)

`sp-steenrod`'s Route 1 delivers the operations only up to a universal constant, i.e. with
`P(h) = h + κ h^p` on degree-2 classes for an unknown unit `κ = c_2^{-1} ∈ F_p^×`.  **The
Step D forcing is unaffected, and I can say so from the lemma list rather than from the
sweep.**  §3.3 uses exactly four facts about `P`: the total `P` is a ring homomorphism,
`P(h) = h + κ h^p` on the degree-2 generators, `P(z) = z`, and instability.  It never uses
the `p`-th power property `P^{q/2} = (·)^p`, and it never uses the value of any constant.
Tracking `κ` through:

| lemma | with `P(h) = h + κh^p` |
|---|---|
| L1 | untouched (no `P`) |
| L2 | `P(γ(V)) = ∏_i (1 + h_i^p + κ h_i^{p²})^{d_i/p}`, using `κ^p = κ` |
| L3a, L3b | unchanged: the support is still `≡ 0 mod p` |
| L4a | the coefficient becomes `κ^i·(−1)^{i(p−1)}C(b−1,i)`; at `(b,i) = (i+1,i)` it is `κ^i` |
| L5 | triangular with leading coefficient `κ^i`, a **unit**, instead of `1` |
| L6, L7 | unchanged |

So `c_2 ≠ 0` is the whole requirement and its value is irrelevant.  The structural reason,
which is the lead's and which I have checked: `P'^i := κ^{-i}P^i` is again a ring
homomorphism in total (`κ^{-(a+b)} = κ^{-a}κ^{-b}`) with `P'(h) = h + h^p`, `P'^0 = id` and
the same instability, so the `κ`-family's per-`j` Wu relations are the `κ = 1` relations
with the weight-`(j+i(p−1))` component scaled by `κ^i` — nonzero row scalings of a
homogeneous linear system, which do not move its solution space.  (Note `P'` no longer
satisfies the top-power property, which is why this is a statement about *Step D's* axiom
list and not a general renormalisation.)  PROPOSED by proof, and confirmed numerically in
`tools/lix_modp_kappa.py` — see the run recorded below.

### 3.4 What the `F₂` tree already proves, and what `sp-evenside` must generalise

| `F₂` declaration | what it is | general-`p` status |
|---|---|---|
| `CharClass/ChernRelation.lean` | Chern classes from a `PowerBasis` (Leray–Hirsch as pure algebra), `γ_k = e_k(roots)` in the split case, Whitney sum via an injective base change | **coefficient-generic already in spirit**; the file fixes the convention `∏(X + y_k)`, so `γ_k = e_k(y)` with the `y` the *negatives* of the usual Chern roots.  At odd `p` that is still fine: `P^1(y) = y^p` for a degree-2 class survives the sign because `(−1)^p = −1`.  Flag for `sp-coeff`: the docstring's "over `ZMod 2` signs are invisible" must be re-audited, not re-used. |
| `CharClass/WuDiagonal.lean`: `SqData`, `SqData.wu_diagonal` | the abstract structure (Cartan, `Sq⁰ = id`, `Sq¹y = 0`, `Sq²y = y²`, `Sq^{≥3}y = 0`) and **the diagonal Wu relation** `Sq^{2i} γ_{i+1} = ∑_{j≤i} γ_{i−j}γ_{i+1+j}` | this is hypothesis **(W)** at `p = 2`.  `SqData` becomes `PowerData` with `P^0 y = y`, `P^1 y = y^p`, `P^{≥2} y = 0`. |
| `CharClass/WuSymmetric.lean`: `esymm_halfAntidiagonal_eq` | the combinatorial identity `m_{(2^i,1)}(y) = ∑_{j≤i} e_{i−j}e_{i+1+j}` in characteristic two | **do not try to generalise this.**  I printed the exact weight-`(ip+1)` component of `E_{i+1}` for `p = 2,3,5,7`: at `p = 2` it is the two-factor sum above, at `p = 3,5,7` it has many terms of length up to `p` and no two-factor form (e.g. `p=3, i=1`: `e_2e_1² + e_2² + 2e_3e_1 + e_4`).  VERIFIED (model).  The general-`p` route needs only the *shape* `γ_{ip+1} + decomposables` (L4a), not a closed form. |
| `CharClass/ParityEvenSlice.lean`: `sliceClass_eq_mul_self`, `sliceClass_coeff_odd_eq_zero` | `∏(1+h_j)^{d_j}` is a square when every `d_j` is even, so its odd components vanish | this is **L1 + L3a** at `p = 2`; the general form is "a `p`-th power when `p ∣ d_j`", the same two-line Frobenius argument |
| `CharClass/ParityEven.lean`: `ParityData` | the abstract Künneth-plus-Steenrod structure: `γ_k = ι(a_k) + t x ι(b_k)`, `Sq^{>0}t = Sq^{>0}x = 0`, `a_odd`, `sq_b` (instability `2k < j+6`), `wu` | the structure of §3.2 verbatim, with `Odd q` → `p ∤ q`, `2k < j + 6` → `i > k − (n+1)`, and `wu` in the (W) shape |
| `CharClass/ParityEven.lean`: `sum_a_mul_b_eq_zero` | the `tx`-component of (Wu-diag): `∑_{q+k=2i+1} a_q b_k = 0` | the general-`p` analogue is the displayed relation of §3.2's proof; at `p = 2` the decomposable part of `Q_i` is the single sum `∑_{j≤i}γ_{i−j}γ_{i+1+j}` so the `z`-part is a plain convolution, which is why the `F₂` file can state it so cleanly |
| `CharClass/ParityEven.lean`: `b_odd_eq_zero`, `gamma_top_eq_zero`, `gamma_top_eq_zero_of_slice` | the induction and the conclusion | **L6, L7**, with `Odd N` → `N ≡ 1 mod p` and `Even m` → `p ∣ n + m` |
| `CharClass/LemmaTwoStepD.lean`, `ParityInstance.lean`, `SqDataInstance.lean` | the instances and the glue to Lemma 2 | re-instantiate at `p`; `sp-coeff` owns the coefficient parameter |

**The one genuinely new ingredient is L4a** — the linear part of the universal Wu
polynomial — and everything else is a re-indexing of an argument the tree already has.
The proof I give for L4a (ring endomorphism of symmetric functions, descend to
indecomposables, compute on power sums) is elementary and literature-free but uses Newton's
identities over `ℤ` and a division by `b`; that division is the only delicate step and it is
exact, `C(b,i)(b+i(p−1))/b = C(b−1,i) + p·C(b−1,i−1)`.

---

## 4. Signs over `F_p` for the `k`-zero Step C

### 4.1 Where the signs would enter, and what the note's claim really covers

The `k = 1` architecture is, reading down from `LIXStepCOddThom.lean`:

```text
  lix_topClass_ne_zero_of_thom → lix_topClass_ne_zero_of_local
    → ThomStepCOddLocal.topChernClass_ne_zero_odd_local → ThomStepCOdd.topChernClass_ne_zero_odd
    → ThomSectionDetect.topChernClass_ne_zero_of_chartInjective
    → ThomStepCSection.topChernClass_ne_zero_of_section
    → ThomStepCEuler.topChernClass_ne_zero_of_su_ne_zero_line
```

and its logic is: `PuncturedAcyclic N (2r) z` kills `H^{2r}(N ∖ {z})`, so
`i = 0` and `range j = ker i` makes **`j` surjective**; `absLine` says `H^{2r}(N)` is a line
and `exc ≪≫ chartIso` says `rel = H^{2r}(N, N∖{z})` is a line; hence **`j` is an
isomorphism**, and `su ≠ 0` gives `γ_r = j(su) ≠ 0`.  VERIFIED (read).

At `k` zeros this breaks in exactly one place: `rel_k = H^{2r}(N, N ∖ Z)` with
`Z = {z_0,…,z_{k−1}}` is `k`-dimensional, `j` is still surjective, but no longer injective.
So `su ≠ 0` is not enough; one has to evaluate `j(su)`.  Excision to `k` disjoint balls
splits `rel_k ≅ ⊕_i H^{2r}(N, N∖{z_i})` with `j = ∑_i j_i ∘ pr_i`, and each `j_i` is an
isomorphism of lines by the *same* `k = 1` argument applied at `z_i`.  So

```text
   γ_r(W_g)  =  ∑_{i<k} j_i(x_i) ,        x_i = the local class of the section at z_i,
```

and the whole question is whether the `k` summands are equal.  Over `F₂` this is invisible
(a nonzero element of an `F₂`-line is *the* element).  Over `F_p` the summands are units
times a generator and the sum could be anything.

**The note's §1.3.4 claim is correct for one of the two halves and silent about the other.**

* **Half A (the global orientation factors): correct as stated.**  `R^i := id × ρ^i × id`
  is a homeomorphism of `N` with `R^i(z_0) = z_i` and `R^i(N∖{z_0}) = N∖{z_i}`, so
  naturality of `relToAbs` gives `j_0 ∘ (R^i)^*_rel = (R^i)^*_abs ∘ j_i`, and
  `(R^i)^*_abs = id` on `H^{2r}(N)` because `R^i` is isotopic to the identity through
  `R_t = id × ρ_t × id`, `ρ_t = diag(e^{2πit/k},1,…,1)`.  **Only absolute homotopy
  invariance is used, and no local degree is computed.**  So
  `j_i(x_i) = j_0((R^i)^*_rel x_i)` and it remains to compare the `x_i` inside one line.
  VERIFIED (read: `relToAbs_naturality` is used already at
  `LIXStepCOddRelative.lixHnat`; absolute homotopy invariance is §4.3).
* **Half B (the local classes): not free, and the note does not mention it.**
  `(R^i)^*_rel(x_i) = x_0` would follow from `σ ∘ R^i ≃ σ` *through maps of pairs*
  `(N, N∖{z_0}) → (E, E∖0)`, and that homotopy does **not** exist: `σ ∘ R_t` vanishes on
  `R_t^{-1}(Z)`, which for intermediate `t` is not inside `N ∖ {z_0}`'s complement.  Worse,
  the mapping-torus bundle `E = W_g` is **not** `R`-invariant: the fields `a, b, c` are
  (`a` is constant, `b = Ψ_k ∘ x` is `ρ`-invariant by construction, `c` depends on `Y`
  only) and `Vmat` is, but `G` comes from Step A and is an arbitrary continuous unitary
  field, and `mtSection = mappingTorus V G y t *ᵥ (field)` sees it.

Half B is nevertheless true, and the reason is that the *local model is `G`-free*.  The
tree's local homeomorphism is built from `trivialBlockChart`, i.e. from the **field**
`blockSouth a b c χ y` and not from `mtSection` (VERIFIED (read):
`LIXSectionChart.trivialBlockChart`, `LIXSectionDeriv.hasStrictFDerivAt_trivialBlockChart`,
`LIXHsqEta.lixEtaLin_eq_blockSouth` mention `G` nowhere).  The field is exactly
`R`-invariant.  What is `G`-dependent is the identification of the bundle over the ball
with the trivial bundle (`lixTrivBall`, `lixLocalPairIsoClosed`), and two such
identifications over a contractible ball differ by a continuous map into `GL_r(ℂ)`, which
is path-connected, so they induce the same map on `H^{2r}(ℂ^r, ℂ^r∖0)`.  That is the extra
lemma Half B needs, and §4.4 shows the tree currently proves its `F₂` instance
(`relPullback_lixKHomeo_eq_id`) by an argument that does not survive to `F_p`.

**Model-tested support for Half B.** In canonical bases the derivative of the section at
the `k` zeros is *literally one matrix* after transporting the source basis by `ρ^i`
(§2.3: spread `≤ 2.3e−10` over the `k` zeros, `n ∈ {2,3}`, `k ≤ 6`).  So the local models
are equal, not merely conjugate, once the charts are chosen as `ρ^i`-translates.
VERIFIED (model).

### 4.2 The corrected claim, as a proposition

> **Proposition (`k`-zero Step C, `F_p`).**  Let `Z = {ρ^i q₀ × …}` be the `k` zeros,
> `R = id × ρ × id`, and suppose
> 1. `H^{2r}(N ∖ Z; F_p) = 0` and `H^{2r+1}(N; F_p) = 0`;
> 2. `H^{2r}(N; F_p)` is a line;
> 3. excision splits `H^{2r}(N, N∖Z) ≅ ⊕_i H^{2r}(N, N∖{z_i})`, compatibly with `j`;
> 4. each `H^{2r}(N, N∖{z_i})` is a line and `j_i` an isomorphism;
> 5. `(R^i)^*_abs = id` on `H^{2r}(N)` (absolute homotopy invariance along `R_t`);
> 6. `(R^i)^*_rel(x_i) = x_0` (Half B);
> 7. `x_0 ≠ 0` (the `k = 1` local statement, at the zero `−e₁`).
>
> Then `γ_r(W_g) = k · j_0(x_0)`, so `γ_r(W_g) ≠ 0` whenever `p ∤ k`.

Items 1–5 and 7 are `PROPOSED` but routine, 6 is the one with content, and every step is
an equality of classes — **no local degree, no determinant, no orientation is computed
anywhere**, which is the note's design goal and it is met.

### 4.3 Absolute homotopy invariance: it exists, and it is already coefficient-generic

This is the most useful thing I found for the Lean lanes.

* **`ThirdParty/.../AlgebraicTopology/SingularCohomologyHomotopyInvariance.lean`:**
  `singularCohomologyMap_eq_of_homotopy (R : Type) [CommRing R] (M : ModuleCat.{0} R) (n : ℕ)`
  and its `Homotopic` and `C(X,Y)` variants are proved **unconditionally for an arbitrary
  coefficient module over an arbitrary commutative ring**, via Mathlib's
  `TopCat.Homotopy.singularChainComplexFunctorObjMap` (a genuine chain homotopy, at the
  pin, in `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`).
  **VERIFIED (read).**  `sp-coeff` does not have to build absolute homotopy invariance at
  `F_p`; it has to *use* the generic statement instead of the `ZMod 2` wrapper.
* **`CharClass/CohomologyBridge.lean`:** `pull_eq_of_homotopic`, `pull_eq_of_homotopy`,
  `pullMap_eq_of_homotopic`, `pullEquivOfHomotopyEquiv` — the `ZMod 2` wrappers `CharClass`
  actually calls.  These are the ones to re-cut over `K`.  VERIFIED (read).

### 4.4 The trap that dominates the odd side: **relative** homotopy invariance is `F₂`-only

`CharClass/RelativeLineHomotopy.lean` says it itself, and its own module docstring is the
warning:

> "**What this does not give.**  It is not homotopy invariance.  If the source pair's
> relative group has rank two or more, two homotopic maps of pairs can still have different
> pullbacks as far as this file knows, and the mod-2 coefficients are load-bearing: over any
> other field two isomorphisms between two lines differ by a scalar, and the scalar
> survives."

VERIFIED (read).  Its `eq_of_injective_of_line` is literally a `decide` over `ZMod 2`.  And
it is **load-bearing for Step C already at `k = 1`**: `CharClass/LIXHsq.lean`'s
`relPullback_lixGL_eq_lixGR` — the proof of the `hsq` binder — is
`RelativeSupport.relPullback_eq_of_homotopy_of_line …` plus
`relPullback_lixKHomeo_eq_id` (the "a linear automorphism's relative pullback is the
identity" step), both `F₂`-only.  VERIFIED (read, `LIXHsq.lean:118–140`).

So the odd side over `F_p` needs a real relative homotopy invariance, and it needs it twice:
for `hsq` (already at `k = 1`) and for Half B of §4.1.

**The good news, and the concrete recommendation.**  `RelativeLineHomotopy.lean`'s premise
("the prism construction was never ported") is **stale**.  The prism is in the tree, at
arbitrary coefficients, via Mathlib (§4.3).  The missing step is only the *relative*
one: the chain homotopy `H.toSSet.chainComplexMap R` is natural in the space, so for a
homotopy `H : X × I → Y` carrying `A × I` into `B` it restricts to
`C_*(A) → C_{*+1}(B)` and descends to the relative complexes, giving
`relPullback f = relPullback g` for homotopic maps of pairs, over any `R`.
**PROPOSED**, and I recommend the lead put it on `sp-coeff`'s or a new lane's plate before
`sp-oddside` starts: it retires an `F₂`-only step that the existing mod-2 proof depends on,
and it is the prerequisite for §4.2 item 6.

### 4.5 The lemma list for `sp-oddside`

**Reused verbatim** (the statement is already parametric in the subspace / the point, so
only the argument changes):

| declaration | why it survives |
|---|---|
| `RelativeSupport.lixHexact` = `relLES_range_eq_ker X A n` | generic in the subset `A`; apply it at `A = Zᶜ` |
| `RelativeSupport.lixHnat` = `relToAbs_naturality` | generic; this is also the engine of Half A |
| `RelativeSupport.lixHsection` | `absPull_comp` + `absPull_id_eq`, generic |
| `RelativeSupport.lixS`, `lixPi`, `lixS_comp_lixPi` | the section and projection as maps of spaces; `lixS_comp_lixPi` is `rfl` |
| `LIXThomClassTerm.lixThomClassTerm`, `lixThomClassTerm_ne_zero` | the Thom class of the bundle; it does not know where the section vanishes |
| `LIXBundlePair.lixTotalPair`, `lixPuncturedInTotal`, `lixSectionTotal` | unchanged; only `lixSectionTotal_mapsTo` needs the new zero-locus lemma |
| `LIXSectionChart`, `LIXSectionDeriv`, `LIXSectionLocalHomeo` | the local model at **one** zero, once the constant section is a parameter (§1.3); at `z_0` it is character for character the `k = 1` file |
| `LIXHsqEta.lixEtaLin_eq_blockSouth` and the `LIXHsq*` reconstruction | `G`-free; it is the reason Half B is true |

**Needs a parameter** (same mathematics, new binder):

| declaration | new binder |
|---|---|
| `LemmaTwoStepC.lixZero`, `LemmaTwoGlue.lixZeroPoint`, `lixSection_eq_zero_iff` | the finite zero set `Z` and `b = Ψ_k ∘ x`; the zero-locus theorem `LemmaTwoZero.mtSection_manuscript_eq_zero_iff` itself is unchanged (§1.1) |
| `LIXStepCOddRelative.lixJ`, `lixI` | `{lixZero dd}ᶜ` ⟶ `Zᶜ` |
| `LIXLocalPair.lixTrivSet/lixTrivBall`, `LIXLocalPairClosed.lixLocalPairIsoClosed` | indexed by `i < k`, i.e. at each `z_i` |
| `LIXStepCOddLocal.lix_topClass_ne_zero_of_local`, `LIXStepCOddThom.lix_topClass_ne_zero_of_thom` | conclusion changes from "`su ≠ 0` ⟹ `γ ≠ 0`" to the sum of §4.2; the binder list is otherwise the same |
| the whole `CharClass` coefficient layer | `sp-coeff`'s `K` |

**New** (in dependency order; `sp-design` recommends this order):

1. **Relative homotopy invariance over `K`** (§4.4).  Blocking.  Retires
   `RelativeLineHomotopy`'s `F₂`-only cut and unblocks `hsq` and Half B.
2. **`GL_r(ℂ)` acts trivially on `H^{2r}(ℂ^r, ℂ^r∖0; K)`** — from 1 plus path-connectedness
   of `GL_r(ℂ)`.  Replaces `LIXHsq.relPullback_lixKHomeo_eq_id`.
3. **`k`-point punctured acyclicity**: `H^{2r}(N ∖ Z; K) = 0` for a finite `Z`.  Induction
   on `|Z|` with Mayer–Vietoris: with `A = N ∖ (Z∖{z_0})`, `B = N ∖ {z_0}`, `A ∪ B = N`,
   `A ∩ B = N ∖ Z`, the sequence `H^{2r}(A) ⊕ H^{2r}(B) → H^{2r}(A∩B) → H^{2r+1}(N)` has
   both ends zero.  The tree has Mayer–Vietoris (`CharClass/MayerVietoris*.lean`) and
   `PuncturedAcyclic` for one point (`ThomPuncturedRecursion.lean`).
4. **The excision splitting** `H^{2r}(N, N∖Z) ≅ ⊕_i H^{2r}(N, N∖{z_i})`, compatible with
   `relToAbs`.  From `CharClass/RelativeExcision.lean` applied to `k` disjoint balls.
5. **`j_i` is an isomorphism for every `i`** — the `k = 1` argument at `z_i`; needs
   `PuncturedAcyclic` at an arbitrary point of `N`, not only at `lixZero`.
6. **The transport lemma** `j_i(x_i) = j_0((R^i)^*_rel x_i)` — naturality (`relToAbs_naturality`)
   plus `(R^i)^*_abs = id` (§4.3).  This is Half A, and it is three lines.
7. **Half B**, `(R^i)^*_rel(x_i) = x_0` — from 1, 2 and the `R`-invariance of the fields.
8. **The count** `γ_r(W_g) = k · j_0(x_0)`, hence `≠ 0` when `p ∤ k`.

Items 6 and 8 are the only genuinely new *mathematics*, and both are formal.  Items 1 and 2
are infrastructure that the mod-2 proof is currently short-cutting; items 3–5 are standard.

---

## Review of `sp-steenrod`

Requested by the lead: §2, §3 (sign conventions, Koszul signs, the two places `p` odd is
used) and §6 (Cartan via the `2p`-fold target and the resolution coproduct) of
`notes/lix-stronger-lane-reports/sp-steenrod.md`.  **Verdict: the plan is mathematically
sound and I sign off on §2, §3 and §6, with one wrong proof to replace (R1) and one
reported obstruction that is not real (R12).**  Everything below is VERIFIED (read + hand
computation) unless marked otherwise.

**R1 — `grNorm_eq`'s proof does not determine the element.  Replace it.**  §2.1 proposes to
prove `∑_{j<p} T^j = s^{p−1}` by "multiply `∑ T^j` by `T − 1` and telescope".  That gives
`s·∑T^j = T^p − 1 = 0`, which says only that `∑T^j` lies in `Ann(s)`.  In
`Λ ≅ F_p[s]/(s^p)`, `s` is a zero divisor and `Ann(s) = (s^{p−1})` is one dimensional, so
the telescope leaves `∑T^j = c·s^{p−1}` with `c ∈ F_p` **undetermined** — including
`c = 0`.  This is the lane's own §4 hazard, an unknown unit, appearing in its first lemma.
Two correct proofs, the second cheaper:

* telescope in `F_p[X]`, which is a domain: `X·∑_{j<p}(1+X)^j = (1+X)^p − 1 = X^p`, cancel
  `X`, then map `X ↦ s`;
* expand directly.  `(T−1)^{p−1} = ∑_i C(p−1,i)(−1)^{p−1−i}T^i`, and `C(p−1,i) ≡ (−1)^i`
  mod `p` by induction on `i` from `C(p−1,i) + C(p−1,i−1) = C(p,i) ≡ 0` for `1 ≤ i ≤ p−1`
  and `C(p−1,0) = 1`.  With `p−1` even the two signs cancel and every coefficient is `1`.
  Three lines, no polynomial ring, and the induction is the standard `p ∣ C(p,i)` fact.

**R2 — §2.3, the sign in `d ∘ d = 0`.**  Correct.  With
`d(e_i ⊗ σ) = (d_W e_i)⊗σ + (−1)^i(e_i ⊗ ∂σ)` the two mixed terms carry `(−1)^i` and
`(−1)^{i−1}` and cancel; the claim that this replaces the mod-2 cancellation rather than
copying it is right.

**R3 — §2.1 `N e_i` is a boundary in every degree.**  Correct.  Odd `i`: `N e_i = d e_{i+1}`.
Even `i`: `N e_i = s^{p−2}·(s e_i) = d(s^{p−2} e_{i+1})` by `Λ`-linearity of `d`.  Needs
`p ≥ 2` only.

**R4 — §3.3 `tupT_pow_card`.**  Correct, and the proof is right for the right reason.  Over
`r` shifts each slot is moved to the front exactly once, contributing
`(−1)^{n_j(k − n_j)}`, so the total is `(−1)^{k² − ∑ n_j²}`, and `x² ≡ x (mod 2)` makes the
exponent `≡ k − ∑ n_j = 0`.  `r` free, no hypothesis, as claimed.

**R5 — §3.3 `tupD_tupD`.**  Correct.  For `j < j'` the term "face `j` first" carries
`(−1)^{pre_j + pre_{j'} − 1}` because `∂_j` has dropped slot `j'`'s prefix by one, while
"face `j'` first" carries `(−1)^{pre_j + pre_{j'}}`; the operators commute, so the pair
cancels.  Within one slot the prefix is unchanged and it is `∂² = 0`.

**R6 — §3.3 "`p` odd enters in exactly two places".**  Accurate for §2, §3 and §6, but it is
**one fact used three times**: `(−1)^{a(p−1)} = 1`.  Place 1 is `tupEval`'s `T`-invariance
(sign `(−1)^{q²(p−1)}`); place 2 is `p·⟨u^{⊗p}, y⟩ = 0`, which is `p = 0` rather than
parity; and §6.1's invariance of `u⊗v⊗u⊗v⊗⋯` under the block shift is place 1 again at
`r = 2p` with the block degree `a+b` (sign `(−1)^{(a+b)²(p−1)}`).  Recommend one named
lemma `neg_one_pow_mul_p_sub_one` and three citations, rather than three inline parity
arguments.

**R7 — §3.4(A), the telescoping contraction.**  Correct in outline and it is the right
choice over (B).  One warning: the prefix sign `(−1)^{pre_j}` must be computed on the
**input** degrees while the prefix slots' outputs have degree `0` after `ηε`.  That
mismatch, not the `Finset.filter`, is where the computation will fight; state
`dS + Sd = 1 − (ηε)^{⊗r}` with the sign convention fixed before writing any of it.

**R8 — §6.1, all four sign claims.**  Correct.  `slotwise Φ₀` is Koszul-free because `Φ₀`
has degree `0`; `A` intertwines `T` with the block shift by two (and the block's total
degree equals the slot's, so the shift sign is unchanged by `Φ₀`); `B` naked intertwines
`T` with the simultaneous shift inside each block; the riffle
`x_1…x_p y_1…y_p ↦ x_1y_1…x_py_p` conjugates one to the other with
`ε = ∑_j |y_j|·∑_{l>j}|x_l|`, which is exactly the cost of moving each `y_j` past
`x_{j+1},…,x_p`.

**R9 — §6.3, agreement in degree `0`.**  Correct: for a `0`-simplex `x`, `A` gives
`(x⊗x)^{⊗p}` and `B` gives `x^{⊗p}⊗x^{⊗p}` riffled, both `x^{⊗2p}`.

**R10 — §6.2, the abstract `ψ_W`.**  Correct, with one sentence to split.  The comparison
theorem needs the **source** `W` to be a complex of projectives (it is free over `Λ`) and
the **target** `W ⊗_{F_p} W` to be acyclic in positive degrees (Künneth over a field, since
`W` resolves `F_p`).  Freeness of `W ⊗ W` is *not* needed and should not be claimed as part
of the justification; if it is wanted for another reason, note it is a real lemma
(`Λ ⊗_{F_p} M` with the diagonal action is free, by untwisting), not a consequence of `W`
being free.

**R11 — the Route-3 descent: the reported discrepancy is an arithmetic slip, and the
descent closes.**  This is the finding that matters for the lane.

`sp-steenrod` writes: "`j = p−1` gives `λ_{p−2}(−1)^{p−2} = (p−1)(−1)^{p−1} = −1` with `p`
odd, where the alternating pattern wants `+1`".  But `(−1)^{p−2} = −1` for `p` odd, not
`(−1)^{p−1} = +1`.  With the correct sign,

```text
   λ_{p−2}·(−1)^{p−2} = (p−1)·(−1) = 1 − p ≡ +1   (mod p),
```

which is exactly what the alternating pattern wants.  **The telescope closes with
`λ_i = i+1` and no endpoint correction.**  Checked by hand at `p = 3`:
`1·D(ffg) + 2·D(gff) = (v_0+v_1) − 2(v_1+v_2) = v_0 − v_1 − 2v_2 ≡ v_0 − v_1 + v_2 (mod 3)`,
which is `∑_j(−1)^j v_j`.

**R12 — and the sign vector of `N` is alternating, in the variable the telescope uses.**
`sp-steenrod`'s computation `+, +, −, …` is correct as a function of the rotation index `k`:
`ε_0 = 1`, `ε_1 = 1` (the moved factor has degree `0`), and `ε_k = −ε_{k−1}` for `k ≥ 2`
(the moved factor has degree `1` and passes `p−2` factors of degree `1`, and `p−2` is odd).
So `ε_k = (−1)^{k−1}` for `k ≥ 1`.  But `T^k v_0 = ε_k v_{p−k}`, and re-indexing by the
**position `j = p−k` of the `f`** — which is the index the telescope runs over — gives
`ε_{p−j} = (−1)^{p−j−1} = (−1)^j` because `p−1` is even.  Hence

```text
   N v_0  =  ∑_{j=0}^{p−1} (−1)^j v_j ,
```

alternating on the nose.  The `+,+,−` pattern and the alternating pattern are the same
vector read in two orders; there is no endpoint irregularity and nothing here resembles the
composite-B hazard.  Numeric confirmation is in the run reported below.

**R13 — the growth risk is the real one, and it is the only open item.**  I agree with
`sp-steenrod` that a Lean proof generic in `p` needs a closed form for the coefficient
vector at every one of the `p−1` levels, not only the first, and that is what the descent
numerics below are for.

---

## Model tests for the lead (2026-09-10): the κ-sweep and the descent

### (a) The κ-sweep: the Step D verdict is independent of the normalisation constant

Tool `tools/lix_modp_kappa.py`, node copy `scratch/lix_modp_kappa.py`, log `scratch/kappa.log`.
`tools/lix_modp_fast.py` with **both** places `κ` enters changed together: the Steenrod ring
homomorphism `P(h^m) = (h + κh^p)^m` and the universal Wu polynomials
`E_j(e) = e_j(y + κy^p)`, whose linear part becomes `κ^i(−1)^{i(p−1)}C(b−1,i)`.  Every
`κ ∈ F_p^×` was run for each case.

```text
cases where the verdict depended on kappa: 0 of 28
```

All 28 cases of the program note's §1.4 table (including every negative control) give
**identical verdict, identical rank and identical free dimension for every `κ ≠ 0`**.
VERIFIED (model).  Sample rows, `κ = 1` shown, "identical for every κ" `True` throughout:

| case | verdict | rank | free |
|---|---|---|---|
| `n=2 p=2 d=[2,4,8]` | FORCED | 132 | 3 |
| `n=2 p=3 d=[3]` | NOT forced | 2 | 2 |
| `n=3 p=3 d=[3,6]` | FORCED | 25 | 3 |
| `n=6 p=3 d=[12]` | FORCED | 12 | 1 |
| `n=6 p=5 d=[12]` | NOT forced | 11 | 2 |
| `n=11 p=11 d=[11]` | FORCED | 11 | 1 |

Together with §3.4a's proof, **the value of the normalisation constant is irrelevant to Step
D and only `c_2 ≠ 0` matters.**  I treat it that way everywhere above.

### (b) The descent: `c_1 = ((p−1)/2)!`, and the `Δ²` route does not close

Tool `tools/steenrod_descent.py` (with `tools/ambig2.py` for the independence test), node
copies in `scratch/`.

**The observation that makes the descent cheap and canonical.**  Work in
`C^*(Δ^n, {0})`, the cochains vanishing on the vertex `0`.  It is exact in *every* degree,
and the cone on vertex `0` gives an explicit contraction

```text
   h(τ^*) = (τ ∖ {0})^*   if 0 ∈ τ and τ ≠ [0],   else 0,        δh + hδ = 1.
```

At `n = 1` this alphabet **is** the lead's `{f, g}`: `f = [1]^*`, `g = δf = [01]^*`.  Then
for the `p`-fold tensor power `H := h ⊗ 1 ⊗ ⋯ ⊗ 1` (slot `0` only) satisfies
`D H + H D = 1` on the nose — the two mixed Koszul terms cancel because `h` lowers degree by
one.  VERIFIED (model): 0 failures over all `3^p` words, `p = 3, 5`.

Consequently **every primitive in the descent is `Y = H(A)`, with no linear solve**, because
`A` is a `D`-cocycle at every level: `D A_{k+1} = op(op'(Y_{k−1})) = 0` since
`N(T−1) = (T−1)N = T^p − 1 = 0`.  That makes `p = 13` instant and the coefficient vectors
canonical.

**The numbers.**

| `p` | 3 | 5 | 7 | 11 | 13 |
|---|---|---|---|---|---|
| `c_1` | 1 | 2 | −1 | −1 | 5 |
| `((p−1)/2)!` mod `p` | 1 | 2 | 6 = −1 | 120 = −1 | 720 = 5 |

**`c_1 = ((p−1)/2)!` exactly, at every prime tested, with no sign.**  VERIFIED (model).
Its nonvanishing is then free: `((p−1)/2)!` is a product of integers `1,…,(p−1)/2`, all
units mod `p`.  (Wilson gives the sharper `((p−1)/2)!² ≡ (−1)^{(p+1)/2}`.)

**Well-definedness.**  The answer must not depend on the choice of primitive.  Tested
exhaustively over every single-word perturbation `Y ↦ Y + D(w)` at every level:

```text
c_1 on Delta^1, p = 3:  4 non-trivial perturbations, values {1}   -> WELL DEFINED
c_1 on Delta^1, p = 5: 26 non-trivial perturbations, values {2}   -> WELL DEFINED
```

**`sp-steenrod`'s two requested vectors.**

* The sign vector of `N` on the bidegree (one degree-`0` slot, `p−1` degree-`1` slots):
  `T^k v_0 = ε_k v_{p−k}` with `ε = (+1, +1, −1, +1, −1, …)`, i.e. `ε_k = (−1)^{k−1}` for
  `k ≥ 1` — their computation, confirmed.  Re-indexed by the position `j` of the `f`, the
  coefficient of `N v_0` on `v_j` is `(−1)^j` for **every** `j` and every `p` tested
  (`p = 3,5,7,11,13`).  There is no endpoint irregularity; see the Review, R12.
* The coefficient vectors at every level are in the tool's output.  Two things are worth
  recording.  The **last** level has a closed form: writing `ṽ_j` for the word with the
  single `g` in slot `j`, the final primitive is

  ```text
     Y_last = c_1 · ∑_{j=1}^{p−1} j · ṽ_j ,
  ```

  checked at `p = 7, 11, 13` (e.g. `p = 13`, `c_1 = 5`: the printed vector
  `5, −3, 2, −6, −1, 4, −4, 1, 6, −2, 3, −5` is `5j mod 13` for `j = 1..12`).  And the
  intermediate supports are far smaller than `C(p,k)` (`p = 13`: `1, 12, 11, 100, 81, 288,
  196, 336, 175, 140, 45, 12` against `C(13,k)` up to `1716`).

**On `sp-steenrod`'s growth risk.**  It is smaller than they feared, because with the
canonical `H` **there is no coefficient vector to find**: the descent is the explicit finite
composite `A_{k+1} = op_k(H(A_k))` of two one-line operators, and a Lean proof generic in `p`
needs three lemmas — `δh + hδ = 1` on `C^*(Δ^n,{0})`, `D H + H D = 1` on the `p`-fold tensor
power (one slot, one sign), and `N(T−1) = 0` — plus the single evaluation
`⟨A_final, AW⟩ ≠ 0`.  Only the last is a computation, and it is where the remaining work is.

**The `Δ²` route for `c_2` does NOT close, and here is exactly where.**  The descent runs,
every primitive exists, `D(Y) = A` holds at every level, and the answer is `0` — but the
answer is **not well defined**:

```text
c_2 on Delta^2, p = 3:  198 non-trivial perturbations, values {0,1,2}     -> NOT well defined
c_2 on Delta^2, p = 5: 2730 non-trivial perturbations, values {0,1,2,3,4} -> NOT well defined
```

The choice of primitive can produce **every** element of `F_p`, so the `Δ²` descent computes
nothing.  The reason is precisely the one `sp-steenrod` identified as a *check that passes*
at `q = 1`, failing at `q = 2`.  Changing the primitive changes `A_final` by a `D`-coboundary
`D(ξ)`, and the final pairing changes by

```text
   ⟨D(ξ), AW(σ)⟩ = ⟨ξ, ∂ AW(σ)⟩ = ⟨ξ, AW(∂σ)⟩ .
```

On `Δ¹`, `∂σ` is a sum of **points**, and every word at the relevant level carries a `δf`
factor, which is the *zero cochain* on a point — so the ambiguity dies, which is exactly
`sp-steenrod`'s point-term lemma.  On `Δ²`, `∂σ` is a sum of **edges**, the words at the
final level have total degree `2` spread over `p` slots and their letters are perfectly
nonzero on edges, so nothing kills the ambiguity.  With my canonical `H` the collapse is
visible in the log: at `p = 5` the element `A` becomes identically `0` at `W`-index `3`.

**Recommendation.**  Take `c_2` from multiplicativity rather than from `Δ²`.  The lead's own
ruling (b) already states `c_{q+q'} = c_q c_{q'}` on even degrees; applied to two degree-`1`
classes it gives `c_2 = c_1²`, and `c_1 = ((p−1)/2)!` is a unit, so `c_2 ≠ 0`.  That does
re-introduce the odd×odd Cartan comparison the lead wanted to avoid — but §6's comparison is
being built anyway, and its degree-`0` agreement (`A` and `B` both send `e_0 ⊗ x` to
`x^{⊗2p}`) is what normalises the Cartan coefficient to `1`, so no *further* unknown
constant appears.  I see no way to make a `Δ^q` descent with `q ≥ 2` well defined, because
the ambiguity is a boundary term on `∂Δ^q` and only `q = 1` has a boundary of points.

---

## 5. Summary, and the open risks

### The four deliverables in one paragraph each

**1. Where the zero is.**  For abstract block data the transported section vanishes exactly
where the circle is at its south pole, `b(m) = −a(m)`, and `c(m) = 0`
(`LemmaTwoZero.mtSection_manuscript_eq_zero_iff`, VERIFIED by reading it); the antipodality
is forced by `unitVectors_seam_eq_zero_iff`, not assumed.  At `n = 2` that is
`(southPole, −e₃, basePoint)` and the local model is `eulerLinearModel`,
`(dw₀,dw₁,dc,du) ↦ (dw₀/2, dw₁/2, (dc/2)i − du)`, an isomorphism proved by exhibiting the
inverse.  **The note's §1.2 is confirmed**: `−e₃` is a suspension point of the clutching
coordinate `Re(x 2)`, so a hemisphere-preserving `Σψ_k` is a cone there; with `a = e₁` the
zero moves to `−e₁`, which is on the equator.  "Nothing else changes" is right for Lemma 2,
for Step A and for the C*-endpoint (a constant unitary `P` with `Pe₁ = e₃`), but the chart
layer does change; I list the eleven files and recommend making the chart generic in `a`
rather than relabelling `Fin 3`, which the tree is already one definition away from.

**2. `ψ_k`.**  `Ψ_k(x) = (x₀^k/|x₀|^{k−1}, x₁, …, x_n)`, `ρ = diag(ω,1,…,1)`, agreed with
`sp-powers` who reached the same map independently.  `Σψ_k` is the same formula, so the
suspension is free.  `ψ_k^{-1}(−e₁)` is the `k` roots of `−1` in the `x₀`-line, one free
`ρ`-orbit, and `d(ψ_k)` is `diag(k,1,…,1)` in canonical bases at *every* one of them
(VERIFIED (model) to `1.9e−10`, `n ≤ 4`, `k ≤ 7`), so no local degree is ever computed.  The
section's derivative at the `k` zeros is one and the same matrix.  Requirement (iv) has a
complete elementary route with no Hopf degree theorem: normalise `u` on the wall by a ball
unitary (no `U(n)`-connectedness), then the explicit `k`-fold Eckmann–Hilton interpolation,
which `sp-powers` has already mechanised.

**3. Step D mod `p`, uniform.**  Certificates say the whole system is used through its
diagonal `j = i+1` only.  The uniform theorem, in the shape of the `F₂` tree's `ParityData`:
if `a_q = 0` for `p ∤ q`, instability holds for `b`, and the diagonal Wu relation has the
shape `γ_{ip+1} + decomposables`, then `b_N = 0` for every `N ≡ 1 (mod p)`, hence
`γ_r(W) = 0` when `r ≡ 1 (mod p)`.  `p ∣ n` supplies both hypotheses at every stage of the
tower at once (`p ∣ d_j = n2^j` and `r − 1 = n + m = n·2^s`), so the proof is
stage-independent by construction.  Eight lemmas, every one model-tested, `0` failures in 21
cases plus 17 in the `ParityData` shape.  The `F₂` tree already proves the `p = 2` instance
of all of it; the one new ingredient is the linear part of the universal Wu polynomial, for
which I give a proof (ring endomorphism of symmetric functions, descend to indecomposables,
compute on power sums).  The normalisation constant of the odd-primary operations does not
reach Step D: only `c_2 ≠ 0` matters, proved structurally and confirmed by a κ-sweep with
`0` of `28` cases depending on `κ`.

**4. Signs over `F_p` for the `k`-zero Step C.**  Half of the note's §1.3.4 claim is right as
stated — the global orientation factors agree by naturality of `relToAbs` plus absolute
homotopy invariance along `ρ_t`, with no local degree computed — and absolute homotopy
invariance is in the tree **already generic in the coefficient ring**.  The other half, that
the local classes correspond, is not free and the note does not mention it: the mapping-torus
bundle is not `ρ`-invariant because `G` comes from Step A.  It is nevertheless true, because
the local model is `G`-free, and it needs one extra lemma.  Both that lemma and the existing
`hsq` rest on **relative** homotopy invariance, which the tree currently has only in an
`F₂`-only form that its own docstring warns is mod-2-specific.

### The open risks, in the order I would worry about them

1. **Relative homotopy invariance over `F_p`.**  The single blocking item for the odd side.
   `CharClass/RelativeLineHomotopy.lean` is `F₂`-only by construction and `LIXHsq.lean`
   depends on it *already at `k = 1`*.  Its premise that "the prism construction was never
   ported" is stale — Mathlib's `TopCat.Homotopy.singularChainComplexFunctorObjMap` gives the
   chain homotopy at arbitrary coefficients and the tree already uses it for the absolute
   case.  What is missing is the relative descent of that chain homotopy.  Put it on a lane
   before `sp-oddside` starts.
2. **`c_2 ≠ 0` for `sp-steenrod`.**  `c_1 = ((p−1)/2)!` is settled numerically and is a unit
   for a trivial reason, but the `Δ²` descent for `c_2` is *not well defined* (it takes every
   value in `F_p`), so `c_2 = c_1²` has to come from the Cartan comparison after all.
3. **The linear part of the universal Wu polynomial (L4a).**  I have a proof but it goes
   through Newton's identities over `ℤ` and a division by `b`; it is the one genuinely new
   combinatorial statement `sp-evenside` owes, and there is **no** closed form for the
   diagonal Wu polynomial at odd `p` to fall back on (I printed it for `p = 3,5,7`; it is not
   a two-factor sum as it is at `p = 2`).
4. **The chart layer's `a`-genericity.**  Cheap if done once and generically; expensive and
   repeated if done as a `Fin 3` relabelling now and again for general `n` later.
5. **`k`-point punctured acyclicity and the excision splitting.**  Standard, but they are new
   files, and `PuncturedAcyclic` is currently stated at one distinguished point.

Nothing in the four deliverables turned up an obstruction to the stronger theorem itself.
The two places where the program note is wrong are small and both are recorded above: the
`ρ`-plane must contain `e₁` (§2.4), and the local models compose by **pre**-composition with
`ρ^{−j}` (§2.3).

---

## GREEN / AUTHORED, UNVERIFIED

Not applicable: this lane writes no Lean.  Everything it produces is either a statement
tagged VERIFIED (read) against a Lean declaration named in the text, a numeric result tagged
VERIFIED (model) with the tool and the output recorded, or explicitly PROPOSED.

Tools landed in `notes/lix-stronger-lane-reports/tools/` (node copies in
`scratch/`): `psi_k_modeltest.py`, `psi_k_orient.py` (§2), `lix_modp_certificates.py`,
`lix_modp_uniform_check.py`, `paritydata_p.py`, `diag_wu_shape.py`, `lix_modp_kappa.py`
(§3), `steenrod_descent.py`, `ambig2.py`, `diag2.py` (the descent).

## NEEDS

* **`sp-coeff` (or a new lane), blocking `sp-oddside`:** relative homotopy invariance over
  `K` — `relPullback f = relPullback g` for homotopic maps of pairs — by descending Mathlib's
  `TopCat.Homotopy.singularChainComplexFunctorObjMap` to the relative cochain complex.  See
  §4.4.  This retires `CharClass/RelativeLineHomotopy.lean`, which is `F₂`-only and which
  `CharClass/LIXHsq.lean` already depends on at `k = 1`.
* **`sp-coeff`:** re-cut `CharClass/CohomologyBridge.lean`'s `pull_eq_of_homotopic` and
  friends over `K`; the underlying `ThirdParty` statement is already generic in `(R, M)`.
* **Superseded by `sp-oddside`:** my §4.2 item 3 and §4.5 item 4 asked for a direct-sum
  splitting; read them instead in their `ρ_i` form (`x = ∑_i ρ_i(x_i)`, `ρ_i ≫ j = j_i` by
  naturality along the identity).  See "Review of `sp-oddside`".
* **`sp-oddside`:** confirm that `CharClass/ChernRelation.lean`'s `∏(X + y_k)` convention
  survives at odd `p` (I believe it does — `P^1(y) = y^p` is sign-stable for a degree-2 class
  because `(−1)^p = −1` — but the file's "over `ZMod 2` signs are invisible" docstring must be
  re-audited, not re-used).
* **L4a, the linear part of the universal Wu polynomial** — assigned to nobody as of
  2026-09-10; `sp-evenside` has offered to take it and I have no objection (it is pure
  symmetric-function algebra with no cohomology in it).  Proof in §3.3; only the diagonal
  case is needed, where the coefficient is `1 + p·i ≡ 1` times `κ^i`.  There is no closed
  form for the odd-`p` diagonal Wu polynomial to fall back on.
* **Anyone stating hypothesis (W):** its leading coefficient is a **unit**, not `1`
  (`κ^i` under `sp-steenrod`'s normalisation).  §3.2, corrected 2026-09-10.
* **The lead:** two corrections to `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` — §1.3.2's
  `ρ`-plane must *contain* `e₁`, and its local-model identity is pre-composition.

## TRAPS

* **A local degree's sign is meaningless in a QR-chosen frame.**  My first `ψ_k` model test
  reported alternating local degrees at the `k` zeros and read as "the branches disagree".
  The frames were the arbitrary output of a QR complement.  In canonical bases every
  determinant is exactly `k`.  `sp-powers` hit the same shape independently.
* **Telescoping inside a ring with zero divisors determines nothing.**  `sp-steenrod`'s
  `grNorm_eq` proof multiplies by `T − 1` inside `F_p[s]/(s^p)`, where `s` kills
  `s^{p−1}`; the conclusion is an unknown scalar multiple, including zero.  Telescope in a
  domain, or compute the coefficients.
* **`(−1)^{p−2} ≠ (−1)^{p−1}`.**  One character, and it produced a reported obstruction that
  sent a lane looking for an endpoint correction that does not exist.  Review, R11.
* **A "constant" computed by a descent is only defined modulo the boundary terms.**  The
  `Δ¹` descent for `c_1` is well defined because `∂Δ¹` is points and the cochains vanish
  there; the identical construction on `Δ²` takes *every* value in `F_p` depending on the
  choice of primitive.  Test the independence before believing any number a descent prints.
* **A module docstring's premise can be stale.**  `RelativeLineHomotopy.lean` says the prism
  operator "was never ported"; it is in the tree, at arbitrary coefficients, via Mathlib.

## `c_2 = c_1²` at lemma precision, and the resolution's coproduct

Follow-up (a) for the lead, and the answer to `sp-steenrod`'s challenge that the degree-`0`
agreement of the Cartan comparison pins only the bottom coefficient.  **They are right that
it pins only the bottom one, and wrong that the identity therefore carries an unknown
constant: the constant is `1`, and the other candidate terms vanish for a reason that needs
no instability input at all.**  Tool `tools/wcoproduct.py` (with `tools/wshow.py`,
`tools/wcheck.py`); node copies in `scratch/`.

### The coproduct, solved rather than remembered

`sp-steenrod`'s §6.2 says of the explicit `ψ_W`: "I will not write this from memory.  The
deliverable is: solve the chain-map recursion symbolically, confirm the closed form, and only
then state it."  Done.  `Λ = F_p[T]/(T^p−1)`, `W_i = Λ e_i`, `d e_{2k+1} = s e_{2k}`,
`d e_{2k+2} = N e_{2k+1}`.  `Λ` carries the explicit `F_p`-linear contraction of `W`

```text
   h_E(T^j) = 1 + T + ⋯ + T^{j−1}  (h_E(1) = 0)    on even degrees,
   h_O(T^j) = [ j = p−1 ]                           on odd degrees,
```

which satisfies `dh + hd = 1` in positive degrees and `= 1 − ηε` in degree `0` (VERIFIED
(model): `0` failures, `p = 3,5,7,11,13`, degrees `0..5`).  Then `H := h ⊗ 1` gives
`DH + HD = 1 − (ηε)⊗1` on `W ⊗ W`, so the recursion `ψ(e_n) = H(α_n·ψ(e_{n−1}))` plus one
explicit correction in the `a = 0` blocks solves the chain-map condition in `O(size)` at
every degree.  The chain-map identity is asserted at every step and holds.

**The closed form it produces**, `ψ(e_n) = ∑_{a+b=n} (block)`:

```text
   a even                :  e_a ⊗ e_b
   a odd,  b even        :  e_a ⊗ T e_b
   a odd,  b odd         :  ∑_{0 ≤ u < v < p}  T^u e_a ⊗ T^v e_b
```

VERIFIED (model) block by block for `p = 3, 5, 7` over all degrees `n ≤ 2(p−1)`: every
`(even,even)` block is `e_a ⊗ e_b` with coefficient `1`, every `(odd,odd)` block is exactly
`∑_{u<v} T^u ⊗ T^v`, and the `(odd,even)` and `(even,odd)` blocks are as displayed.  This is
the classical formula; it is now confirmed rather than recalled, and `sp-steenrod` may state
it.

### The three lemmas

Write `ψ(e_n) = ∑_{a+b=n} ∑_{i,j} c^{(n)}_{a,b;i,j} T^i e_a ⊗ T^j e_b` and let
`c̄^{(n)}_{a,b} := ∑_{i,j} c^{(n)}_{a,b;i,j}` be the **reduced** coefficient — the only thing
the Cartan evaluation sees, because the functional `u⊗v⊗u⊗v⊗⋯` is `T`-invariant.

> **C1 (the reduced coefficients).**  For the `ψ` above,
> `c̄^{(n)}_{a,b} = 1` whenever `a` is even, and whenever `a` is odd and `b` is even;
> `c̄^{(n)}_{a,b} = 0` whenever `a` and `b` are both odd.
>
> *Reason for the vanishing, and it is the whole point:* the `(odd,odd)` block is
> `∑_{0≤u<v<p}T^u e_a ⊗ T^v e_b`, whose reduced coefficient is the number of pairs `u < v`,
> namely `C(p,2) = p(p−1)/2 ≡ 0 (mod p)`.  It is the reduction to `F_p` that kills it; the
> integral count is not zero.

VERIFIED (model), `p = 3,5,7,11,13`: at `n = 2(p−1)` every `a`-odd reduced coefficient is `0`
and every `a`-even one is `1`.

> **C2 (exactly one term survives, with no instability input).**  Let `u, v` be cocycles of
> degree `1`.  In the Cartan identity at index `2(p−1)`,
> `D_{2(p−1)}(uv) = ∑_{a+b=2(p−1)} c̄_{a,b}·D_a(u)·D_b(v)`, every term except
> `(a,b) = (p−1,p−1)` vanishes:
> * `a + b` is even, so `a` and `b` have the same parity.  If `a` is odd then both are, and
>   `c̄_{a,b} = 0` by C1.  This is what kills the two terms one would otherwise have to
>   worry about, `(p, p−2)` and `(p−2, p)`, since `p` and `p−2` are both odd.
> * If `a` is even and `a ≠ p−1`, then either `a ≥ p+1`, and `D_a(u) ∈ C^{p−a}` with
>   `p − a < 0`, so the group is zero; or `a ≤ p−3`, and then `b = 2(p−1)−a ≥ p+1` and
>   `D_b(v) ∈ C^{p−b} = 0`.
> * `p−1` is even because `p` is odd, so `(p−1,p−1)` is not excluded.

VERIFIED (model): `c̄_{(p,p−2)} = c̄_{(p−2,p)} = 0` at `p = 11, 13` (and the same at 3, 5, 7).
Note what this buys: **the vanishing at the `a > q(p−1)` end of the range, which is the
instability statement `P^s = 0` for `s < 0`, is not needed.**  `sp-steenrod` was right to
worry about it; it does not arise.

> **C3 (the constant).**  Hence `c_2·(uv) = C·c_1²·(uv)` with
> `C = c̄^{(2(p−1))}_{p−1,p−1} = 1`, so `c_2 = c_1² = (((p−1)/2)!)²`, a unit.

VERIFIED (model): `C = 1` at `p = 3, 5, 7, 11, 13`.  By Wilson, `c_2 ≡ (−1)^{(p+1)/2}`.

### The two caveats, both `sp-steenrod`'s and both real

* **A pair of degree-`1` classes with `uv ≠ 0` is needed**, and at odd `p` a degree-`1` class
  squares to zero, so `u ≠ v`.  The torus `S¹ × S¹` with the two circle classes supplies it
  (`u v` generates `H²`), which routes through Künneth rather than through a single sphere.
  The tree has `CharClass/CohomologyKunnethSphere.lean`.  Name it now.
* **C1 is a property of the explicit `ψ`, not of an abstract one.**  If `sp-steenrod` takes
  `ψ` from the comparison theorem (their §6.2's cheap option), C1 is unavailable and the two
  competing terms come back, and then they *do* need instability at the `a > q(p−1)` end.
  With the explicit `ψ` above — now confirmed, with a `O(size)` construction and a chain-map
  identity that is checkable degree by degree — neither is needed.  I recommend the explicit
  `ψ`: it is one closed formula in three cases, and it retires an unknown constant instead of
  creating one.

Their own unconditional argument for even × even (top index, instability, the `p`-th power
property) stands and is a good independent check: it forces `c_{q+q'} = c_q c_{q'}` on even
degrees with no reference to the coproduct, so everything really does reduce to `c_2`, and
`c_2 = c_1²` closes it.

## Review of `sp-oddside`'s plan

Follow-up (b) for the lead.  **Verdict: the plan is right, its two structural findings are
genuine improvements on my §4.2/§4.5 and I adopt both, and there is one simplification they
have not taken and one caveat on their finding 1.**

**Adopted from them, replacing my §4.2 item 3.**  The direct-sum splitting
`H^{2r}(N, N∖Z) ≅ ⊕_i H^{2r}(N, N∖{z_i})` is more than the consumer needs.  For each `i`
the identity of `N` is a map of pairs `(N, N∖Z) → (N, N∖{z_i})` because `N∖Z ⊆ N∖{z_i}`, so
`relPullback` gives `ρ_i : H^{2r}(N, N∖{z_i}) ⟶ H^{2r}(N, N∖Z)`, and naturality of
`relToAbs` along the identity gives `ρ_i ≫ j = j_i`.  The obligation is then the single
equation `x = ∑_i ρ_i(x_i)` — no biproduct, no compatibility square, nothing to invert.
VERIFIED (read): the variance is right (`relPullback` is contravariant in the pair, and
enlarging the subspace is the direction that exists), and `j(∑_i ρ_i x_i) = ∑_i j_i(x_i)`
follows.  **My §4.2(3) and §4.5(4) should be read in their form.**

**Adopted: the line is needed at one zero only.**  `topClass_eq_of_naturality'` produces
`γ_r = j(σ^*u)` from `hnat` and `hsection` alone and never uses surjectivity of `j`
(VERIFIED (read), `ThomStepCEuler`/`ThomStepCOdd`).  So the punctured-acyclicity machinery is
consumed once, at the distinguished zero, to get `c ≠ 0`.

**The caveat on their finding 1.**  "The `k+1`-point punctured vanishing is not on the
critical path" is right about the `k+1`-point statement, but the **one**-point statement at
*every* `z_i` may still be, depending on how `LocalClassesAgree` is discharged:

* **Route 1 (`F₂` only):** run the one-zero argument at each `z_i`.  Needs
  `PuncturedAcyclic N (2r) z_i` at every `i`, and then over an `F₂`-line
  `j_i(x_i) ≠ 0 ⟹ j_i(x_i) = c`.
* **Route 2 (any `p`):** the `ρ`-transport of §4.1 — Half A (naturality plus absolute
  homotopy invariance along `ρ_t`) and Half B.  Needs no extra punctured acyclicity, but
  needs relative homotopy invariance at odd `p`.

They have `puncturedAcyclic_lixPoint` in `LIXKStepCWired`, so Route 1 is anticipated; the
point is that finding 1 should not be read as retiring it.

**The simplification they have not taken, and it removes the whole `ρ`-machinery from the
`F₂` deliverable.**  At `p = 2`, `LocalClassesAgree` needs neither Half A nor Half B in any
form: `H^{2r}(N; F₂)` is a line, so `j_i(x_i) = c` for every `i` as soon as
`j_i(x_i) ≠ 0`, which is Route 1.  **So the first deliverable needs no isotopy `ρ_t`, no
naturality square along `ρ^i`, and no homotopy invariance of any kind.**  Their §0.4 cites
"the `F₂` line trick of `RelativeLineHomotopy`" for Half B; that is the wrong citation and
also more than they need — the fact is "an `F₂`-line has a unique nonzero element"
(`ThomStepCEuler.eq_localGenerator_of_ne_zero`, or
`RelativeSupport.eq_of_injective_of_line`), and reaching for
`relPullback_eq_of_homotopy_of_line` would pull in machinery that does not generalise
anyway.  Keeping `LocalClassesAgree` an abstract hypothesis — which their §0.2 already
does — is exactly right, because the odd-`p` discharge is Route 2 and has a different
shape.

**One thing not to budget as free.**  `LocalSplit` (`x = ∑_i ρ_i(x_i)`) is simpler to
*state* than the direct sum, but its proof is still excision to `k+1` disjoint balls; the
saving is in the interface, not in the work.

**Rulings they asked for.**  (i) Do the local model at `−e₁` in the generic form — a unit
vector `a` with `Re (a n) = 0` plus an ℝ-linear isometry `L` onto `a^⊥_ℝ`, giving
`chart_a(w) = L w − √(1−‖w‖²)·a` with derivative `(dw,du) ↦ ½ L dw − du·a` — not as a
`Fin 3` relabelling.  `LIXSectionDeriv.lean:79` already factors through the coordinate-free
identity, so the cost is one definition, and `sp-tower` needs the same object at general `n`
where the `![…]` literal has no analogue.  (ii) Their `joinC` reading is right and the trap
is real: `joinPow` is `planeSub`-based and wants `InnerProductSpace ℝ E`, which
`unitVectors (Fin 3) ⊆ (Fin 3 → ℂ)` does not have; the scalar `joinC` is the shared part.
Note the index shift: their `Ψ_k` (degree `k+1`) is my `Ψ_{k+1}`, and their exponent-facing
statement is about `k+1`, so at `F₂` the arithmetic condition `((k+1 : ℕ) : K) ≠ 0` is "the
exponent is odd", matching the existing `n = 2` theorem.

## κ(1,1), and `c_2` computed directly (2026-09-10, second pass)

The lead held the `c_2 = c_1²` ruling on the ground that nothing computed so far touches the
Cartan comparison's coefficient at the top splitting — the reduced coproduct coefficient is
only one factor of it, the riffle shuffle's Koszul sign and the evaluation reordering are the
others.  **That is correct.**  Rather than assemble those signs, I built the equivariant
diagonal `Φ` itself on the models and read both constants off, which answers the same
question with strictly less bookkeeping and produces `c_1` a second time, by different
machinery, as a cross-check on the descent.  Tool `tools/phi_models.py`, node log
`scratch/phi.log`.

### The construction

`Φ : W ⊗ C_*(X) → C_*(X)^{⊗p}`, natural and equivariant with `Φ(e_0 ⊗ −)` the iterated
Alexander–Whitney diagonal, is determined on the models by

```text
   ∂ Φ(e_a ⊗ ι_n) = α_a·Φ(e_{a−1} ⊗ ι_n) + (−1)^a ∑_j (−1)^j (δ_j)_# Φ(e_a ⊗ ι_{n−1}) ,
```

`α_a = s = T−1` for `a` odd and `N` for `a` even.  `C_*(Δ^n)` has the cone contraction
`s(σ) = [0,σ]` (zero if `0 ∈ σ`) with `∂s + s∂ = 1 − ηε`, and the **full** tensor
contraction `S = ∑_l (ηε)^{⊗(l−1)} ⊗ s ⊗ 1^{⊗(p−l)}` satisfies `∂S + S∂ = 1 − (ηε)^{⊗p}`
with no Koszul signs (the `l`-th term is nonzero only when the prefix slots are vertices).
Since `(ηε)^{⊗p}` is supported in degree `0`, `Φ(e_a ⊗ ι_n) = S(rhs)` solves the recursion
exactly for `n + a ≥ 1`.  The chain-map identity is **asserted at every step** and holds.
*(Trap: the one-slot contraction `s ⊗ 1^{⊗(p−1)}` is not enough — it leaves the
`(ηε)⊗1` residual, which is what the first run failed on.)*

### Reading the constants off

> **Do not formalise this route** — the one-dimensionality of the top degree is simplicial
> and fails for singular chains.  The values transfer, the route does not.  See "The descent
> needs no cone operator".

`Φ(e_a ⊗ ι_n)` has degree `n + a`; at `a = n(p−1)` that is `np`, the **top** degree of
`C_*(Δ^n)^{⊗p}`, whose only basis element is `[0..n]^{⊗p}`.  So
`Φ(e_{n(p−1)} ⊗ ι_n) = λ_n·[0..n]^{⊗p}`, and for a degree-`n` cocycle `w` and an `n`-cycle
`c`, `⟨D_{n(p−1)}(w), c⟩ = ±λ_n·⟨w,c⟩^p`.  On the minimal torus (one vertex, edges `a,b,c`,
triangles `U, L`, fundamental cycle `U − L`, `w = u ∪ v` with `⟨w,U⟩ = 1`, `⟨w,L⟩ = 0`) this
gives `c_2 = ±λ_2`; `Δ¹` gives `c_1 = ±λ_1`.

**Why the cycle matters, and why the answer does not depend on the choice of `Φ`.**  Two
diagonals differ by an equivariant chain homotopy, `Φ' − Φ = DH + HD`.  Pairing with
`w^{⊗p}`, the first term dies because `w` is a cocycle.  The second is
`⟨w^{⊗p}, H(D(e_a ⊗ c))⟩` and `D(e_a ⊗ c) = (d_W e_a) ⊗ c ± e_a ⊗ ∂c`; the second summand
dies because `c` is a **cycle** (this is exactly what fails on `Δ^q`, `q ≥ 2`, and is why
the `Δ²` descent of the first pass was ill defined), and the first is
`⟨w^{⊗p}, α_a·H(e_{a−1} ⊗ c)⟩ = ⟨(α_a)^*w^{⊗p}, H(e_{a−1} ⊗ c)⟩ = 0` because `w^{⊗p}` is
`T`-invariant and both `s = T−1` and `N` annihilate an invariant functional (`N` gives
`p·(−) = 0`).  That is `sp-steenrod`'s §3.3(2), used here for well-definedness.

### The numbers

| `p` | `c_1 = λ_1` | `((p−1)/2)!` | `c_2 = λ_2` | `κ(1,1) = c_2/c_1²` | `(−1)^{(p−1)/2}` |
|---|---|---|---|---|---|
| 3 | 1 | 1 | **−1** | **−1** | −1 |
| 5 | 2 | 2 | **−1** | **+1** | +1 |
| 7 | −1 | −1 | **−1** | **−1** | −1 |
| 11 | −1 | −1 | **−1** | **−1** | −1 |
| 13 | 5 | 5 | *(running)* | | +1 |

VERIFIED (model).  Four things at once:

1. **`κ(1,1) ≠ 0` at every prime computed**, so the lead's ruling stands.  Its value is
   `(−1)^{(p−1)/2}`, a unit, which is all that was asked.
2. **`c_2 = −1` for every odd `p`**, computed directly.  So the Cartan bridge is not needed
   for `c_2 ≠ 0` at all — it is a cross-check rather than a prerequisite.
3. **`c_1` agrees with the `Δ¹` cochain descent at every prime** (`1, 2, −1, −1, 5`).  Two
   independent computations, chain-level `Φ` versus cochain-level descent, of the same
   number by different machinery.  That validates both.
4. The three numbers are arithmetically consistent: by Wilson `(((p−1)/2)!)² ≡ (−1)^{(p+1)/2}`,
   so `κ(1,1)·c_1² = (−1)^{(p−1)/2}·(−1)^{(p+1)/2} = (−1)^p = −1 = c_2` ✓.

**And it matches the sign I derived by hand** before running anything: on the surviving
terms of the evaluation every slot has degree `1`, so the riffle sign
`ε = ∑_j |y_j|·∑_{l>j}|x_l|` is `∑_{j=1}^{p}(p−j) = p(p−1)/2`, giving
`(−1)^{p(p−1)/2} = (−1)^{(p−1)/2}` for `p` odd, and the evaluation reordering sign is the
same on both sides of the comparison and cancels.  Derivation and computation agree at
`p = 3, 5, 7, 11`.

**What this changes.**  `c_2 = −1` is now a computed number rather than a consequence of a
bridge, so `sp-steenrod` may take the shortest route available to them: prove `c_2 ≠ 0`
however is cheapest, knowing the answer.  Their unconditional even × even argument then
gives every even constant, and the `c_2 = c_1²` bridge survives as an independent check —
`(−1)^{(p−1)/2}·(((p−1)/2)!)² = −1` is a Wilson identity, so if the two routes ever disagree
the fault is in the chain-map identity, exactly where they said they would look.

## κ_top(q, q') in closed form, and the even constants

Follow-up for the lead after `sp-steenrod` retracted their even-degree multiplicativity
lemma (it evaluated at the bottom corner, the counit case; the constants live at the top
corner).  Tools `tools/phi_higher.py`, `tools/wtop.py`; node logs `scratch/phi3.log`,
`scratch/phi5.log`.

### The formula

> **κ_top(q, q') = (−1)^{q q'·p(p−1)/2} = (−1)^{q q'·(p−1)/2}** for `p` odd.
> In particular **κ_top = 1 whenever `q` or `q'` is even**, so `c_{q+q'} = c_q·c_{q'}` on
> even degrees and `c_{2k} = c_2^k = (−1)^k`.

Three ingredients, and the last two are why only the first needs a computation:

1. **The reduced coproduct coefficient at the top corner is `1`.**  The corner is
   `(a,b) = (q(p−1), q'(p−1))`, and both are **even** because `p−1` is even — for any `q`,
   `q'` whatever.  So it falls in the `(even,even)` case of C1, where `c̄_{a,b} = 1`.
   VERIFIED (model), `tools/wtop.py`: `c̄_{q(p−1),q'(p−1)} = 1` at every
   `(p,q,q')` tested — `p = 3` for `(1,1),(2,2),(2,4),(4,4),(2,6)`, `p = 5` for the same,
   `p = 7` for `(1,1),(2,2),(2,4)` — i.e. up to `n = 36`, and the full pattern
   (`a` odd ⟹ `0`, `a` even ⟹ `1`) holds at every one.
2. **The riffle shuffle's Koszul sign.**  On the surviving terms of the evaluation every
   `x`-slot has degree `q` and every `y`-slot degree `q'` (otherwise `⟨u,x_l⟩` or
   `⟨v,y_j⟩` vanishes), so
   `ε = ∑_{j=1}^{p} |y_j|·∑_{l>j}|x_l| = q q'·∑_{j=1}^{p}(p−j) = q q'·p(p−1)/2`.
3. **The evaluation reordering cancels.**  Its sign depends only on the degree sequence of
   the `2p` slots, which is `(q,q',q,q',…)` on **both** sides of the comparison.

### The numbers

> **Do not formalise this route.**  The step "the top degree has one basis element" is a
> statement about the **simplicial** chain complex of `Δ^n`.  It is false for singular
> chains, where the top-degree group of a simplex is enormous.  The pairing **values** below
> transfer (they are pairings, and the operations are the same); the **route** does not.  The
> Lean chain uses the descent for `c_1` and `κ_top` for the rest, both model-free — see "The
> descent needs no cone operator" below.

`Φ(e_{n(p−1)} ⊗ ι_n)` sits in the top degree `np` of `C_*(Δ^n)^{⊗p}`, whose only basis
element is `[0..n]^{⊗p}`; write it `λ_n·[0..n]^{⊗p}`.  Then for a degree-`n` cocycle `w` and
**any** `n`-cycle `c = ∑ n_s s`,

```text
   ⟨D_{n(p−1)}(w), c⟩ = λ_n·(−1)^K·∑_s n_s⟨w,s⟩^p = λ_n·(−1)^K·⟨w,c⟩   (mod p, Fermat),
```

`K = n²·p(p−1)/2`, so `c_n = (−1)^K λ_n`.  **No torus has to be built**: products of circles
are needed only to certify that some closed `n`-manifold carries a degree-`n` class with
nonzero fundamental evaluation, not for the number.  (The `x^p = x` step is where a cycle
with values outside `{0,1}` is handled, and it is Fermat.)

| `p` | `c_1` | `c_2` | `c_4` | `c_6` | `κ_top(1,1)` | `κ_top(2,2)` | `κ_top(2,4)` |
|---|---|---|---|---|---|---|---|
| 3 | −1 | −1 | +1 | −1 | −1 ✓ | +1 ✓ | +1 ✓ |
| 5 | +2 | −1 | +1 | — | +1 ✓ | +1 ✓ | — |
| 7 | −1 | −1 | — | — | −1 ✓ | — | — |
| 11 | −1 | −1 | — | — | −1 ✓ | — | — |

VERIFIED (model); ✓ marks agreement with `(−1)^{q q'(p−1)/2}`, and every one of the five
available `(p,q,q')` combinations matches.  `c_{2k} = (−1)^k` holds at `p = 3` for
`k = 1,2,3` and at `p = 5` for `k = 1,2`.  `λ_1 = ((p−1)/2)!` throughout, so
`c_1 = (−1)^{(p−1)/2}((p−1)/2)!`; the `Δ¹` cochain descent computes `λ_1`, in its own
convention, and agrees at every prime.

### What this settles

* **Every even constant is a unit**, `c_{2k} = (−1)^k`, which is what the normalisation
  needs and is stronger than "nonzero".
* **`sp-steenrod`'s retracted lemma is recovered at the right corner**, and inside the
  Cartan deliverable rather than beside it: multiplicativity on even degrees is
  `κ_top = 1`, which is ingredient 2 with `q q'` even.
* The odd × odd case is not `1` but `(−1)^{(p−1)/2}`, which is exactly the discrepancy that
  made the `c_2 = c_1²` bridge look suspicious; it is a unit, so nothing is lost.

## Endpoint statements (for `sp-endpoint`)

Drafted at the lead's request so the lane starts from statements.  Nothing here is
model-tested; it is reading plus statement-writing.  The challenge side mirrors
`Palomar/LIXChallenge.lean` exactly: Mathlib-only vocabulary, `Type` (not universe
polymorphic), the spectral order supplied by `letI`, `U₀` as `pathComponent (1 : unitary _)`,
the stabilisation in `CStarMatrix (Fin 2) (Fin 2) A`, and `cornerDiag` from the shared block.
**The shared block is reused unchanged** — `cornerDiag` and `IsK1Injective` are already what
the stronger statements need, and a second copy of either would be a second term.

### (1) The general theorem, Mathlib-only

```lean
/-- **The stronger theorem.**  For every `n ≥ 2` there is a separable simple unital
C⋆-algebra carrying a unitary `v` whose stabilisation `diag (v, 1)` is connected to `1` in
`U(M₂(A))` — so its `K₁`-class dies at the first stabilisation — and whose powers stay
outside `U₀(A)` unless the exponent is divisible by every prime dividing `n`.

The `Fintype (Fin 2)` instance is pinned to `Fin.fintype 2` so that the statement elaborates
to the same term in every environment; `n` occurs only as a natural number, never as a
matrix index, so no instance on `Fin n` is involved. -/
theorem exists_simple_separable_powers_outside_U0 (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) →
           ∀ p : ℕ, p.Prime → p ∣ n → p ∣ k) := by
  sorry
```

Two deliberate choices.  The stabilisation clause is written **exactly** as in
`exists_separable_simple_stage_two_witness` (an existential over `w` in the path component
whose underlying matrix is `cornerDiag`), not as `diagOne v ∈ …`, because `diagOne` is
development vocabulary.  And `v ∉ pathComponent 1` is **not** a separate conjunct: it is the
`k = 1` case of the power clause, since `p ∣ n` holds for some prime (as `2 ≤ n`) and `p ∣ 1`
is false.  `sp-endpoint` should record that derivation rather than add the conjunct, so the
statement has no redundant clause.

### (2) The headline instance, `n = 6`

```lean
/-- **The `n = 6` instance.**  A separable simple unital C⋆-algebra with a unitary whose
class dies at the first stabilisation and whose powers leave `U₀` unless the exponent is
divisible by `6`: an element of `U(A)/U₀(A)` of order divisible by `6`, or infinite, that is
trivial in `K₁`. -/
theorem exists_simple_separable_order_six_witness :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) → 6 ∣ k) := by
  sorry
```

Proof shape: instantiate (1) at `n = 6`, then from `2 ∣ k` and `3 ∣ k` conclude `6 ∣ k` by
`Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3`.

### (3) Every squarefree order

```lean
/-- **Every squarefree order is realised.**  For squarefree `N ≥ 2` there is a separable
simple unital C⋆-algebra with a unitary trivial in `K₁` whose powers leave `U₀` unless `N`
divides the exponent. -/
theorem exists_simple_separable_squarefree_witness (N : ℕ) (hN : 2 ≤ N) (hsq : Squarefree N) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
      (letI : PartialOrder A := CStarAlgebra.spectralOrder A
       letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
       letI : Fintype (Fin 2) := Fin.fintype 2
       ∃ v : unitary A,
         (∃ w ∈ pathComponent (1 : unitary (CStarMatrix (Fin 2) (Fin 2) A)),
            (w : CStarMatrix (Fin 2) (Fin 2) A) = cornerDiag A 2 (v : A)) ∧
         ∀ k : ℕ, v ^ k ∈ pathComponent (1 : unitary A) → N ∣ k) := by
  sorry
```

Proof shape: instantiate (1) at `n = N`, so `p ∣ k` for every prime `p ∣ N`.  Then
`N ∣ k` by factorisations: dispose of `k = 0` first (`dvd_zero`), and otherwise
`Nat.factorization_le_iff_dvd` reduces it to `N.factorization ≤ k.factorization`, which holds
pointwise because `hsq` gives `N.factorization p ≤ 1` (`Nat.Squarefree.factorization_le_one`)
while `p ∣ k` gives `1 ≤ k.factorization p` (`Nat.Prime.factorization_pos_of_dvd`).  **State
that arithmetic step as its own lemma** — `squarefree_dvd_of_forall_prime_dvd` — because it
is pure `ℕ` and belongs nowhere near the C⋆-side.

### (4) The development-side theorem

Repo vocabulary, in the `LIXEndpointStatement` idiom, with the same two local instances
re-registered rather than redeclared (that file's own warning: a fresh pair is definitionally
equal but not the same term, and `rw` matches instances syntactically).

```lean
attribute [local instance] GroupApproximation.instSpectralPartialOrder
                           GroupApproximation.instSpectralStarOrderedRing

variable (A) in
/-- **The witness condition, generalised to powers.**  `A` carries a unitary whose
stabilisation is null-homotopic in `U(M₂(A))` and whose powers leave `U₀(A)` unless the
exponent is divisible by every prime dividing `n`.  At `n = 2` and with the power clause read
at `k = 1` this is `HasK1InjWitness A`. -/
def HasK1InjPowerWitness (n : ℕ) : Prop :=
  ∃ v : unitary A, diagOne v ∈ unitaryComponentOne (CStarMat 2 A) ∧
    ∀ k : ℕ, v ^ k ∈ unitaryComponentOne A → ∀ p : ℕ, p.Prime → p ∣ n → p ∣ k

/-- **The theorem the solution proves.**  The limit algebra at rank `n` carries the power
witness, given the topological input at every prime dividing `n` and every exponent that
prime does not divide. -/
theorem lixLimit_hasK1InjPowerWitness_of (n : ℕ) [NeZero n]
    (h : ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k → LIX.LemmaTwoHolds n p k) :
    HasK1InjPowerWitness (LIX.Gen.LIXLimit n) n := by
  sorry
```

`LemmaTwoHolds n p k` is the program note §1.6 generalisation: at every stage `j`,
`¬ ContinuousMvNEquiv (FHmat_k) EHmat` over `M = S^{2n+1} × ∏_{i<j} ℂP^{d_i}` with
`d_i = Gen.stageRank n i = 2 ^ i * n`, `FHmat_k` built from `b = x ∘ Ψ_k` and `a = e₁`.

### The chain each step consumes

Read downwards; every name is from a lane report or the tree.

| step | statement | consumes |
|---|---|---|
| the algebra | `Gen.LIXLimit n` is a separable, simple, nontrivial unital C⋆-algebra | `sp-tower`: `Gen.lixTower n`, `Gen.lixIota`, `Gen.instCStarAlgebraStageAlgebraPi n`, `Gen.lixLimit_separableSpace`, `Gen.lixLimit_isSimpleCStar n` (both `#audit_closed_axioms`), and `Nontrivial (Gen.LIXLimit n)` which carries `[NeZero n]`; then `isSimpleCStar_iff_isSimpleRing` for the challenge's `IsSimpleRing` |
| the generator | the seam unitary at rank `n`, with `diag (u,1) ≃ 1` | `sp-tower`: `Gen.ePole n = Pi.single (Fin.last n) 1`, `Gen.genU n x = seamGen (ePole n) x`, both hemisphere trivialisations, `seamPath (ePole n)`; then `Gen.genUnitary` and `hdiag_genUnitary` |
| powers ↦ composition | `u^{k+1}` and `u ∘ ψ_k` are homotopic through unitaries | `sp-powers`: `Powers.joinC`, `Powers.IsRadialMap`, `isRadialMap_joinPow`, `normGen` with `isBallUnitary_normGen` and `normGen_wall`, `pinchIdentification_angleRepar`, and **the primary export** `exists_homotopy_pow_comp_normGen` (no hypothesis on the generator beyond ball-unitarity) |
| into `CharClass` | the clutched projections at the `k`-th power | `sp-powers`: `Analysis/LIXPowersExport.lean` — `clutchEquiv_iff_continuousMvNEquiv` (`Iff.rfl`), `continuousMvNEquiv_pow_pullback_map` |
| Corollary 4, powers | the climbed generator's `k`-th power is outside `U₀` when `p ∤ k` | the generalisation `climb_genUnitary_pow_notMem n p k (hk : ¬ p ∣ k)` of `LIX.climb_genUnitary_notMem`, over `LemmaTwoHolds n p k`, through `false_of_path` and `hasGeneratorShape_climb` at rank `n` |
| Lemma 2 at `(n,p,k)` | `¬ ContinuousMvNEquiv FHmat_k EHmat` at every stage | Step A: `CharClass.HasStepAUnitary` via `LemmaTwoUnitary`, with the constant unitary `P`, `P e₁ = e₃`, of §1.3.  Step C: `sp-oddside`'s `lixK_topClass_ne_zero` / `lixK_topClass_ne_zero_odd` over `LocalSplit`, `LocalClassesAgree`, `KLocalNonzero`.  Step D: `sp-evenside`'s `ParityPData.gamma_top_eq_zero_of_slice` at `p ∣ n` |
| the endpoint | `¬ K1Inj` and the three challenge theorems | `not_k1Inj_of_hasWitness` (the `k = 1` reading of the power witness), then the assembly of `Palomar/LIXSolution.lean` with `cornerDiag` and the `Fin 2` pinning |

### What the Comparator's shared block must pin

The `n = 2` surface needed one pin this morning; the stronger surface needs the same one and
no more, but for a reason worth writing down.

* **`Fintype (Fin 2)` — pin it, `letI : Fintype (Fin 2) := Fin.fintype 2`.**  `CStarMatrix`
  carries a `Fintype` on the index type and Lean can find more than one term for `Fin 2`;
  this is the pin the Comparator forced.  Keep it inside the `letI` block of every statement
  that mentions `CStarMatrix (Fin 2) (Fin 2) A`.
* **The spectral order pair — pin it, as now.**  `CStarMatrix.instCStarAlgebra` asks for
  `[PartialOrder A] [StarOrderedRing A]`, and `CStarAlgebra.spectralOrder` /
  `CStarAlgebra.spectralOrderedRing` are the unique choice.  On the solution side
  re-register `GroupApproximation.instSpectralPartialOrder` and
  `instSpectralStarOrderedRing` rather than declaring a fresh pair.
* **`Fin n` — nothing to pin, and this is the point.**  The rank `n` enters the Mathlib-only
  statements only as a natural number, in `p ∣ n`.  It is never a matrix index and never an
  index type, so no `Fintype (Fin n)` instance appears in the statement at all.  The whole
  rank-`n` machinery is on the solution side of the wall.  Do not be tempted to state the
  algebra as `CStarMatrix (Fin n) (Fin n) _` anywhere in the challenge.
* **The `CStarAlgebra` instance on the limit — do NOT pin it, and do not let a second one
  exist.**  On the challenge side the instance is existentially bound, `(_ : CStarAlgebra A)`,
  so there is nothing to fix.  On the solution side the witness is `⟨Gen.LIXLimit n,
  inferInstance, …⟩` and `inferInstance` must find exactly the instance the tower builds
  through `Gen.instCStarAlgebraStageAlgebraPi n`.  `sp-tower` flags that this is a **data**
  class and that they deliberately made the `n = 2` instance resolve *through* the generic
  one rather than declaring an independent second: keep it that way.  A second pi-instance
  would be definitionally equal and a different term, and the two environments would then
  disagree on a statement that looks identical.
* **`NeZero n` is a solution-side obligation, not a binder.**  `Nontrivial (Gen.LIXLimit n)`
  carries `[NeZero n]`, and the challenge hypothesis is `2 ≤ n`.  The solution supplies
  `haveI : NeZero n := ⟨by omega⟩`; the challenge must not mention `NeZero`.
* **Nothing new for the powers.**  `v ^ k` is `Monoid.npow` in `unitary A`, which the group
  structure already gives; `pathComponent` needs only the topology induced from `A`.

### The third Comparator configuration

```json
{
  "challenge_module": "Palomar.LIXStrongChallenge",
  "solution_module": "Palomar.LIXStrongSolution",
  "theorem_names": [
    "ProblemLIXStrong.exists_simple_separable_powers_outside_U0",
    "ProblemLIXStrong.exists_simple_separable_order_six_witness",
    "ProblemLIXStrong.exists_simple_separable_squarefree_witness"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

A **new namespace** `ProblemLIXStrong`, not an extension of `ProblemLIX`: the existing
surface is a verified artifact and must keep building unchanged, and two namespaces cannot
collide on `cornerDiag`.  The shared block is copied byte-identically into both new files, as
the existing pair does, and it should be the *same* bytes as the `n = 2` pair's so a reader
can diff the four files and see one block.

## The descent needs no cone operator (answer to `sp-steenrod`, 2026-09-10)

Two questions from `sp-steenrod` before they author: is my contraction simplicial or the dual
of a singular cone, and is the primitive-independence a theorem or an observation.  Answers:
**simplicial, and it does not matter**; and **a theorem, two lines**.

### The descent never leaves a two-letter complex

Let `E` be the two-term complex `E⁰ = K·f`, `E¹ = K·g`, `δf = g`, `δg = 0`.  A map
`E → C^*(X)` is *any* `0`-cochain `f` — singular, simplicial, whatever — and it is a chain map
for free.  Now observe what the descent touches: `D` replaces one `f` by `δf` with a Koszul
sign, `T` and `N` permute slots, `H` acts on one slot.  **Every one of these preserves
`E^{⊗p}`.**  So the whole descent is finite-dimensional linear algebra over `F_p` in `2^p`
words, and it maps into `C^*(X)^{⊗p}` by functoriality of `E → C^*(X)` — no injectivity, no
comparison of models, no cone.

On `E` the contraction is `h(g) = f`, `h(f) = 0`, and `δh + hδ = 1` **with no `ηε` term**,
because `E` is exact (`δ : E⁰ → E¹` is an isomorphism).  That is why `h ⊗ 1^{⊗(p−1)}` suffices
here, for exactly the reason it sufficed on the resolution and failed on chains: there is
nothing in the bottom degree for a residual to leak into.

Concretely on `Δ¹`: take `f` = the affine coordinate (the barycentric coordinate of vertex
`1`), a singular `0`-cochain; then `g = δf` has `g(σ) = f(σ(1)) − f(σ(0))`.  The final
Alexander–Whitney evaluation is unchanged: `f(σ(0)) = 0` kills every term but the one with the
`g` in slot `0`.

**My `h` was simplicial face-removal**, `h(τ^*) = (τ ∖ {0})^*` — `sp-steenrod` read it right —
but that spelling is only how the two-letter complex happened to be presented in a model where
I could also build `Φ`.  The descent itself needs only `E`.

VERIFIED (read): Mathlib has no cone or star operator on singular chains at the pin.  I
grepped `Mathlib/AlgebraicTopology/` and `Mathlib/Topology/Homotopy/` for
`coneOperator`/`singularCone`/`starOperator`/`prismOperator` and for a convex straight-line
contraction, and `SingularHomology/HomologyZero.lean` has nothing usable.  Their check was
right; the cost is real and now avoidable.

### Primitive-independence is a theorem

Perturb `Y_k` by `z` with `D z = 0`.  By exactness `z = D(ζ)`, so `A_{k+1}` changes by
`op(D ζ) = D(op ζ)`, a coboundary; `Y_{k+1}` absorbs it, and

```text
   A_{k+2}  changes by  op'(op(ζ)) = 0 ,
```

because consecutive operators are `N` and `T−1` and `N(T−1) = (T−1)N = T^p − 1 = 0`.  **So a
perturbation introduced at any level but the last dies within two steps.**  At the last step
the answer changes by `⟨D(ξ), AW(σ)⟩ = ⟨ξ, AW(∂σ)⟩`, which vanishes on `Δ¹` by the point lemma
and does not on `Δ²` — exactly the pattern the two runs showed.

`op ∘ op' = 0` is the invariance engine, and it is the same fact as `sp-steenrod`'s "`N e_i` is
a boundary in every degree".  My exhaustive test was in fact complete rather than a sample:
enumerating `D(w)` over all basis words `w` one degree up spans `im D = ker D`, and the
descent's dependence on the perturbation is linear, so invariance on a spanning set is
invariance.

### What does not survive to the singular setting, and what replaces it

`sp-steenrod` is right that my shortcut for the higher constants — reading the coefficient off
the top degree because it is one dimensional — is simplicial and fails singularly, where the
top-degree chain group is enormous.  It does not affect the numbers, which are pairings, but
it is not a Lean route.  **It does not have to be**, because nothing in the Lean chain needs
it:

* `c_1` comes from the descent, which §above shows is model-free;
* `κ_top(q,q') = (−1)^{q q'(p−1)/2}` comes from the coproduct's reduced coefficients (a purely
  algebraic statement about `W ⊗ W`) and the riffle Koszul sign (a sign on degrees) — both
  model-free;
* `c_2 = κ_top(1,1)·c_1²` and `c_{2k} = c_2^k` follow.

So the `Φ`-on-models computation was corroboration and a prediction of the values, not a route
to be formalised.

## Program note audit (2026-09-10)

Read `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` end to end against the seven lane reports.
I do not edit the note.  Fourteen findings, tagged **(a)** stale (true when written, false
now), **(b)** internally inconsistent, **(c)** claim with no artefact.  Ordered by how much
damage a reader takes from them.

### The two the lead named

**A1 (b), §1.3.2 — two dangling corrections that correct text no longer in the note.**
§1.3.2 says "the rotation `ρ` … **in the `e₁`-plane** (not in a plane avoiding `e₁`)", but the
sentence being corrected was replaced when the AGREED block landed, so the parenthesis
corrects something a reader cannot see and reads as a warning about an alternative that was
never proposed.  §1.5 has the same shape: "Correction (sp-coeff, 12:20): graded commutativity
IS provided at `F₂`…" now follows text that no longer says the opposite.  **Fix:** state both
positively ("`ρ` is `x₀ ↦ e^{2πi/k}x₀` in the `e₁`-plane"; "graded commutativity is provided at
`F₂` … and is false at odd `p` without the sign"), and if the history is worth keeping put it
in one dated line at the end of the section rather than inline.

**A2 (a)(b), §1.5 — the constant paragraphs are a revision log, and one of them is
out of order and contradicted.**  Four blocks in sequence: "The normalisation constant
(decided)", "Model caveat (12:55)", "Resolved (12:55): no cone needed", "Settled ~11:50".  The
last is timestamped *before* the two above it, is actually later than 11:50 (the `c_2`
computation landed after 12:15), and asserts `c_2 = −1` "by evaluating on the fundamental class
of the torus" — the `Φ`-on-models route whose top-degree step the paragraph above it
retracts.  The "decided" block also still contains `c_n = (−1)^K λ_n` … "so every constant is
read off the model simplex", which is that same retracted route, two paragraphs before its own
retraction.  And `c_2` is given twice by different means (`κ(1,1)·c_1²`, and "directly").
**Proposed single replacement below.**

### Stale claims

**A3 (a), §1.4 headline — "Conjecture the lanes must turn into a proof".**  It is no longer a
conjecture.  The uniform theorem is proved (my §3.2), stated in the `ParityData` shape, with
every lemma model-tested over 24 cases and `0` failures, and `sp-evenside` has it authored as
`CharClass/ParityPData.lean`.  The same paragraph's closing instruction ("`sp-design` derives
the uniform argument … and model-tests every lemma") is a task that is done.  **Fix:** state
the theorem and cite `sp-design` §3.2 and `sp-evenside`; keep the table as the calibration
record.

**A4 (a), §1.2 — "`sp-design` must confirm … that the zero … is where `b = −a`".**  Confirmed:
`LemmaTwoZero.mtSection_manuscript_eq_zero_iff` gives `t = −1 ∧ y = 0 ∧ b m = −a m ∧ c m = 0`.
**Fix:** replace the instruction with the formula.  The same paragraph's "Lemma 2 is
unchanged" is right about Lemma 2 and silent about the eleven chart-layer files that do change;
the ruling `sp-oddside` asked for and got — do the local model generically in a unit vector `a`
with `Re (a n) = 0` and an ℝ-linear isometry `L` onto `a^⊥`, not as a `Fin 3` relabelling —
belongs here.

**A5 (a)(b), §1.3.2 — the withdrawn renormalisation route is still printed.**  "(`clutch((a·ũ)^k)
≅ clutch(ũ^k)` via `θ ↦ (A_θ ũ)^k ũ^{-k}`, no centrality needed)" is the argument `sp-powers`
**withdrew**: their gauge lemma asks for a BALL unitary, not a disc unitary, so no homotopy is
built — the gauge factor `u^m·(ũ^m)ᴴ` is itself a ball unitary and the left gauge lemma applies
in one step (`clutchEquiv_normGen_pow`).  §1.3 item 1 already carries the replacement, so the
note states both.  The same sentence says "disc unitary" where the landed hypothesis is "ball
unitary", which is exactly the distinction that removed the obligation.

**A6 (a)(b), §1.3 item 2 — the gauge lemma's hypothesis and its open question.**  Item 2 still
reads "If `a ∈ U₀` (extends over the northern hemisphere)" and "(check whether `LIXClutching`
already has it in this generality)".  It is landed as `exists_partialIsometry_of_gauge_left` /
`_right` over `IsBallUnitary`, which is a weaker hypothesis than `a ∈ U₀`, and item 1 above it
already says so.

**A7 (a), §1.4 — the tool pointer.**  "`scratch/lix_modp_fast.py` … source in this session's
scratchpad `sp/`" predates the tools directory.  The eleven tools now live in
`notes/lix-stronger-lane-reports/tools/`.

**A8 (a)(b), §1.1 status paragraph vs §3.**  §1.1 asserts "PROBE GREEN 3040 jobs" at 11:56, and
§3 now says (sp-tower, 13:20) that "every green obtained before the transitive criterion
existed is unevidenced … and must be re-probed before it lands" and (13:40) that a job count is
not a work count.  The 11:56 green predates the 13:00 transitive purge, so the note's own
protocol disqualifies the note's own status line.  **Fix:** mark it pre-purge and pending
re-probe, or re-probe and restate with a `grep -c Built`.

### Inconsistencies

**A9 (b), §0 — the displayed theorem contradicts the §1.6 ratification.**  §0's Lean block uses
`diagOne v ∈ pathComponent 1 (unitary (CStarMat 2 A))`, development vocabulary; §1.6 ratifies
that the challenge states the stabilisation as an existential over a path-component element
whose matrix is `cornerDiag`, with no `diagOne`.  Two further slips in the same block:
`pathComponent 1 (unitary X)` has the arguments the wrong way round (Mathlib's is
`pathComponent (1 : unitary X)`), and `SeparableSpace` is `TopologicalSpace.SeparableSpace`.
**Fix:** either paste the ratified challenge statement or label the block "schematic; the
Mathlib-only form is §1.6".

**A10 (b), §1.4 vs §1.5 — `P(h) = h + h^p` vs the normalisation.**  §1.4 lists the available
relations with `P(h) = h + h^p`, but §1.5 decides the operations are normalised so that
`P^0 = id`, at the price of `P(h) = h + κ h^p` with `κ` a unit.  Everything survives (§3.4a),
but the consequence must be recorded where the relations are listed: **the Wu hypothesis's
leading coefficient is a unit, not `1`**.  `sp-evenside` had hard-coded `1` and has been
corrected; the note should not re-seed the error.  §2's `sp-steenrod` row has the same
`P(h) = h + h^p`.

**A11 (b), §1.3 item 4 vs `sp-oddside`'s plan.**  Item 4 asks for excision to a direct sum and
says the local contributions agree "by naturality of `j` and ABSOLUTE homotopy invariance".
Two changes since: the splitting is the single equation `x = ∑_i ρ_i(x_i)` with `ρ_i ≫ j = j_i`
(no biproduct — `sp-oddside`'s simplification, which I adopted), and the "contributions agree"
step has a **second half** the note never mentions — the local classes corresponding under
`(ρ^i)^*_rel`, which is not free because the mapping-torus bundle is not `ρ`-invariant (`G` comes
from Step A).  It is true, because the local model is `G`-free, but it needs its own lemma.
At `p = 2` neither half is needed at all: an `F₂`-line has one nonzero element.  Also item 4's
`γ_r(W_g) = k·c₀` is `(k+1)·c` in `sp-oddside`'s indexing (their `ψ_k` has degree `k+1`).

**A12 (b), §2 lane table.**  `sp-design` and `sp-evenside` are both assigned **clone spare1 and
cores 96–103**, while §3 says "Never use another lane's clone."  Harmless only because this
lane runs no `lake`; it should say so rather than assert a shared clone.  And `sp-powers`' first
deliverable still names the clutching statement, which §1.3's interface decision moved off the
critical path in favour of the bare homotopy.

### Claims with no artefact behind them

**A13 (c), §0 — "Mod-p cohomology cannot see `p²` (see §1.4)".**  §1.4 contains a model table
and a mechanism, and no argument about `p²`.  The support that exists is indirect: the Step D
theorem concludes `p ∣ k`, and the certificates show the relations constrain residues mod `p`
only.  **Fix:** give the reason in one clause or drop the cross-reference, which currently
promises a justification the target does not contain.

**A14 (c), §1.1 — "this is the only place the tower's shape enters Step D".**  There are **two**
arithmetic inputs, not one: `p ∣ d_j` (which is what this sentence names) and `p ∣ n + m`, i.e.
`r ≡ 1 (mod p)`, which is about the RANK and is what makes the final index land where the
induction has reached.  Both follow from `p ∣ n`, which is why the sentence has never caused
trouble, but as written it is an exhaustive claim that is not exhaustive.

### The consolidated §1.5 constant paragraph

Replacing the four blocks (A2), with the retracted route named as such:

> **The normalisation constant (settled 2026-09-10).**  An abstract equivariant diagonal gives
> every axiom except `P^0 = id`, which is the value of a universal constant `c_q`
> (`Q^0 = c_q·id`); no other axiom pins it (the Frobenius satisfies all of them with `c = 0`).
> Its VALUE never reaches Step D: a rescaling `P'^i = κ^i P^i` preserves every axiom, the
> κ-sweep found `0` of `28` cases dependent on it, and the only consequence downstream is that
> the degree-2 relation reads `P(h) = h + κ h^p` with `κ = c_2^{-1}` a unit — so **every
> statement of the Wu hypothesis carries a unit leading coefficient, not `1`**.  What is needed
> is `c_2 ≠ 0`, and it is now known.
>
> * **`c_1 = ((p−1)/2)!`**, by the descent on `Δ¹`, generic in `p`.  The descent never leaves
>   the two-letter complex `E⁰ = ⟨f⟩`, `E¹ = ⟨g⟩`, `δf = g`, where `h(g) = f` and
>   `h ⊗ 1^{⊗(p−1)}` is a **full** contraction of `E^{⊗p}` (no `ηε` term, `E` being exact); so
>   it is finite linear algebra in `2^p` words, model-free, landing in the singular tensor power
>   by functoriality.  **No cone operator is needed** (there is none in Mathlib at the pin).
>   Primitive-independence is a THEOREM: a perturbation changes the next element by a
>   coboundary the following step absorbs, `N(T−1) = 0` kills the rest, and only the last
>   step's boundary term survives, which vanishes on `Δ¹` by the point lemma.  A descent on
>   `Δ²` is NOT well defined (the ambiguity pairs against `AW(∂σ)`, edges rather than points)
>   and must not be attempted.
> * **`κ_top(q,q') = (−1)^{q q'(p−1)/2}`**, the Cartan coefficient at the TOP corner (both
>   `W`-indices at their maxima), derived and verified: the reduced coproduct coefficient there
>   is always `1` because both indices are even, the rest is the riffle Koszul sign, and the
>   evaluation reordering cancels.  So even-degree multiplicativity holds (`κ_top = 1` when `q`
>   or `q'` is even) and the odd × odd case is `(−1)^{(p−1)/2}`.
> * Hence **`c_2 = κ_top(1,1)·c_1² = −1`** and **`c_{2k} = (−1)^k`**, a unit in every even
>   degree.  Independently confirmed by building the equivariant diagonal `Φ` on the models:
>   `c_2 = −1` at `p = 3,5,7,11`, `c_4 = +1` and `c_6 = −1` at `p = 3`, `c_4 = +1` at `p = 5`,
>   and `c_1` agreeing with the descent at every prime — two computations by different
>   machinery.
> * `sp-steenrod` therefore takes the resolution's coproduct **explicitly** (`sp-design` solved
>   it in closed form, three cases, verified block by block; the abstract route creates an
>   unknown, the explicit one retires it and removes the need for the vanishing below the bottom
>   of the range), and states the bridge with its Künneth prerequisite: two **distinct**
>   degree-one classes with nonzero product, i.e. a torus, since an odd class squares to zero.
>   Their earlier "coefficient `1` in even degrees" lemma was RETRACTED (it evaluated at the
>   bottom corner, the counit case).  The explicit `p`-fold interval-cut diagonal is not built.
>   The lane has no unknown constant anywhere.
> * **Not a route to formalise.**  The `Φ`-on-models computation reads each constant off the top
>   degree of `C_*(Δ^n)^{⊗p}` because that degree has a single basis element.  That is true of
>   the **simplicial** model and false for singular chains, where the top-degree group of a
>   simplex is enormous.  The pairing values transfer; the route does not.  `c_1` comes from the
>   descent and the higher constants from `κ_top`.
