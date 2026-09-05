# The LIX clutching layer, and the exact cost of the explicit generator

Lane `lix-clutching`, 5 September 2026.  Companion to
`stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` §§2–3.

This note records (a) the Lean architecture of the clutching layer, which is
elementary and now written, and (b) a **negative finding** about the two
"positive facts" §3 attributes to the explicit generator: they are *not*
elementary, they are Bott's unstable computation, and the manuscript cites
[Bott, p. 315] for exactly them.  The finding matters because it moves work
off this lane's critical path and onto a single, sharply stated input.

## 1. What the clutching layer delivers

`GroupApproximation/Analysis/LIXClutching.lean`.

### 1.1 The model

No bundles, no Chern classes, no homotopy groups.  A *suspension chart* on a
space `X` is a pair of continuous maps

```text
t : X → ℝ        (height)
ν : X → E        (equatorial part, E a real normed space)
‖ν x‖² + (t x)² = 1
```

Any presentation of `S^{n+1}` with a chosen axis carries one, so the layer is
model-agnostic and can be instantiated on whatever `lix-spaces` lands.  The
clutched projection is the explicit matrix

```text
clutchMat t f = ⎡ ((1+t)/2)·1     (1/2)·fᴴ ⎤ ,      f = ‖y‖ · w(y/‖y‖),
                ⎣ (1/2)·f       ((1-t)/2)·1 ⎦
```

in `M_{2k}(ℂ)`, where the only algebraic input is `IsClutchDatum t f`, namely
`fᴴf = f fᴴ = (1-t²)·1`.  Verifications, all proved:

* `clutchMat_conjTranspose`, `clutchMat_mul_self`, `trace_clutchMat` — a
  self-adjoint idempotent of trace `k`.
* Continuity is bought by the factor `‖y‖` in the cone `f`: the direction
  `y/‖y‖` has no limit at either pole, but it is multiplied by something that
  goes to zero.  `continuous_damped` is that mechanism, isolated as a lemma.
* Normalisation check: `k = 1`, `E = ℝ²`, `w =` identity of the circle gives
  `(1/2)(1 + x·σ)` over `S²`, the tautological line of `CP¹`.
* `clutchMat_directSum` — clutching is additive, which is how `u ⊕ 1_H` is
  fed in.

### 1.2 Null-homotopy kills the twist, without functional calculus

The textbook route from "the clutching function is null-homotopic" to "the
clutched bundles are isomorphic" runs through *homotopic projections are
unitarily equivalent*, which needs `(1 - (p-q)²)^{-1/2}` and hence a
continuous functional calculus on `C(X, M_N)`.  That instance ladder is
expensive here (cf. the CFC-on-Calkin experience) and it is avoided
completely.

Instead: write `A_f` for the isometry of `ℂ^k` onto the range of
`clutchMat t f` coming from the *upper* hemisphere trivialisation.  The
comparison map between two clutched projections is `A_g κ A_fᴴ` for a unitary
gauge `κ`.  Expanded into blocks:

```text
seamMat t f g κ m = ⎡ ((1+t)/2)·κ      (1/2)·κ fᴴ ⎤
                    ⎣ (1/2)·g κ      ((1-t)/2)·m  ⎦
```

The naive bottom-right entry is `g κ fᴴ / (2(1+t))`, singular at the south
pole; carrying the renormalised product `m = g κ fᴴ/(1-t²)` as *separate
data* cancels the singularity once and for all.  The four ingredients are then
bound by a single relation,

```text
hseam :  κᴴ gᴴ m = fᴴ,
```

and `seamMat_conjTranspose_mul_self` / `seamMat_mul_conjTranspose` prove

```text
seamᴴ · seam = clutchMat t f ,      seam · seamᴴ = clutchMat t g
```

by pure `fromBlocks` algebra — no square roots, no polar decomposition, no
case splits.  This is the engine.

**Null-homotopy in disc form.**  The hypothesis used is `IsDiscUnitary Ω`: a
continuous unitary-valued `Ω` on the closed unit ball of `E` with `Ω 0 = 1`.
That is *exactly* null-homotopy of `Ω|_{S^n}`, read the manuscript's way — "a
path extends `w` over the disc by collapsing the identity end of the radial
parameter to the centre" — and taking it as the hypothesis removes every
uniform-continuity estimate from the proof.

With `f = cone(Ω|_{S^n})`, `g = ‖ν‖·Ω(ν)` and gauge `κ = Ω(μ)`, where

```text
μ(x) = (seamParam (t x) / ‖ν x‖) · ν x,
seamParam t = min 1 (max 0 ((1-t)·2/3)),
```

the four blocks are continuous for the following reasons, and no others:

| block | damping factor | vanishes at | field continuous on |
|---|---|---|---|
| `(1,1)` | `(1+t)/2` | south pole | `{t ≠ -1}` |
| `(1,2)` | `‖ν‖/2` | both poles | `{ν ≠ 0}` |
| `(2,1)` | `‖ν‖/2` | both poles | `{ν ≠ 0}` |
| `(2,2)` | `(1-t)/2` | north pole | `{t ≠ 1}` |

The one design decision that makes this work is the **plateau** in
`seamParam`: it is `0` at `t = 1` (so `κ → 1` at the north pole, using only
continuity of `Ω` at the centre) and identically `1` on the whole collar
`t ≤ -1/2` (so `μ = ν/‖ν‖` there and the correction collapses to
`m = Ω(ν)`, continuous at the south pole).  A smooth interpolation without a
plateau would instead require uniform continuity of `Ω` on a compact set;
the plateau buys it for free.

Result:

```text
exists_partialIsometry_of_isDiscUnitary :
  IsSuspensionChart t ν → IsDiscUnitary Ω →
  ∃ V, Continuous V ∧ (∀ x, (V x)ᴴ * V x = clutchMat (t x) (coneMat Ω (ν x)))
                    ∧ (∀ x, V x * (V x)ᴴ = clutchMat (t x) (‖ν x‖ • 1))
```

and its contrapositive `not_isDiscUnitary_of_clutchingObstruction`.

### 1.3 The single input owed

`ClutchingObstruction t ν Ω` — the clutched projection is *not* Murray–von
Neumann equivalent to the untwisted one.  It is stated as a named `Prop` with
no proof and no instance; it is the manuscript's Lemma 2 in clutched form,
and it is the only thing the reduction needs.  Murray–von Neumann equivalence
transports it (`W = V·Wᴴ` composition), so the obstruction lane may deliver it
for `F ⊕ H` in whatever concrete model it prefers, provided the bridge
`clutch u ≅ F` is available — see §3.

## 2. The explicit generator

The generator is pinned as the quaternionic suspension of the Hopf map.  Write
`S⁴ ⊂ ℂ² × ℝ`, a point being `((z,w), s)` with `|z|² + |w|² + s² = 1`, and set
`n = (|z|²+|w|²)^{1/2}`.  Then

```text
u((z,w), s) = ⎡ s + i(|z|²-|w|²)/n        2 z w̄ / n     ⎤
              ⎣  -2 z̄ w / n          s - i(|z|²-|w|²)/n ⎦
```

This is the map `Ση : S⁴ → S³ = SU(2)`, in quaternion form
`u(v,s) = s + v i v̄ / |v|` for `v ∈ ℍ = ℝ⁴`: the suspension parameter is `s`,
and at each latitude the equatorial `S³` is sent to `S² ⊂ Im ℍ` by the Hopf
map `v ↦ v i v̄`, scaled by `|v|`.

Facts that are cheap and are formalised:

* `u` lands in `SU(2)`: `|α|² + |β|² = s² + ((|z|²-|w|²)² + 4|z|²|w|²)/n²
  = s² + n² = 1`.
* `u` is continuous, including at the two poles `n = 0`, because both
  off-diagonal-type coefficients are `O(n)`; with Lean's `x/0 = 0` the formula
  is total and needs no case split in the definition.
* `u(pole) = ±1`, so `u` is a based map.

## 3. Negative finding: (i) and (ii) are Bott, not elementary

The lane brief asked for direct proofs that

* (i) `u²` is null-homotopic in `U(2)`-valued maps on `S⁴`;
* (ii) `u ⊕ 1 : S⁴ → U(3)` is null-homotopic;

on the grounds that "the manuscript proves them directly".  It does not.  §3
of the manuscript derives both from
`π₄(U(2)) ≅ ℤ/2`, `π₄(U(3)) = 0`, cited to [Bott, p. 315].  Neither is
reachable by an explicit contraction, for reasons that are worth recording so
the lane is not re-attempted.

### 3.1 (i) is exactly `2·Ση = 0` in `π₄(S³) = ℤ/2`

`u = Ση` and `u² ` is, pointwise, the quaternion square:
`u(v,s)² = cos 2θ + sin 2θ · η̂` where `s = cos θ`, `|v| = sin θ`.  Every
homotopy of the *restricted* form `cos g_τ(θ) + sin g_τ(θ)·η̂` is obstructed:
continuity at the poles forces `sin g_τ(0) = sin g_τ(π) = 0`, so
`g_τ(0), g_τ(π) ∈ πℤ`; these are constant in `τ`, hence `g_τ(0) = 0` and
`g_τ(π) = 2π` throughout, while a constant end map needs `g_1` to be
`πℤ`-valued and continuous, hence constant.  Contradiction.  A null-homotopy
must therefore leave the "θ-only" family entirely — which is precisely the
content of `π₄(S³) = ℤ/2` (equivalently, that the suspension
`π₃(S²) = ℤ → π₄(S³)` is reduction mod 2), an EHP/Freudenthal computation.

**Consequence for the counterexample:** (i) is *not* needed for the negative
answer to Problem LIX.  It gives "order **exactly** two" in `U(A)/U₀(A)`.
Failure of `K₁`-injectivity needs only `v ∉ U₀(A)` together with `[v] = 0` in
`K₁(A)`, and `K₁(A) = 0` supplies the latter for free (manuscript Lemma 5).

### 3.2 (ii) and `clutch u ≅ F` are one and the same input

Both follow from a single object: an **explicit pair of continuous local
sections** `σ_± : D_± → U(3)` of the frame fibration `a ↦ a e₃` over the two
closed hemispheres of `S⁵`, with `u` their seam discrepancy
`σ_+^{-1}σ_-|_{S⁴}`.  Given those,

* `clutch u ≅ F` holds by construction (the sections *are* the hemisphere
  trivialisations of `F(x) = 1 - x xᴴ`), and
* (ii) is explicit: `σ_±|_{S⁴}` each extend over a disc, hence are
  null-homotopic in `U(3)`, hence so is their product `u ⊕ 1` — the only extra
  ingredient being a path in `U(3)` from the constant `σ_+(N)σ_-(S)ᴴ` to `1`.

So the whole question is whether such `σ_±` can be written down.  **They
cannot be, by the natural ansatz, and the obstruction is visible.**  The
canonical candidate is the planar rotation carrying `e₃` to `x` inside
`span{e₃, x}`, which is a genuine section only after a phase choice `λ(x)`;
regularity at `|x₃| → 1` forces `λ = x₃/|x₃| + O(1-|x₃|²)`, and the resulting
section

```text
σ(x) = 1 + (x₃-1) e₃e₃ᴴ + y e₃ᴴ - (x₃/|x₃|) e₃ yᴴ - y yᴴ/(1+|x₃|),
        y = x - x₃e₃,
```

is singular exactly on the great `S³ = {x₃ = 0}` — which meets **both**
hemispheres, whatever equator is chosen.  Nor can the phase be repaired: any
continuous `λ` on `S⁵` (or on `S⁵` minus a point) that agrees with `α` on the
polar circle `{αe₃ : |α| = 1}` restricts, on each level set `{|x₃| = 1-ε} ≅
S¹ × S³`, to a map homotopic to the `S¹`-projection, which does not extend
over `{|x₃| ≤ 1-ε}`.  Three charts suffice (`{x ⊥ p}` is missed for each of
three independent `p`), but three charts is not a two-hemisphere clutching.

This is not a defect of the formula: it *is* the nontriviality of `F`, showing
up where it must.

### 3.3 What to ask for instead

The clutching layer needs exactly one topological input, and it is best taken
in clutched form, so that no bundle-to-projection bridge is needed at all:

> **`ClutchingObstruction t ν Ω`** for the suspension chart of `S⁵ × Y`,
> `E`-part the `S⁵` factor, and `Ω` the comparison map `u ⊕ 1_H`: the
> projection clutched by `u ⊕ 1_H` is not Murray–von Neumann equivalent to
> the untwisted projection of the same rank.

This is the manuscript's Lemma 2 (`F ⊕ H ≇ 1² ⊕ H`) once `clutch u ≅ F` is
in hand, and it is *equivalent* to it, so nothing is lost by stating it this
way.  If the obstruction lane prefers to work with `F` directly, the bridge
`clutch u ≅ F` is the extra item, and by §3.2 it is the same object as (ii).

Recommended split:

| item | owner | status |
|---|---|---|
| clutched projection, continuity, seam isometry, null-homotopy ⇒ equivalence | `lix-clutching` | **proved** |
| explicit `u`, unitary and continuous | `lix-clutching` | **proved** |
| `ClutchingObstruction` for `u ⊕ 1_H` (= Lemma 2) | `lix-obstruction` | named `Prop` |
| `clutch u ≅ F` (= hemisphere trivialisations of `F`, = (ii)) | `lix-obstruction` | named `Prop`; **not** elementary |
| `u²` null-homotopic (= `π₄(U(2)) = ℤ/2`) | — | named `Prop`; **not needed** for the negative answer |

## 4. Files

* `GroupApproximation/Analysis/LIXClutching.lean` — the layer.
* `GroupApproximation/Analysis/LIXGeneratorUnitary.lean` — the explicit `u`
  and the three named `Prop`s.
