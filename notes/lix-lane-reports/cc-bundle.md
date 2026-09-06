# Lane `cc-bundle`

Owns `GroupApproximation/CharClass/Bundle*.lean`, namespace
`GroupApproximation.CharClass`.  Deliverable: the geometry of complex vector
bundles in the projection model (§2 roster row `cc-bundle` of
`notes/LIX_FULL_PROGRAM_2026-09-05.md`).

## The model, fixed once (peers: this is the interface)

A bundle is a **bundled structure** over an arbitrary finite index type, not
over `Fin K`.

```lean
structure Bundle (X : Type) [TopologicalSpace X] (ι : Type) [Fintype ι] where
  toFun : X → Matrix ι ι ℂ
  continuous_toFun : Continuous toFun
  isStarProjection_toFun : ∀ x, IsStarProjection (toFun x)
```

with a `FunLike` coercion, so `p x : Matrix ι ι ℂ`.  `CP d` is **always**
`STW59.CP d` from `Analysis/LIXProjectiveSpaceModel.lean`; no second model
exists anywhere in this lane.

```lean
def totalSet (p : Bundle X ι) : Set (X × (ι → ℂ)) := {v | p v.1 *ᵥ v.2 = v.2}
def sphereSet / puncturedSet / projSet   -- all Set (X × …)
abbrev Total p := ↥(totalSet p)   abbrev Sphere p := ↥(sphereSet p)
abbrev Punctured p := ↥(puncturedSet p)   abbrev Proj p := ↥(projSet p)
```

## GREEN — all 8 modules, 2974 jobs total (final probe, 2026-09-05)

| module | content |
|---|---|
| `BundleBasic.lean` | `Bundle`, `FunLike`, `rank`, `triv`, `comap` (pullback), `blockSum`, `plusOne`, the bridge `Matrix ι ι C(X,ℂ) ↔ Bundle X ι`, `BundleIso` (rectangular MvN) and its equivalence with `MurrayVonNeumannEquiv` |
| `BundleRankOne.lean` | `eucNormSq`, `lineOf`, `normalizeVec`, `conjNormalize`, `conj_rankOneProj` — the rank-one calculus everything else runs on |
| `BundleSpace.lean` | `totalSet`/`sphereSet`/`puncturedSet`/`projSet`, compactness of `Sphere`/`Proj`, zero section, `totalPi`/`projPi`, `tautLine`, `projSetCP`/`projHomeoCP` (comparison with `STW59.CP`), the campaign bundles `cpTaut`, `hopfLine`, `hopfPerp` |
| `BundleChart.lean` | `projIncl : Proj p ↪ Proj (p.plusOne)` (closed embedding), the affine chart `chartOf : Total p ≃ₜ Chart p` where `Chart p = {z ∈ Proj(p.plusOne) : betaEntry z ≠ 0}` — i.e. **`E(p) ≅ P(p⊕1) ∖ P(p)`, open** |
| `BundleHomotopy.lean` | `Total p ≃ₕ X` (scaling to the zero section), `Punctured p ≃ₕ Sphere p` (normalizing) |
| `BundleLocal.lean` | the intertwiner `intert p x₀ x`, invertibility on `trivSet p x₀` (open, contains `x₀`), `exists_finite_trivializing_cover`, rank locally constant, `totalTriv`/`projTriv` — local triviality against the **abstract** fibre `fibreSet (p x₀)` / `projFibreSet (p x₀)` |
| `BundleInvariance.lean` | `BundleIso p q → Total p ≃ₜ Total q` (`totalHomeo`) and `Proj p ≃ₜ Proj q` (`projHomeo`), both over the base; `tautIso` (tautological lines correspond) |
| `BundleFrame.lean` (new) | `exists_isometry_of_isStarProjection`/`stdFrame`: every star-projection of rank `r` is `W Wᴴ` for an isometry `W : Matrix ι (Fin r) ℂ`, built by peeling rank-one summands; `fibreEquivPi : fibreSet q ≃ₜ (Fin r → ℂ)`, `projFibreEquivCP : projFibreSet q ≃ₜ CP d` (rank `d+1`); composed with `BundleLocal`'s local triviality: `Bundle.totalTrivStd`/`Bundle.projTrivStd` give the **literal** deliverable `E(p)|_U ≅ U × ℂ^r`, `P(p)|_U ≅ U × ℂP^d` |

Deliverables from the roster row now landed: total space, `E(p)∖0`, sphere
bundle, `P(p) ⊂ X × CP(K-1)` with tautological line, `p ⊕ q`, pullback,
`P(p) ⊂ P(p⊕1)`, `E(p) = P(p⊕1)∖P(p)` open, zero section, local triviality,
finite trivializing cover, **literal** `P(p)|_U ≅ U × CP^{r-1}` and
`E(p)|_U ≅ U × ℂ^r`, invariance under MvN equivalence.

## AUTHORED, UNVERIFIED

Nothing — every declaration in all 8 owned modules is green.

## NEEDS

Nothing from a peer.  Two roster items are **not yet started** (left for the
next continuation of this lane, or a peer who wants to build directly on the
green interface above — everything needed is already in place):

1. **`P(p⊕1) ∖ Z ≃ₕ P(p)`** (Z = the zero section's image under the chart,
   i.e. `Z = {z ∈ Proj(p.plusOne) : z.2 = Q∞}` with
   `Q∞ := rankOneProj (Sum.elim (0 : ι → ℂ) (fun _ => 1))`, the single FIXED
   rank-one projection onto the "at infinity" coordinate — this is what
   `chartOf p (zeroSection p x)` works out to, independent of `x`).  This is
   the classical "`ℂP^n` minus a point deformation retracts onto a hyperplane
   not containing it" fact, needed by `cc-projective` for the Gysin sequence
   and by `cc-thom` for its `(P(p⊕1), P(p⊕1)∖Z)` pair.  **Route found but not
   built**: for `z ∈ Proj(p.plusOne)` with `z.2 ≠ Q∞`, the *ι-block*
   `M z := fun i j => z.2 (Sum.inl i) (Sum.inl j) : Matrix ι ι ℂ` is exactly
   `conjNormalize Wᴴ z.2` for the **fixed** isometry
   `W : Matrix (ι ⊕ Unit) ι ℂ`, `W (Sum.inl i) j = if i = j then 1 else 0`,
   `W (Sum.inr ()) j = 0` (so no spanning-vector choice is needed — `M z` is a
   direct, continuous, choice-free function of `z.2`); `(M z).trace = 1 -
   betaEntry z` when `z.2` has trace 1, which is `eucNormSq v ≠ 0` for any
   spanning unit vector `w = (v, c)` of `z.2`, i.e. `z.2 ≠ Q∞ ↔ trace (M z) ≠
   0`.  `retract z := (z.1, (trace (M z))⁻¹ • M z)` lands in `Proj p` (the
   absorption condition transports from `p.plusOne`'s via `mem_plusOne_fibre_iff`).
   The homotopy is `h_t z := (z.1, conjNormalize-style interpolation between
   z.2 and inclMat (retract z).2)` — has not been written; `BundleRankOne`'s
   `continuous_conjNormalize` and `BundleLocal`'s `trace_conj_ne_zero_iff`
   are the continuity tools it needs.
2. **The classifying map of a rank-one bundle and its rotation homotopy.**
   For `ι = Fin K`, a line bundle `p : Bundle X (Fin K)` (rank 1 everywhere)
   has `Proj p ≃ₜ X` (bijective: the only rank-one sub-projection of a rank-1
   `p x` is `p x` itself), so `f_p := tautClassifying p ∘ (that homeomorphism)⁻¹
   : X → CP (K-1)` is the classifying map.  Needed: `f_p` well defined up to
   homotopy under `BundleIso`/rescaling of the ambient `K` (`cc-projective`'s
   NEED, "rotate one embedding into the other").  Not started; the rotation
   homotopy itself (a path of unitaries in `U(K)` conjugating one embedding
   to another) is standard but has not been written in this lane's
   vocabulary.

## TRAPS (all found the hard way; save the next reader the probes)

* **Anonymous constructor `⟨(tuple with a bare literal or an existing
  variable), by …⟩` can make Lean throw `unknown free variable
  _fvar.NNNN`** and silently fail to bind the whole declaration — every
  downstream reference then reports "unknown identifier"/"invalid field",
  which looks like an unrelated cascade.  Hit this three times
  (`zeroSection`, `projIncl`, `totalTriv`/`projTriv`).  Fix: pull the
  membership/side-condition proof out into a **named top-level lemma** and
  reference it as a plain term inside the anonymous constructor — never an
  inline `by` block nested inside a tuple literal.
* **A whole file's worth of "Invalid field `BundleIso.foo`: environment does
  not contain …" for declarations that visibly exist earlier in the same
  file** was **not** actually about those declarations — restating their
  bodies twice over changed nothing.  The real cause: one dot-notation call
  `e.someTheorem` used as a **bare `rw` argument relying on implicit
  unification of an explicit point argument** (`rw [Matrix.mulVec_mulVec,
  e.hom_mul_left]`, not `e.hom_mul_left x`) poisoned everything textually
  after it.  Fix that actually worked: replace **every** dot-notation call to
  a *separately proved theorem* on `BundleIso` (as opposed to a genuine
  structure field — `hom`, `continuous_hom`, `conjTranspose_mul`,
  `mul_conjTranspose`) with the fully qualified `BundleIso.foo e args…`.
  Root cause never fully pinned down; the fully-qualified spelling sidesteps
  whatever it is.
* **Rewriting a variable `q` backward into an expression built from
  `stdFrame hq r hr` breaks the `rw` motive**, because `stdFrame`'s
  well-typedness depends on `hq : IsStarProjection q`, so generalizing `q`
  would need to also generalize `hq`'s type, which `rw` cannot do
  ("motive is not type correct" naming `stdFrame hq` as the offending
  application).  Forward rewrites (`stdFrame`-shaped expression → `q`, or
  `Wᴴ*W` → `1`) are always safe; anything backward needs a separate `have`
  stated purely in terms of `W`/`Wᴴ`, proved without mentioning `q`, then
  rewritten forward at the end to land on the goal.
* **A bare numeral `1` nested two matrix products deep, with no adjacent
  factor pinning both index types simultaneously, elaborates as `(1 : ℕ)`**
  and only shows up as `failed to synthesize HMul ℕ (Matrix …) (Matrix …)`
  several lines away.  Annotate `(1 : Matrix m m ℂ)` explicitly whenever `1`
  is not immediately multiplied against something of manifestly the right
  square type.
* **`Fin.snoc`'s motive `α : Fin (n+1) → Sort*` does not get inferred** when
  the whole `Fin.snoc p x` application is applied to an index immediately
  inside a `show` (it *does* get inferred when the bare function is the
  target of an already-typed `Matrix.of`, e.g. inside a `def`).  Pin it with
  `@Fin.snoc n (fun _ => ℂ) p x i` rather than leaving `α` implicit.
* **`ext v` on a `ContinuousMap`-of-a-subtype-of-a-product equality descends
  through `ContinuousMap.ext`, `Subtype.ext` *and* `Prod.ext` in one step**,
  splitting into a `.1`-goal and a `.2`-goal; a manual `apply Subtype.ext`
  afterward, or a single `show` of the whole tuple, then fails to unify.  Use
  `apply ContinuousMap.ext; intro v; apply Subtype.ext` for full manual
  control instead of the recursive `ext` tactic whenever the target mixes a
  `ContinuousMap` equality with a subtype-of-a-product codomain.
* **`congrArg Prod.fst h'` given an explicit expected type that is itself of
  the form `_.1`** gets unified the wrong way (Lean picks the *outer* `.1`'s
  argument as `congrArg`'s implicit `a`, not the argument `h'` is actually
  about), producing a confusing "expected type ↑z = ↑z'" mismatch.  Let
  `have h1 := congrArg Prod.fst h'` infer its type from `h'` with no
  ascription.
* Many small lemmas about a self-contained algebraic gadget (`inclMat`,
  `chartVec`, `betaEntry`, `fibreSet`/`projFibreSet`) never mention the
  ambient base space `X`, but the section's `variable [TopologicalSpace X]
  [DecidableEq ι]` still gets auto-included and flagged unused.
  `set_option linter.unusedSectionVars false` for the section (an
  already-established pattern in ~20 other files in this repo) is faster and
  less error-prone than chasing exact `omit` lists one theorem at a time.
* `mem_totalSet_iff.mp w.2`'s statement mentions `(p.restrictTo U) w.1`
  (unreduced), while a `show`-stated goal built from `intert_mul` naturally
  produces `p ↑w.1` (reduced) — defeq, but `rw` needs syntactic match.
  `rw [restrictTo_apply] at hw` first.
* `Matrix.trace_mul_comm A B` only closes a calc step directly if the step's
  *stated* LHS is already `(A*B)` in exactly that left-associated grouping;
  otherwise reassociate with `Matrix.mul_assoc` (chosen so the *result*
  matches trace_mul_comm's pattern, not the reverse) before or after.
