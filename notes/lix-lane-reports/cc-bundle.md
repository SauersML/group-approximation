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

## GREEN — all 12 modules together, `Build completed successfully (2978 jobs)`

Final probe 2026-09-05 late evening naming **all twelve modules in one build**,
so the lane is green as a whole and not only module by module.  The individual
runs before it: 2976 jobs with `✔ Built …BundleFlag`, 2974 with
`✔ Built …BundlePairs`, 2973 with `✔ Built …BundleZeroSection` and
`✔ Built …BundleClassify`.

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

### `BundleZeroSection.lean` (new, green)

`infPoint` (the point at infinity `Q∞`), `zeroSectionProj`, `zTrace` and
`notZeroSet` (the complement of the zero section, cut out by the trace of the
`ι`-block), `zTrace_eq_zero_iff`, `isOpen_notZero_in_proj`, `projRetract`,
`projInclNotZero`, `retractHomotopy` and **`notZeroHomotopyEquivProj :
NotZero p ≃ₕ Proj p`** — the deformation retraction `P(p⊕1) ∖ Z ≃ₕ P(p)` that
`cc-projective`'s Gysin sequence and `cc-thom`'s Thom class both wait on.  Also
`conjNormalize_mem_projFibreSet'`, the generalization of `BundleLocal`'s
conjugation lemma that drops both invertibility and squareness.

### `BundleClassify.lean` (new, green)

`classifyOne : X → CP d`, the classifying map of a rank-one bundle (in this
model a rank-one projection-valued map *is* a map to `ℂP^d`), with
`classifyOne_cpTaut` and `classifyOne_comap`; the block embeddings `blockL`,
`blockR` and the sections `classL`, `classR` into `Proj (triv X (ι ⊕ κ))`; and
**`homotopic_classL_classR`**, the rotation homotopy `v ↦ ((1-t)·v, t·φ v)`
that makes `e(L) := f_L^* h` well defined on isomorphism classes.

### `BundlePairs.lean` (new, green)

The four small statements `cc-thom` listed as C1 to C4, each definitional once
stated: `comapTotal`/`comapProj` with their projection squares (pullback
naturality on the spaces), `totalSet_triv`/`totalTrivHomeo`/`puncturedSet_triv`
(the trivial bundle's total space is the product), `chartOf_mem_notZeroSet_iff`
(the affine chart is a map of PAIRS: `E(p) ∖ 0` corresponds to the part of the
chart missing the zero section), and `totalTrivStd_snd_eq_zero_iff` (the
standard local trivialization is a map of pairs).

## AUTHORED, UNVERIFIED

Nothing — every declaration in all 11 owned modules is green.

## EXPORTS (peers: these are the stable signatures)

Everything below is in `namespace GroupApproximation.CharClass.Bundle`.

### `BundleZeroSection.lean` — the zero section and the Gysin input

```lean
-- the point at infinity: the ONE rank-one projection that is the chart image
-- of E(p)'s zero section, independent of the base point
noncomputable def infPoint (ι : Type) [Fintype ι] : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ
  -- = rankOneProj (Sum.elim 0 (fun _ => 1))
noncomputable def zeroSectionProj (p : Bundle X ι) : C(X, Proj p.plusOne)
theorem projPi_comp_zeroSectionProj (p) :
    (projPi p.plusOne).comp (zeroSectionProj p) = ContinuousMap.id X

-- the complement of the zero section, cut out by ONE continuous scalar
noncomputable def zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) : ℂ
    -- = (blockProj ι * z.2 * (blockProj ι)ᴴ).trace, the trace of the ι-block
def notZeroSet (p : Bundle X ι) : Set (X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)
    -- = {z | z ∈ projSet p.plusOne ∧ zTrace z ≠ 0}
abbrev NotZero (p : Bundle X ι) : Type := ↥(notZeroSet p)
theorem zTrace_eq_zero_iff (hz : z ∈ projSet p.plusOne) :
    zTrace z = 0 ↔ z.2 = infPoint ι
theorem isOpen_notZero_in_proj (p) :
    IsOpen {z : Proj p.plusOne | zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0}
def notZeroToProj (p) : C(NotZero p, Proj p.plusOne)

-- the retraction, choice-free and manifestly continuous
noncomputable def projRetract (p) : C(NotZero p, Proj p)      -- [v : λ] ↦ [v : 0]
noncomputable def projInclNotZero (p) : C(Proj p, NotZero p)
theorem projRetract_projInclNotZero (p) (z) : projRetract p (projInclNotZero p z) = z
noncomputable def retractHomotopy (p) :
    ContinuousMap.Homotopy ((projInclNotZero p).comp (projRetract p))
      (ContinuousMap.id (NotZero p))                          -- [v : λ] ↦ [v : tλ]
noncomputable def notZeroHomotopyEquivProj (p) :
    ContinuousMap.HomotopyEquiv (NotZero p) (Proj p)

-- the lemma that made it possible (generalizes BundleLocal's, which is unusable
-- here because the retracting matrix is neither square nor invertible)
theorem conjNormalize_mem_projFibreSet' {κ} [Fintype κ] [DecidableEq κ]
    {a : Matrix κ ι ℂ} {q : Matrix ι ι ℂ} {q' : Matrix κ κ ℂ}
    (hfix : ∀ u : ι → ℂ, q *ᵥ u = u → q' *ᵥ (a *ᵥ u) = a *ᵥ u)
    (hr : r ∈ projFibreSet q) (hne : (a * r * aᴴ).trace ≠ 0) :
    conjNormalize a r ∈ projFibreSet q'
```

### `BundleClassify.lean` — classifying maps

```lean
def classifyOne {d : ℕ} (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1) :
    C(X, CP d)                                   -- a rank-one bundle IS a map to ℂP^d
theorem classifyOne_apply : (classifyOne p hp x : Matrix _ _ ℂ) = p x
theorem classifyOne_cpTaut (d) : classifyOne (cpTaut d) (trace_cpTaut d) = ContinuousMap.id (CP d)
theorem classifyOne_comap (f : C(Y, X)) :
    classifyOne (comap f p) _ = (classifyOne p hp).comp f

def blockL (ι κ) (q : Matrix ι ι ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ
def blockR (ι κ) (q : Matrix κ κ ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ
def classL (κ) (L : Bundle X ι) (hL : ∀ x, (L x).trace = 1) : C(X, Proj (triv X (ι ⊕ κ)))
def classR (ι) (L' : Bundle X κ) (hL') : C(X, Proj (triv X (ι ⊕ κ)))

-- the rotation v ↦ ((1-t)·v, t·φ v), as conjugation by ONE square block matrix
noncomputable def rotSq (e : BundleIso L L') (t : ℝ) (x : X) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ
theorem homotopic_classL_classR (e : BundleIso L L') (hL : ∀ x, (L x).trace = 1) :
    (classL κ L hL).Homotopic (classR ι L' _)
```

`Proj (triv X ρ)` is the space of ALL rank-one projections on `ℂ^ρ` over `X`,
because `triv`'s absorption condition `1 * q = q` is vacuous; for `ρ = Fin (d+1)`
`projHomeoCP` identifies it with `X × CP d`.  So `homotopic_classL_classR` is
the statement "the two classifying maps into `ℂP^{K+K'-1}` are homotopic", in
the index-free form; compose with `projHomeoCP` and a reindexing to read it in
`CP`.

### `BundleFlag.lean` — the splitting principle, geometric half

```lean
-- one step: the complement of the tautological line, rank one less
noncomputable def flagComplement (p : Bundle X ι) : Bundle (Proj p) ι
theorem tautLine_add_flagComplement (p) (z) :
    tautLine p z + flagComplement p z = comap (projPi p) p z
theorem tautLine_mul_flagComplement / flagComplement_mul_tautLine   -- orthogonality
theorem trace_flagComplement (p) (z) :
    (flagComplement p z).trace = (p ((projPi p) z)).trace - 1
theorem rank_flagComplement (p) (z) :
    (flagComplement p).rank z + 1 = p.rank ((projPi p) z)

-- the flag bundle, as a subspace of ONE ambient space for every stage at once
def flagSet (p : Bundle X ι) (n : ℕ) : Set (X × (ℕ → Matrix ι ι ℂ))
abbrev Flag (p : Bundle X ι) (n : ℕ) : Type := ↥(flagSet p n)
def flagProj (p) (n) : C(Flag p n, X)
def flagForget (p) (n) : C(Flag p (n + 1), Flag p n)
theorem flagProj_comp_flagForget (p) (n) :
    (flagProj p n).comp (flagForget p n) = flagProj p (n + 1)
def flagOne (p : Bundle X ι) : Flag p 1 ≃ₜ Proj p        -- the first stage IS P(p)

-- the r tautological lines, rank one and pairwise orthogonal BY CONSTRUCTION
def flagLine (p : Bundle X ι) (n k : ℕ) : Bundle (Flag p n) ι
theorem trace_flagLine (hk : k < n) (w) : (flagLine p n k w).trace = 1
theorem flagLine_mul_flagLine (hk : k < n) (hl : l < n) (hkl : k ≠ l) (w) :
    flagLine p n k w * flagLine p n l w = 0
theorem comap_mul_flagLine / flagLine_mul_comap (hk : k < n) (w)   -- each line is ≤ p

-- THE DECOMPOSITION
theorem flag_decomposition (p : Bundle X ι) (r : ℕ) (hr : ∀ x, (p x).trace = (r : ℂ))
    (w : Flag p r) :
    comap (flagProj p r) p w = ∑ l ∈ Finset.range r, flagLine p r l w
```

The tower is **not** a `Type`-valued recursion.  Iterating `P(-)` literally
gives a different base space at every stage, so every statement would carry its
own `TopologicalSpace` instance.  A point of the `n`-th stage is the same thing
as a point of `X` with an orthogonal `n`-tuple of lines in its fibre, and that
description lives in `X × (ℕ → Matrix ι ι ℂ)` for all `n` at once.  So the lines
are the coordinates: rank-one, pairwise orthogonal and continuous by
construction, with no choice, no local triviality and no induction.  The single
theorem needing proof is `flag_decomposition`, and it is the trace argument: the
sum of the lines is a subprojection of `p` of the same trace, and a projection
of trace zero is zero.

## NEEDS

Nothing from a peer, and nothing from the roster row is left unstarted.  One
item is deliberately deferred: the `finSumFinEquiv` reindexing of
`homotopic_classL_classR` to a statement about `CP (d + d' + 1)`, whose shape
depends on `cc-projective`'s hyperplane stability.

## TRAPS (all found the hard way; save the next reader the probes)

* **`omit … in` goes above the attribute as well as above the docstring.**  For
  `@[simp] theorem foo`, the line order is `omit [Inst] in`, then `@[simp]`,
  then `theorem`.  The `unusedSectionVars` linter is fatal under
  `-DwarningAsError=true` and fires on instances that appear in the *statement*
  but not in the proof term, which is most `[DecidableEq ι]` in this lane.
* **The `unusedSimpArgs` linter is fatal too**, and it reports the exact
  argument and column, so fix the one it names rather than pruning the list.
  Three textually identical `simp [a, b]` branches can differ: only the branch
  whose goal a `@[simp]` lemma already closes will flag `b`.
* **`rw` order matters when one rewrite destroys another's pattern.**
  `rw [conjNormalize_def, rotSq_conj, trace_rotSq_conj …]` fails, because
  `rotSq_conj` also rewrites the copy of the conjugate *inside* the trace, so
  the trace lemma no longer matches.  Rewrite the trace first.
* **`rw` finishes with a `rfl` at reducible transparency only.**  A goal that is
  `rfl` after unfolding a plain `def` (`infPoint`) needs an explicit `rfl` on
  the next line.
* **A `rw` that closes the goal makes the next tactic fail** with `No goals to
  be solved`; `rw [h]` followed by `exact Homotopic.refl _` is a common instance.
* **`ext` on a `ContinuousMap` equality descends past the map** into `Prod` and
  `Subtype` and leaves a goal about `.1`.  Use `ContinuousMap.ext fun z => …`.

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
