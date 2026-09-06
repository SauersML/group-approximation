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

## GREEN — 22 modules; `BundleGysinPieces` at 2976 jobs; `BundleProjOver` at 2970 jobs; `BundleOneStep` at 8672 jobs; `BundleBlockIter` at 8808 jobs; `BundleTautRestrict` at 8671 jobs; `BundleLineTriv` and `BundleInvariance` at 8671 jobs, `BundleCoordEmbed` at 8669 (both import
`cc-projective`'s `ProjectiveSpaceHyperplane`), `BundleRank` at 2970,
`BundleBlockIncl` at 2975, `BundleStabilize` at 2974, the other twelve
together at 2978

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

### `BundleInvariance.lean` — dot notation for the transport methods

```lean
def BundleIso.toTotalHomeo (e : BundleIso p q) : Bundle.Total p ≃ₜ Bundle.Total q
def BundleIso.toProjHomeo  (e : BundleIso p q) : Bundle.Proj p  ≃ₜ Bundle.Proj q
def BundleIso.toTautIso    (e : BundleIso p q) : BundleIso (Bundle.tautLine p) (…)
theorem BundleIso.toTotalHomeo_eq / toProjHomeo_eq / toTautIso_eq      -- each `rfl`
theorem BundleIso.toTotalHomeo_over_base / toProjHomeo_over_base       -- each `rfl`
```

`BundleIso` is declared in `CharClass` while `totalHomeo`, `projHomeo` and
`tautIso` are declared in `CharClass.Bundle`, so dot notation never reached
them: it looks in the structure's own namespace and finds nothing, and even a
bare `BundleIso.projHomeo` written inside `namespace Bundle` resolves to the
structure's namespace rather than the enclosing one.  The aliases sit in the
structure's namespace under new names; the originals are untouched.
`toTautIso` is stated at the original's type **verbatim**, so alias and
original are the same term at the same type and `rw` can move between them.

### `BundlePairs.lean` — the trivial bundle's sphere and punctured space

```lean
def sndSubtypeHomeo (S : Set B) : ↥{v : A × B | v.2 ∈ S} ≃ₜ A × ↥S
theorem sphereSet_triv : sphereSet (triv X ι) = {v : X × (ι → ℂ) | v.2 ∈ unitVectors ι}
noncomputable def sphereTrivHomeo : Sphere (triv X ι) ≃ₜ X × ↥(unitVectors ι)
noncomputable def puncturedTrivHomeo : Punctured (triv X ι) ≃ₜ X × ↥({v : ι → ℂ | v ≠ 0})
theorem sphereTrivHomeo_fst / puncturedTrivHomeo_fst                   -- over the base
noncomputable def prodPuncturedHomotopyEquivSphere :
    ContinuousMap.HomotopyEquiv (X × ↥({v : ι → ℂ | v ≠ 0})) (X × ↥(unitVectors ι))
```

The replacement step for a Thom or Gysin argument: over any base at once,
`X × (ℂ^ι ∖ 0)` is homotopy equivalent to `X × S(ℂ^ι)`, by normalizing the
second coordinate and leaving the first alone.  With it the pair
`(X × ℂ^r, X × (ℂ^r ∖ 0))` becomes `(X × ℂ^r, X × S^{2r-1})`, and the long exact
sequence of the pair plus an **absolute** Kunneth for a sphere factor computes
it: no relative Kunneth, and no hypothesis on the base.  The map of pairs is the
identity on the total space and the retraction on the subspace, so it is not a
homeomorphism of pairs; the five lemma is the way in, and `cc-projective`'s
`bijective_of_ladder` is that five lemma in element form.

**`trivSet p x₀` carries no contractibility and cannot be made to.**  It is
`{x | (intert p x₀ x).det ≠ 0}`, open and containing `x₀`, and nothing more is
true of it because nothing more is true of a compact Hausdorff space: a Cantor
set has a neighbourhood basis of Cantor sets.  Shrinking the trivializing set is
free, since the trivialization is an explicit formula in `intert` rather than a
choice, but a contractible shrink is a property of the BASE and has to be
hypothesized or supplied by whoever owns the base.

### `BundleGysinPieces.lean` — the two pieces of the Gysin cover

```lean
def chartOpensSet (p : Bundle X ι) : Set (Proj p.plusOne)      -- betaEntry ≠ 0
def notZeroOpensSet (p : Bundle X ι) : Set (Proj p.plusOne)    -- zTrace ≠ 0
def chartHomeoOpens / notZeroHomeoOpens / interHomeoOpens / puncturedHomeoInter
noncomputable def chartOpensHomotopyEquivBase (p) : ↥(chartOpensSet p) ≃ₕ X
noncomputable def notZeroOpensHomotopyEquivProj (p) : ↥(notZeroOpensSet p) ≃ₕ Proj p
noncomputable def interHomotopyEquivSphere (p) :
    ↥(chartOpensSet p ∩ notZeroOpensSet p) ≃ₕ Sphere p
```

**The complement of the zero section retracts onto `P(p)`, NOT onto the base.**
That is the whole point of the Gysin cover: one piece is the base, the other is
the hyperplane at infinity, and the sequence relates them.  Both are plausible
spaces over the same base, so the wrong reading is hard to notice; the signature
refuses it.

**No new homotopy appears here.**  All three reduce to
`totalHomotopyEquivBase`, `notZeroHomotopyEquivProj` and
`puncturedHomotopyEquivSphere`.  What the file actually adds is four flattening
homeomorphisms: every space in this lane is a subtype of `X × Matrix`, while a
cover of `Proj p.plusOne` produces subsets of that subtype.  Together with
`projOverHomeo` this is the third time that mismatch has had to be bridged, so
expect it again.

### `BundleProjOver.lean` — the part of `P(p)` over an open set

```lean
def projOverSet (p : Bundle X ι) (U : Set X) : Set (Proj p) := (projPi p) ⁻¹' U
def projOverHomeo (p) (U) : Proj (p.restrictTo U) ≃ₜ ↥(projOverSet p U)
theorem projOverHomeo_over_base / projOverHomeo_snd                     -- both `rfl`
theorem restrictTo_plusOne (p) (U) :
    (p.restrictTo U).plusOne = (p.plusOne).restrictTo U                 -- `rfl`
```

`Proj (p.restrictTo U)` and the part of `Proj p` over `U` are the same space but
not the same subtype: the first sits in `↥U × Matrix`, the second in
`X × Matrix`.  Every trivialisation in this lane is stated in the first form and
a cover induction over the base produces the second, so the comparison has to
exist somewhere.  It is pure point-set, because the four conditions cutting out
`projSet` mention the base point only through `p` at it.

`restrictTo_plusOne` holding on the nose is what matters most: it makes
`Proj ((p.restrictTo U).plusOne)` and `Proj ((p.plusOne).restrictTo U)` the
**same type**, so no transport appears between this lane's spelling and a
consumer's.

**The reason the interface takes no contractibility hypothesis.**  A cover
induction produces intersections of trivialising sets with arbitrary opens.
Those stay trivialising, because `trivSet` is a determinant non-vanishing
condition and an intersection of those is another one, but they stop being
contractible.  So a chart step must be stated over an arbitrary trivialising
open, never over a contractible one.  Same distinction as the shrinking question
recorded above, from the other direction.

### `BundleOneStep.lean` — the one-step comparison of the two embeddings

```lean
def sumUnitEquiv (d : ℕ) : Fin (d + 1) ⊕ Unit ≃ Fin (d + 1 + 1)   -- THE reindexing
theorem sumUnitEquiv_inl / sumUnitEquiv_inr
theorem sumInclLeft_sumUnitEquiv (d) :
    sumInclLeft (sumUnitEquiv d) = coordIncl (Fin.castSucc : Fin (d+1) → Fin (d+1+1))
theorem finRotate_castSucc (d) (i) : finRotate (d + 1 + 1) i.castSucc = i.succ
theorem coordIncl_finRotate_isometry / coordIncl_finRotate_mul_conjTranspose
theorem coordIncl_finRotate_mul_castSucc (d) :
    coordIncl (⇑(finRotate (d + 1 + 1))) * coordIncl Fin.castSucc = shiftMat d
theorem coordIncl_finRotate_mul_sumInclLeft
```

`projIncl` adds a coordinate at the **front**; the hyperplane inclusion of
`ℂP^d` adds it at the **back**.  Two injections into the same finite target of
the same size differ by a permutation of the target, and here it is the one-step
rotation, with no wraparound because `castSucc` is never the last coordinate.
`sumUnitEquiv` is the reindexing to use wherever `plusOne`'s `ι ⊕ Unit` meets
`ℂP`'s `Fin (d+2)`; **do not introduce a second one**.

Matrix level only.  Turning `coordIncl (finRotate _)` into a permutation of
`ℂP^d` is cc-projective's `permCP`, left to them rather than guessed at.

### `BundleBlockIter.lean` — the block inclusion IS the iterated hyperplane inclusion

```lean
def iterFin (d : ℕ) : (k : ℕ) → Fin (d + 1) → Fin (d + k + 1)      -- i ↦ i + k
theorem iterFin_val (d k) (i) : (iterFin d k i).val = i.val + k
noncomputable def iterMat (d : ℕ) : (k : ℕ) → Matrix (Fin (d + k + 1)) (Fin (d + 1)) ℂ
theorem iterMat_isometry / iterMat_eq_coordIncl / cpEmbed_iterMat_succ

def blockEquivIter (d) : Fin (d + 1) ⊕ Fin (d + 1) ≃ Fin (d + (d + 1) + 1)
noncomputable def cpBlockInclIter (d : ℕ) : C(CP d, CP (d + (d + 1)))
theorem blockEquivIter_ne_iterFin (d) (i k) :
    blockEquivIter d (Sum.inl i) ≠ iterFin d (d + 1) k
theorem homotopic_cpBlockInclIter (d) :
    (cpBlockInclIter d).Homotopic (cpEmbed (iterMat d (d + 1)) _)
theorem homotopic_classifyOne_blockInclIter (hp) (hq) (e : BundleIso p q) :
    ((cpBlockInclIter d).comp (classifyOne p hp)).Homotopic
      ((cpBlockInclIter d).comp (classifyOne q hq))
```

**The obstacle was arithmetic, not conceptual.**  The `(d+1)`-fold hyperplane
iterate lands in `Fin (d + (d + 1) + 1)` while `cpBlockIncl` lands in
`Fin (2 * d + 1 + 1)`.  Those are equal for every `d` but **not**
definitionally, because `2 * d` does not reduce for a variable `d`.  Casting
between them would have built a parallel `Fin`-congruence layer beside the clean
one.  Instead the block inclusion is restated at the iterate's index:
`blockEquivIter` is `blockEquiv` with its `finCongr` aimed at
`d + (d + 1) + 1`, everything downstream is the existing `sumInclLeft` suite
applied to it, and no cast appears anywhere.  `cpBlockIncl` at `2 * d + 1` is
untouched, per rule 11.

The bridge itself is `homotopic_cpEmbed_of_orthogonal`, and the orthogonality is
a value comparison: the left block occupies the first `d + 1` coordinates and
the iterate shifts past all of them.

### `BundleTautRestrict.lean` — the tautological line along the hyperplane

```lean
def inlMat (ι : Type) [Fintype ι] [DecidableEq ι] : Matrix (ι ⊕ Unit) ι ℂ
theorem inlMat_isometry (ι) : (inlMat ι)ᴴ * inlMat ι = 1
theorem inlMat_conj (ι) (q) : inlMat ι * q * (inlMat ι)ᴴ = inclMat q
theorem inclMat_apply_inl_inr / inclMat_apply_inr_inl                  -- both `rfl`

def tautRestrictIso (p : Bundle X ι) :
    BundleIso (comap (projIncl p) (tautLine p.plusOne)) (tautLine p)
theorem tautRestrictIso_hom (p) (z) :
    (tautRestrictIso p).hom z = (z : X × Matrix ι ι ℂ).2 * (inlMat ι)ᴴ     -- `rfl`
```

The hyperplane at infinity carries the tautological line to the tautological
line.  The two sides are indexed by `ι ⊕ Unit` and by `ι`, so the comparison is
the block padding rather than an identity, and a `BundleIso` being rectangular
is exactly what absorbs it.  The implementer is the point's own matrix followed
by the block row, and both identities use only that the point is a self-adjoint
idempotent and that `inlMat` is an isometry: `aᴴ a = inclMat r` because
`r r = r`, and `a aᴴ = r` because `inlMatᴴ inlMat = 1`.

### `BundlePairs.lean` — the fibre inclusion as a strict map of pairs

```lean
def sliceIncl {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (a : A) : C(B, A × B)
theorem snd_comp_sliceIncl (a) :
    (ContinuousMap.snd : C(A × B, B)).comp (sliceIncl a) = ContinuousMap.id B     -- `rfl`
theorem sliceIncl_preimage (a) (S : Set B) :
    sliceIncl a ⁻¹' {v : A × B | v.2 ∈ S} = S                                     -- `rfl`
theorem snd_preimage (S : Set B) :
    (ContinuousMap.snd : C(A × B, B)) ⁻¹' S = {v : A × B | v.2 ∈ S}               -- `rfl`
theorem sliceIncl_mapsTo / snd_mapsTo
theorem sliceIncl_preimage_puncturedSet_triv / sliceIncl_preimage_totalSet_triv
```

The retraction identity is the whole content of the nonvanishing step in a Thom
argument: pullback along the projection has a left inverse, so it is injective,
so a class pulled back from the fibre cannot vanish.  Stated at a general
product `A × B` rather than at `V × ℂ^r`, because nothing in it uses either
factor, and as PREIMAGE equations rather than memberships or images, which is
the hypothesis shape a relative-cohomology functor takes.

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

The decomposition reaches `cc-wu`'s `SqData` (`CharClass/WuDiagonal.lean`)
**through `cc-projective`'s Whitney formula, not directly**: `ParityData` has no
`decomposition` field, and `cc-wu` consumes none of `comap`, `flagLine` or
`flagProj` (their correction, recorded here so the next reader does not repeat
my mistake).  The index convention is theirs: sums over `Finset.range r` with
natural-number indices, so that `esymmOn s y j` needs no coercions; do not
switch to `Fin r`.

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

### `BundleStabilize.lean` — the stabilised classifying map

The form `cc-projective`'s Euler class consumes.  In `ℂP^d` itself isomorphic
line bundles need **not** have homotopic classifying maps; they do after one
stabilisation along a linear isometric embedding with room for two disjoint
copies.

```lean
def cpEmbed (V : Matrix (Fin (N+1)) (Fin (d+1)) ℂ) (hV : Vᴴ * V = 1) : C(CP d, CP N)
theorem cpEmbed_apply : (cpEmbed V hV z : Matrix _ _ ℂ) = V * (z : Matrix _ _ ℂ) * Vᴴ

noncomputable def stabRot (e : BundleIso p q) (A B) (t : ℝ) (x : X)
    -- = ((1-t : ℝ) : ℂ) • A + ((t : ℝ) : ℂ) • (B * e.hom x)

theorem homotopic_cpEmbed_of_iso (e : BundleIso p q)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0)
    (hp : ∀ x, (p x).trace = 1) (hq : ∀ x, (q x).trace = 1) :
    ((cpEmbed A hA).comp (classifyOne p hp)).Homotopic
      ((cpEmbed B hB).comp (classifyOne q hq))

theorem homotopic_cpEmbed_same (e : BundleIso p q) (hA hB hAB hBA hp hq) :
    ((cpEmbed A hA).comp (classifyOne p hp)).Homotopic
      ((cpEmbed A hA).comp (classifyOne q hq))       -- SAME embedding both sides

-- a splitting of ℂ^{N+1} from any equivalence of index types
def sumInclLeft (eqv : ι ⊕ κ ≃ ρ) : Matrix ρ ι ℂ
def sumInclRight (eqv : ι ⊕ κ ≃ ρ) : Matrix ρ κ ℂ
theorem sumInclLeft_isometry / sumInclRight_isometry
theorem sumInclLeft_conjTranspose_mul_right / sumInclRight_conjTranspose_mul_left
```

`homotopic_cpEmbed_same` is obtained by rotating twice, once along the
isomorphism and once along the identity of `q`.

### `BundleBlockIncl.lean` — the concrete instance `cc-projective` states over

```lean
def blockEquiv (d : ℕ) : Fin (d + 1) ⊕ Fin (d + 1) ≃ Fin (2 * d + 1 + 1)
noncomputable def cpBlockIncl (d : ℕ) : C(CP d, CP (2 * d + 1))

theorem cpBlockIncl_apply (d) (z) :                       -- the matrix, in closed form
    (cpBlockIncl d z : Matrix _ _ ℂ)
      = sumInclLeft (blockEquiv d) * (z : Matrix _ _ ℂ) * (sumInclLeft (blockEquiv d))ᴴ
theorem cpBlockIncl_apply_left (d) (z) (i j : Fin (d+1)) :
    (cpBlockIncl d z : Matrix _ _ ℂ) (blockEquiv d (.inl i)) (blockEquiv d (.inl j))
      = (z : Matrix _ _ ℂ) i j
theorem cpBlockIncl_apply_row (d) (z) (k) (t) :
    (cpBlockIncl d z : Matrix _ _ ℂ) (blockEquiv d (.inr k)) t = 0
theorem cpBlockIncl_apply_col (d) (z) (s) (k) :
    (cpBlockIncl d z : Matrix _ _ ℂ) s (blockEquiv d (.inr k)) = 0

theorem homotopic_classifyOne_blockIncl (hp) (hq) (e : BundleIso p q) :
    ((cpBlockIncl d).comp (classifyOne p hp)).Homotopic
      ((cpBlockIncl d).comp (classifyOne q hq))
```

The three entry lemmas determine the matrix, because `blockEquiv d` is a
bijection: an index is `Sum.inl i` or `Sum.inr k`, giving the entry of `z` or
zero.  `CP (2*d+1)` has matrices indexed by `Fin (2*d+1+1)`, which is `Fin (2*d+2)`
definitionally.

### `BundleRank.lean` — one global rank on a connected base

New names; nothing published is changed (fleet rule 11).

```lean
theorem isLocallyConstant_rank (p : Bundle X ι) : IsLocallyConstant p.rank
theorem rank_eq_of_isPreconnected (p) (hs : IsPreconnected s) (hx : x ∈ s) (hy : y ∈ s) :
    p.rank x = p.rank y
theorem rank_eq_of_preconnectedSpace [PreconnectedSpace X] (p) (x y) : p.rank x = p.rank y
theorem rank_eq_of_preconnectedSpace_of_eq [PreconnectedSpace X] (p) (hr : p.rank x₀ = r) (x) :
    p.rank x = r
theorem trace_eq_of_preconnectedSpace [PreconnectedSpace X] (p) (hr : p.rank x₀ = r) (x) :
    (p x).trace = (r : ℂ)                       -- the hypothesis shape of flag_decomposition
theorem exists_trace_eq_of_preconnectedSpace [PreconnectedSpace X] [Nonempty X] (p) :
    ∃ r : ℕ, ∀ x, (p x).trace = (r : ℂ)
theorem rank_eq_succ_of_preconnectedSpace [PreconnectedSpace X] (p) (hd : p.rank x₀ = d + 1) (x) :
    p.rank x = d + 1                            -- the rank convention of projTrivStd
```

`BundleLocal.exists_open_rank_eq` is exactly the right-hand side of
`IsLocallyConstant.iff_exists_open`, so the upgrade is three lines and all the
content is in the local statement.  Every base in the programme is connected, so
the connected form is the one that gets used.

### `BundleCoordEmbed.lean` — identifying a `cpEmbed`

The three facts `cc-projective` needs to make the Euler class invariant.

```lean
def coordIncl (f : ι → ρ) : Matrix ρ ι ℂ                      -- the matrix [s = f i]
theorem coordIncl_isometry (hf : Function.Injective f) : (coordIncl f)ᴴ * coordIncl f = 1
theorem coordIncl_conj_apply (hf) (z) (i j) :
    (coordIncl f * z * (coordIncl f)ᴴ) (f i) (f j) = z i j
theorem coordIncl_conj_apply_row / coordIncl_conj_apply_col      -- zero off the image
theorem coordIncl_conjTranspose_mul_of_disjoint (h : ∀ i k, f i ≠ g k) :
    (coordIncl f)ᴴ * coordIncl g = 0
theorem coordIncl_mul_coordIncl (f) (g) : coordIncl g * coordIncl f = coordIncl (g ∘ f)
theorem sumInclLeft_eq_coordIncl (eqv) : sumInclLeft eqv = coordIncl (fun i => eqv (Sum.inl i))

theorem isometry_mul (hA) (hB) : (B * A)ᴴ * (B * A) = 1
theorem cpEmbed_comp (hA) (hB) :
    (cpEmbed B hB).comp (cpEmbed A hA) = cpEmbed (B * A) (isometry_mul hA hB)
theorem homotopic_cpEmbed_of_orthogonal (hA) (hB) (hAB : Aᴴ * B = 0) (hBA : Bᴴ * A = 0) :
    (cpEmbed A hA).Homotopic (cpEmbed B hB)

def shiftMat (d : ℕ) : Matrix (Fin (d + 2)) (Fin (d + 1)) ℂ
theorem shiftMat_isometry (d) : (shiftMat d)ᴴ * shiftMat d = 1
theorem cpEmbed_shiftMat (d : ℕ) :
    cpEmbed (shiftMat d) (shiftMat_isometry d)
      = (⟨CPn.incl, CPn.continuous_incl⟩ : C(CP d, CP (d + 1)))
```

**`homotopic_cpEmbed_of_orthogonal` needs orthogonality and that is not a
technicality.**  Two arbitrary isometries into the same space do give homotopic
maps, but that is the connectivity of a Stiefel manifold and is not proved here.
The orthogonal case is enough for the Euler class, because the block isometry
lands in the first block and the iterated hyperplane inclusion lands in the last.

This is the lane's only module that imports a peer's file
(`ProjectiveSpaceHyperplane`, to state `cpEmbed_shiftMat`); nothing of theirs
imports it, so there is no cycle.

### `BundleLineTriv.lean` — trivializing a line, and the Leray-Hirsch base case

```lean
theorem rankOneProj_mulVec (w v) : rankOneProj w *ᵥ v = (∑ k, star (w k) * v k) • w
theorem lineOf_eq_of_mem_fibre (hq : IsStarProjection q) (htr : q.trace = 1)
    (hv : v ≠ 0) (hfix : q *ᵥ v = v) : lineOf v = q

def colOf (p : Bundle X ι) (i : ι) (x : X) : ι → ℂ          -- the i-th column of p x
theorem colOf_mem_fibre (p) (i) (x) : p x *ᵥ colOf p i x = colOf p i x
theorem colOf_ne_zero (p) (hi : p x i i ≠ 0) : colOf p i x ≠ 0
theorem continuous_colOf (p) (i) : Continuous (colOf p i)

noncomputable def lineIso (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (i : ι)
    (hi : ∀ x, p x i i ≠ 0) : BundleIso p (triv X (Fin 1))

def isoPlusOne (e : BundleIso p q) : BundleIso p.plusOne q.plusOne
def plusOneTrivIso (X) (e : (ι ⊕ Unit) ≃ κ) : BundleIso ((triv X ι).plusOne) (triv X κ)
theorem coordIncl_mul_conjTranspose_of_bijective (hf : Function.Bijective f) :
    coordIncl f * (coordIncl f)ᴴ = 1

theorem projSetCP_triv : projSetCP (triv X (Fin (d+1))) = Set.univ
noncomputable def projTrivHomeoCP : Proj (triv X (Fin (d + 1))) ≃ₜ X × CP d
theorem projTrivHomeoCP_over_base (z) : (projTrivHomeoCP z).1 = projPi _ z

def sumUnitEquivTwo : (Fin 1 ⊕ Unit) ≃ Fin 2
noncomputable def projPlusOneHomeoCPOne (p) (hp : ∀ x, (p x).trace = 1) (i : ι)
    (hi : ∀ x, p x i i ≠ 0) : Proj p.plusOne ≃ₜ X × CP 1
theorem projPlusOneHomeoCPOne_over_base (p) (hp) (i) (hi) (z) :
    (projPlusOneHomeoCPOne p hp i hi z).1 = projPi p.plusOne z

-- the tautological line is identified too, not only the spaces
def comapIso (f : C(Y, X)) (e : BundleIso p q) : BundleIso (comap f p) (comap f q)
theorem tautLine_eq_comap_cpTaut (p : Bundle X (Fin (d + 1))) :
    tautLine p = comap (tautClassifying p) (cpTaut d)          -- by `rfl`
noncomputable def tautClassifyPlusOne (p) (hp) (i) (hi) : C(Proj p.plusOne, CP 1)
theorem tautClassifyPlusOne_apply (p) (hp) (i) (hi) (z) :
    tautClassifyPlusOne p hp i hi z = (projPlusOneHomeoCPOne p hp i hi z).2
noncomputable def tautLineIsoCPOne (p) (hp) (i) (hi) :
    BundleIso (tautLine p.plusOne) (comap (tautClassifyPlusOne p hp i hi) (cpTaut 1))
```

`projPlusOneHomeoCPOne` alone identifies the space and, by `_over_base`, the map
to `X`.  `tautLineIsoCPOne` adds the third piece of data, the line, so the
identification is one of triples and a consumer needs no separate argument that
the degree-two generator is carried to the degree-two generator.  The chain is
`tautIso` along each of the two bundle isomorphisms, pulled back along the first
`projHomeo` by `comapIso`, then `tautLine_eq_comap_cpTaut` at the trivial
rank-two bundle; every step after the two `tautIso`s is definitional.

A line bundle is trivial as soon as it has a nowhere-vanishing section, and on a
projection-valued map the section is free: the `i`-th **column** of `p x` lies in
the fibre because `p` is idempotent, and it is nonzero exactly where the
diagonal entry is.  So no choice and no local triviality argument is needed;
`lineOf_eq_of_mem_fibre` then says a nonzero vector of a rank-one fibre spans it,
which is what turns the section into an isomorphism.

## NEEDS

Nothing from a peer, and nothing from the roster row is left unstarted.

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
* **`omit … in` goes above the docstring, not below it.**  Between the docstring
  and the `theorem` it fails with `unexpected token 'omit'; expected 'lemma'`,
  once per occurrence.  When an instance is unused throughout a section, the
  cheaper fix is to drop it from the `variable` line: chasing it declaration by
  declaration costs one probe round per wave, because the linter only reports
  the ones it reached.
* **A method in `Bundle.BundleIso` is unreachable by dot notation.**  `BundleIso`
  itself lives in `CharClass`, so `e.projHomeo` on `e : BundleIso p q` looks for
  `CharClass.BundleIso.projHomeo`, which does not exist; and writing
  `BundleIso.projHomeo` inside `namespace Bundle` resolves the same way, because
  `BundleIso` resolves as a *constant* first and its namespace wins.  Only the
  fully-qualified `_root_.….Bundle.BundleIso.projHomeo` works.  Affects
  `projHomeo`, `totalHomeo` and `tautIso`; peers must call them qualified.
* **Transitive reach is not import, and it bites twice.**  `BundleInvariance` is
  not in the import closure of `BundleZeroSection`, so a file importing the
  latter sees none of it.  The symptom is `Unknown constant` on a name that
  visibly exists in the tree.
* **`rw [foo_apply]` rewrites every occurrence of the instantiation it picks.**
  A second `rw [foo_apply]` for the *same* arguments then fails with "did not
  find the pattern"; for *different* arguments it is required.  Both shapes
  occur within three lines of each other in `BundleLineTriv`.
* **A metavariable source type will not unify with a `SetLike` coercion.**
  `cc-projective` hit this with `sInclusion` on an open set: the source type
  stays a metavariable and does not meet a subtype that came from the coercion
  on `Opens`.  Writing the map with its expected type given, as `TopCat.ofHom`
  with the type ascribed, fixes it.  Same shape as the rewrite-order trap: the
  elaborator has no reason to pick the form you meant unless you write it.
* **`open unitInterval` makes `σ` an unusable variable name.**  It is scoped
  notation for the interval's symmetry (`Mathlib/Topology/UnitInterval.lean`),
  so `(σ : ι ⊕ κ ≃ ρ)` fails with `unexpected token 'σ'; expected identifier`,
  eight times over, in a file that otherwise elaborates.  `I` is scoped notation
  in the same namespace.  This lane uses `eqv` for equivalences.
* **The rewrite-order trap has a second form.**  `rw [foo_def, foo_conjTranspose]`
  fails when `foo_def` also rewrites the occurrence under the transpose; put the
  transpose lemma first.  The same shape bit the trace lemma in
  `BundleClassify`.

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
