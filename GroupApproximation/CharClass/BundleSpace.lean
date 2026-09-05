import GroupApproximation.CharClass.BundleRankOne

/-!
# Complex vector bundles in the projection model, III: the spaces

The four spaces attached to a bundle `p : Bundle X ι`, all as **subtypes of a
product**, so that `TopCat.of` applies to them directly and the vendored
cohomology of `GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree` can be
taken of them with no glue beyond `cc-cohom-api`'s bridging lemmas:

* `totalSet p ⊆ X × (ι → ℂ)`, the pairs `(x, v)` with `p x *ᵥ v = v`;
* `sphereSet p`, the unit vectors inside it;
* `puncturedSet p`, the nonzero vectors inside it;
* `projSet p ⊆ X × Matrix ι ι ℂ`, the pairs `(x, q)` with `q` a rank-one
  projection absorbed by `p x` -- the projective bundle `P(p)`.

`projSet` is written with the *same four equations* that cut out
`STW59.cpSet d` (self-adjoint, idempotent, trace one) plus the absorption
`p x · q = q`, so that for `ι = Fin (d+1)` the homeomorphism onto
`{z : X × CP d | p z.1 * z.2 = z.2}` is bookkeeping (`projHomeoCP`).  There is
no second model of complex projective space in this development.

The tautological line over `P(p)` is `Subtype.val` composed with the second
projection: literally the matrix carried by the point (`tautLine`).

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section Spaces

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-! ### The total space, the sphere bundle and the complement of the zero section -/

/-- **The total space** `E(p) = {(x, v) : p x · v = v}`. -/
def totalSet (p : Bundle X ι) : Set (X × (ι → ℂ)) := {v | p v.1 *ᵥ v.2 = v.2}

/-- The total space as a topological space. -/
abbrev Total (p : Bundle X ι) : Type := ↥(totalSet p)

theorem mem_totalSet_iff {p : Bundle X ι} {v : X × (ι → ℂ)} :
    v ∈ totalSet p ↔ p v.1 *ᵥ v.2 = v.2 := Iff.rfl

theorem continuous_fibreMap (p : Bundle X ι) :
    Continuous fun v : X × (ι → ℂ) => p v.1 *ᵥ v.2 :=
  (p.continuous.comp continuous_fst).matrix_mulVec continuous_snd

theorem isClosed_totalSet (p : Bundle X ι) : IsClosed (totalSet p) :=
  isClosed_eq (continuous_fibreMap p) continuous_snd

/-- **The sphere bundle** `S(p)`. -/
def sphereSet (p : Bundle X ι) : Set (X × (ι → ℂ)) :=
  {v | v ∈ totalSet p ∧ eucNormSq v.2 = 1}

/-- The sphere bundle as a topological space. -/
abbrev Sphere (p : Bundle X ι) : Type := ↥(sphereSet p)

theorem mem_sphereSet_iff {p : Bundle X ι} {v : X × (ι → ℂ)} :
    v ∈ sphereSet p ↔ p v.1 *ᵥ v.2 = v.2 ∧ eucNormSq v.2 = 1 := Iff.rfl

theorem sphereSet_subset_totalSet (p : Bundle X ι) : sphereSet p ⊆ totalSet p :=
  fun _ hv => hv.1

theorem isClosed_sphereSet (p : Bundle X ι) : IsClosed (sphereSet p) := by
  have h : sphereSet p = totalSet p ∩ {v : X × (ι → ℂ) | eucNormSq v.2 = 1} := rfl
  rw [h]
  exact (isClosed_totalSet p).inter
    (isClosed_eq (continuous_eucNormSq.comp continuous_snd) continuous_const)

theorem isCompact_sphereSet [CompactSpace X] (p : Bundle X ι) : IsCompact (sphereSet p) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ.prod (isCompact_unitVectors ι)) (isClosed_sphereSet p) ?_
  rintro ⟨x, v⟩ hv
  exact ⟨Set.mem_univ x, hv.2⟩

instance Sphere.instCompactSpace [CompactSpace X] (p : Bundle X ι) : CompactSpace (Sphere p) :=
  isCompact_iff_compactSpace.mp (isCompact_sphereSet p)

/-- **The complement of the zero section** `E(p) ∖ 0`. -/
def puncturedSet (p : Bundle X ι) : Set (X × (ι → ℂ)) :=
  {v | v ∈ totalSet p ∧ v.2 ≠ 0}

/-- The complement of the zero section as a topological space. -/
abbrev Punctured (p : Bundle X ι) : Type := ↥(puncturedSet p)

theorem mem_puncturedSet_iff {p : Bundle X ι} {v : X × (ι → ℂ)} :
    v ∈ puncturedSet p ↔ p v.1 *ᵥ v.2 = v.2 ∧ v.2 ≠ 0 := Iff.rfl

theorem puncturedSet_subset_totalSet (p : Bundle X ι) : puncturedSet p ⊆ totalSet p :=
  fun _ hv => hv.1

theorem ne_zero_of_eucNormSq_eq_one {v : ι → ℂ} (hv : eucNormSq v = 1) : v ≠ 0 := by
  intro h
  rw [h] at hv
  simp [eucNormSq] at hv

theorem sphereSet_subset_puncturedSet (p : Bundle X ι) : sphereSet p ⊆ puncturedSet p :=
  fun _ hv => ⟨hv.1, ne_zero_of_eucNormSq_eq_one hv.2⟩

/-! ### The maps between them -/

/-- The bundle projection `E(p) → X`. -/
def totalPi (p : Bundle X ι) : C(Total p, X) :=
  ⟨fun v => (v : X × (ι → ℂ)).1, continuous_fst.comp continuous_subtype_val⟩

@[simp]
theorem totalPi_apply (p : Bundle X ι) (v : Total p) :
    totalPi p v = (v : X × (ι → ℂ)).1 := rfl

/-- The zero section `X → E(p)`. -/
def zeroSection (p : Bundle X ι) : C(X, Total p) :=
  ⟨fun x => ⟨(x, 0), by
      show p x *ᵥ (0 : ι → ℂ) = 0
      exact Matrix.mulVec_zero _⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

@[simp]
theorem zeroSection_apply (p : Bundle X ι) (x : X) :
    (zeroSection p x : X × (ι → ℂ)) = (x, 0) := rfl

theorem totalPi_comp_zeroSection (p : Bundle X ι) :
    (totalPi p).comp (zeroSection p) = ContinuousMap.id X := rfl

/-- The inclusion of the sphere bundle into the punctured total space. -/
def sphereToPunctured (p : Bundle X ι) : C(Sphere p, Punctured p) :=
  ⟨Set.inclusion (sphereSet_subset_puncturedSet p), continuous_inclusion _⟩

/-- The inclusion of the punctured total space into the total space. -/
def puncturedToTotal (p : Bundle X ι) : C(Punctured p, Total p) :=
  ⟨Set.inclusion (puncturedSet_subset_totalSet p), continuous_inclusion _⟩

/-- The punctured total space is an open subspace of the total space. -/
theorem isOpen_puncturedSet_in_total (p : Bundle X ι) :
    IsOpen {v : Total p | (v : X × (ι → ℂ)).2 ≠ 0} := by
  refine IsOpen.preimage (continuous_snd.comp continuous_subtype_val) ?_
  exact isOpen_compl_singleton

/-! ### The projective bundle -/

/-- **The projective bundle** `P(p) = {(x, q) : q a rank-one projection, q ≤ p x}`.

The three equations on `q` are literally the three equations of
`STW59.cpSet`, and the fourth is the absorption `p x · q = q`. -/
def projSet (p : Bundle X ι) : Set (X × Matrix ι ι ℂ) :=
  {z | z.2ᴴ = z.2 ∧ z.2 * z.2 = z.2 ∧ z.2.trace = 1 ∧ p z.1 * z.2 = z.2}

/-- The projective bundle as a topological space. -/
abbrev Proj (p : Bundle X ι) : Type := ↥(projSet p)

theorem mem_projSet_iff {p : Bundle X ι} {z : X × Matrix ι ι ℂ} :
    z ∈ projSet p ↔ z.2ᴴ = z.2 ∧ z.2 * z.2 = z.2 ∧ z.2.trace = 1 ∧ p z.1 * z.2 = z.2 :=
  Iff.rfl

theorem isStarProjection_of_mem_projSet {p : Bundle X ι} {z : X × Matrix ι ι ℂ}
    (hz : z ∈ projSet p) : IsStarProjection z.2 :=
  isStarProjection_matrix_iff.mpr ⟨hz.1, hz.2.1⟩

theorem trace_of_mem_projSet {p : Bundle X ι} {z : X × Matrix ι ι ℂ}
    (hz : z ∈ projSet p) : z.2.trace = 1 := hz.2.2.1

theorem absorb_of_mem_projSet {p : Bundle X ι} {z : X × Matrix ι ι ℂ}
    (hz : z ∈ projSet p) : p z.1 * z.2 = z.2 := hz.2.2.2

/-- The membership criterion actually used: a rank-one projection absorbed by
`p x` is a point of the fibre. -/
theorem mem_projSet_of_lineOf {p : Bundle X ι} {x : X} {u : ι → ℂ} (hu : u ≠ 0)
    (hfix : p x *ᵥ u = u) : ((x, lineOf u) : X × Matrix ι ι ℂ) ∈ projSet p :=
  ⟨conjTranspose_eq_of_isStarProjection (isStarProjection_lineOf hu),
    (isStarProjection_lineOf hu).isIdempotentElem.eq, trace_lineOf hu, mul_lineOf hfix⟩

theorem isClosed_projSet (p : Bundle X ι) : IsClosed (projSet p) := by
  have hsnd : Continuous fun z : X × Matrix ι ι ℂ => z.2 := continuous_snd
  have h1 : IsClosed {z : X × Matrix ι ι ℂ | z.2ᴴ = z.2} :=
    isClosed_eq hsnd.matrix_conjTranspose hsnd
  have h2 : IsClosed {z : X × Matrix ι ι ℂ | z.2 * z.2 = z.2} :=
    isClosed_eq (hsnd.matrix_mul hsnd) hsnd
  have h3 : IsClosed {z : X × Matrix ι ι ℂ | z.2.trace = 1} :=
    isClosed_eq hsnd.matrix_trace continuous_const
  have h4 : IsClosed {z : X × Matrix ι ι ℂ | p z.1 * z.2 = z.2} :=
    isClosed_eq ((p.continuous.comp continuous_fst).matrix_mul hsnd) hsnd
  have hset : projSet p = {z : X × Matrix ι ι ℂ | z.2ᴴ = z.2} ∩
      ({z : X × Matrix ι ι ℂ | z.2 * z.2 = z.2} ∩
        ({z : X × Matrix ι ι ℂ | z.2.trace = 1} ∩
          {z : X × Matrix ι ι ℂ | p z.1 * z.2 = z.2})) := rfl
  rw [hset]
  exact h1.inter (h2.inter (h3.inter h4))

theorem isCompact_projSet [CompactSpace X] (p : Bundle X ι) : IsCompact (projSet p) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ.prod (IsCompact.matrix (isCompact_closedBall (0 : ℂ) 1)))
    (isClosed_projSet p) ?_
  rintro ⟨x, q⟩ hq
  refine ⟨Set.mem_univ x, ?_⟩
  intro i j
  simpa [Metric.mem_closedBall, dist_zero_right] using
    proj_norm_entry_le_one (isStarProjection_of_mem_projSet hq) (trace_of_mem_projSet hq) i j

instance Proj.instCompactSpace [CompactSpace X] (p : Bundle X ι) : CompactSpace (Proj p) :=
  isCompact_iff_compactSpace.mp (isCompact_projSet p)

/-- The projection `P(p) → X`. -/
def projPi (p : Bundle X ι) : C(Proj p, X) :=
  ⟨fun z => (z : X × Matrix ι ι ℂ).1, continuous_fst.comp continuous_subtype_val⟩

@[simp]
theorem projPi_apply (p : Bundle X ι) (z : Proj p) :
    projPi p z = (z : X × Matrix ι ι ℂ).1 := rfl

/-- **The tautological line bundle** over `P(p)`: the matrix carried by the
point.  In this model the tautological line's projection is `Subtype.val`
composed with the second projection -- nothing is constructed. -/
def tautLine (p : Bundle X ι) : Bundle (Proj p) ι where
  toFun z := (z : X × Matrix ι ι ℂ).2
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  isStarProjection_toFun z := isStarProjection_of_mem_projSet z.2

@[simp]
theorem tautLine_apply (p : Bundle X ι) (z : Proj p) :
    tautLine p z = (z : X × Matrix ι ι ℂ).2 := rfl

theorem trace_tautLine (p : Bundle X ι) (z : Proj p) : (tautLine p z).trace = 1 :=
  trace_of_mem_projSet z.2

/-- The tautological line sits inside the pullback of `p`. -/
theorem tautLine_le (p : Bundle X ι) (z : Proj p) :
    comap (projPi p) p z * tautLine p z = tautLine p z :=
  absorb_of_mem_projSet z.2

end Spaces

/-! ### The comparison with `STW59.CP` -/

section CP

variable {X : Type} [TopologicalSpace X] {d : ℕ}

/-- The projective bundle, presented inside `X × CP d`. -/
def projSetCP (p : Bundle X (Fin (d + 1))) : Set (X × CP d) :=
  {z | p z.1 * (z.2 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = (z.2 : Matrix _ _ ℂ)}

/-- **`P(p)` is a subspace of `X × ℂP^{K-1}`**, exactly as the campaign's design
note asks.  The homeomorphism is bookkeeping: the four equations cutting out
`projSet` are the three cutting out `cpSet` plus the absorption. -/
def projHomeoCP (p : Bundle X (Fin (d + 1))) : Proj p ≃ₜ ↥(projSetCP p) where
  toFun z := ⟨((z : X × Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).1,
      ⟨(z : X × Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).2, z.2.1, z.2.2.1, z.2.2.2.1⟩),
    z.2.2.2.2⟩
  invFun w := ⟨((w : X × CP d).1, ((w : X × CP d).2 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)),
    (w : X × CP d).2.2.1, (w : X × CP d).2.2.2.1, (w : X × CP d).2.2.2.2, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_fst.comp continuous_subtype_val).prodMk
      (((continuous_snd.comp continuous_subtype_val)).subtype_mk _))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

/-- The classifying map of the tautological line: `P(p) → ℂP^{K-1}`. -/
def tautClassifying (p : Bundle X (Fin (d + 1))) : C(Proj p, CP d) :=
  ⟨fun z => ⟨(z : X × Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).2, z.2.1, z.2.2.1, z.2.2.2.1⟩,
    ((continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

@[simp]
theorem tautClassifying_apply (p : Bundle X (Fin (d + 1))) (z : Proj p) :
    (tautClassifying p z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
      = (z : X × Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).2 := rfl

end CP

end Bundle

/-! ### The bundles of the campaign

`Analysis/LIXBlockProjections.lean` is owned by lane `cs-stages` and is not
imported here; the two bundles below are stated over the definitions that file's
abbreviations unfold to, so the two presentations agree by `rfl`. -/

section Campaign

open Bundle

/-- The tautological line bundle of `ℂP^d`, as a `Bundle`.  Its projection is
`Subtype.val`: this is `STW59.taut`. -/
def cpTaut (d : ℕ) : Bundle (CP d) (Fin (d + 1)) where
  toFun z := (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
  continuous_toFun := continuous_subtype_val
  isStarProjection_toFun z := isStarProjection_taut d z

@[simp]
theorem cpTaut_apply (d : ℕ) (z : CP d) :
    cpTaut d z = (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := rfl

theorem trace_cpTaut (d : ℕ) (z : CP d) : (cpTaut d z).trace = 1 := trace_taut d z

/-- The Hopf line bundle over `S⁵ = STW59.unitVectors (Fin 3)`: the line spanned
by the point.  (`Analysis/LIXBlockProjections.lean` calls this `hopfProj`.) -/
def hopfLine : Bundle ↥(unitVectors (Fin 3)) (Fin 3) where
  toFun x := rankOneProj (x : Fin 3 → ℂ)
  continuous_toFun := continuous_rankOneProj'.comp continuous_subtype_val
  isStarProjection_toFun x := isStarProjection_rankOneProj x.2

@[simp]
theorem hopfLine_apply (x : ↥(unitVectors (Fin 3))) :
    hopfLine x = rankOneProj (x : Fin 3 → ℂ) := rfl

theorem trace_hopfLine (x : ↥(unitVectors (Fin 3))) : (hopfLine x).trace = 1 :=
  trace_rankOneProj x.2

/-- The rank-two bundle `F = 1₃ - x xᴴ` over `S⁵`, the one the LIX obstruction is
about.  (`Analysis/LIXBlockProjections.lean` calls this `Fproj`.) -/
def hopfPerp : Bundle ↥(unitVectors (Fin 3)) (Fin 3) where
  toFun x := 1 - rankOneProj (x : Fin 3 → ℂ)
  continuous_toFun := continuous_const.sub (continuous_rankOneProj'.comp continuous_subtype_val)
  isStarProjection_toFun x := (isStarProjection_rankOneProj x.2).one_sub

@[simp]
theorem hopfPerp_apply (x : ↥(unitVectors (Fin 3))) :
    hopfPerp x = 1 - rankOneProj (x : Fin 3 → ℂ) := rfl

end Campaign

end CharClass
end GroupApproximation
