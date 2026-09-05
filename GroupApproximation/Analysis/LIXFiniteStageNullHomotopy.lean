import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Finite-stage detection of a null-homotopy

Let `B` be a unital C⋆-algebra written as the closure of an increasing union of
unital C⋆-subalgebras `B₀ ⊆ B₁ ⊆ ⋯`.  A unitary of one stage `B_k` may become
null-homotopic in `B` for a reason that has nothing to do with any stage: the
path is only required to exist in the limit.  The lemma proved here says this
does not happen — a null-homotopy in `B` of a unitary of `B_k` can always be
replaced by a null-homotopy inside a *single later stage* `B_j`.

This is the step that stops finite-stage nontriviality from being silently
substituted for persistence in the limit.  It is used for STW Problem LIX
("are all unital simple C⋆-algebras `K₁`-injective?") in exactly that role:
the candidate unitary is shown non-null-homotopic at every stage of an
inductive system, and this lemma converts that into non-null-homotopy in the
limit.  Nothing below refers to that system; the statement is unconditional and
is about an arbitrary increasing union.

## The statement

Stages are ⋆-subalgebras `S : ι → StarSubalgebra ℂ B` indexed by a
`SemilatticeSup`, each *closed* (so each is itself a C⋆-algebra), monotone, and
with dense union.  Null-homotopy inside a stage is `JoinedIn (unitaryIn (S j))`
— a path of unitaries of `B` all of whose values lie in `S j`, which is the
same thing as a path in the unitary group `U(S j)` (`joined_subUnitary_of_joinedIn`
records the translation).  The conclusion is

    exists_ge_joinedIn_one_of_joined :
      (a : B) ∈ S k → Joined 1 a → ∃ j, k ≤ j ∧ JoinedIn (unitaryIn (S j)) 1 a

with the trivial converse `Joined.of_joinedIn_unitaryIn`.

## The proof

The manuscript's argument partitions the path finely, approximates each node
inside a common stage, and polar-decomposes each approximant back into the
unitary group.  Formalized directly, the polar decomposition is a substantial
continuous-functional-calculus computation and the partition is a fussy finite
induction.

Both are avoidable.  Mathlib's `Unitary.mem_pathComponentOne_iff` already says
that a null-homotopic unitary is a *finite product of exponentials*
`exp (i x₁) ⋯ exp (i x_n)` with `x_m` selfadjoint — that is the partition
argument, done once and for all.  An exponential of a selfadjoint element is
unitary on the nose, so approximating each `x_m` by a selfadjoint element of a
stage (`realPart` of a dense approximant) produces a unitary of that stage
*without any polar decomposition*: the exponential does the unitarizing.
Continuity of `selfAdjoint.expUnitary` turns closeness of the exponents into
closeness of the unitaries, and a closed subalgebra contains the exponential of
each of its elements because it contains every partial sum of the exponential
series (`exp_mem_of_isClosed`).

The resulting product `w` lies in a single stage, is null-homotopic there, and
is within `2` of `a`.  Since `a` also lies in that stage, Mathlib's
`Unitary.joined` — two unitaries at distance `< 2` are joined by a path, via
the principal logarithm supplied by the continuous functional calculus — joins
`a` to `w` *inside that stage*, which is the crux of the manuscript's proof and
the one place where the C⋆-algebra structure of the stage is used.
-/

namespace GroupApproximation

namespace LIX

open scoped Pointwise

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-! ### Unitaries lying in a ⋆-subalgebra -/

/-- The unitaries of `B` whose underlying element lies in the ⋆-subalgebra `S`.  When `S` is
closed this is the unitary group `U(S)`, viewed inside `U(B)`; see `subUnitary` and
`ofSubUnitary` for the translation. -/
def unitaryIn (S : StarSubalgebra ℂ B) : Set (unitary B) := {u | (u : B) ∈ S}

@[simp]
theorem mem_unitaryIn {S : StarSubalgebra ℂ B} {u : unitary B} :
    u ∈ unitaryIn S ↔ (u : B) ∈ S :=
  Iff.rfl

theorem one_mem_unitaryIn (S : StarSubalgebra ℂ B) : (1 : unitary B) ∈ unitaryIn S :=
  one_mem S

theorem unitaryIn_mul_subset (S : StarSubalgebra ℂ B) :
    unitaryIn S * unitaryIn S ⊆ unitaryIn S := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  exact mul_mem hu hv

theorem unitaryIn_mono {S T : StarSubalgebra ℂ B} (h : S ≤ T) : unitaryIn S ⊆ unitaryIn T :=
  fun _ hu => h hu

/-- A unitary of `B` lying in `S` is a unitary of `S`. -/
def subUnitary {S : StarSubalgebra ℂ B} (u : unitary B) (hu : (u : B) ∈ S) : unitary S :=
  ⟨⟨(u : B), hu⟩, Subtype.ext (Unitary.star_mul_self_of_mem u.2),
    Subtype.ext (Unitary.mul_star_self_of_mem u.2)⟩

@[simp]
theorem coe_subUnitary {S : StarSubalgebra ℂ B} (u : unitary B) (hu : (u : B) ∈ S) :
    ((subUnitary u hu : S) : B) = (u : B) :=
  rfl

/-- A unitary of the ⋆-subalgebra `S` is a unitary of `B`. -/
def ofSubUnitary {S : StarSubalgebra ℂ B} (w : unitary S) : unitary B :=
  ⟨((w : S) : B),
    congrArg (fun z : S => (z : B)) (Unitary.star_mul_self_of_mem w.2),
    congrArg (fun z : S => (z : B)) (Unitary.mul_star_self_of_mem w.2)⟩

@[simp]
theorem coe_ofSubUnitary {S : StarSubalgebra ℂ B} (w : unitary S) :
    ((ofSubUnitary w : unitary B) : B) = ((w : S) : B) :=
  rfl

theorem continuous_ofSubUnitary {S : StarSubalgebra ℂ B} :
    Continuous (ofSubUnitary : unitary S → unitary B) :=
  Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

theorem ofSubUnitary_subUnitary {S : StarSubalgebra ℂ B} (u : unitary B) (hu : (u : B) ∈ S) :
    ofSubUnitary (subUnitary u hu) = u :=
  Subtype.ext rfl

/-! ### Closed ⋆-subalgebras absorb real scalars and exponentials -/

theorem real_smul_mem {S : StarSubalgebra ℂ B} {y : B} (hy : y ∈ S) (r : ℝ) : r • y ∈ S := by
  simpa using S.smul_mem hy (r : ℂ)

/-- A closed ⋆-subalgebra contains the exponential of each of its elements: every partial sum
of the exponential series lies in the subalgebra, and the series converges. -/
theorem exp_mem_of_isClosed {S : StarSubalgebra ℂ B} (hS : IsClosed (S : Set B))
    {x : B} (hx : x ∈ S) : NormedSpace.exp x ∈ S := by
  refine hS.mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x).tendsto_sum_nat
    (Filter.Eventually.of_forall fun n => ?_)
  exact SetLike.mem_coe.mpr (sum_mem fun i _ => S.smul_mem (pow_mem hx i) _)

/-! ### Null-homotopy inside a stage -/

/-- Inside a *closed* ⋆-subalgebra containing a selfadjoint element `x`, the exponential unitary
`exp (i x)` is joined to `1` by the path `t ↦ exp (i t x)`, which never leaves the subalgebra. -/
theorem joinedIn_unitaryIn_one_expUnitary {S : StarSubalgebra ℂ B} (hS : IsClosed (S : Set B))
    {x : selfAdjoint B} (hx : (x : B) ∈ S) :
    JoinedIn (unitaryIn S) 1 (selfAdjoint.expUnitary x) := by
  refine ⟨selfAdjoint.expUnitaryPathToOne x, fun t => ?_⟩
  show ((selfAdjoint.expUnitary ((t : ℝ) • x) : unitary B) : B) ∈ S
  rw [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul]
  exact exp_mem_of_isClosed hS (S.smul_mem (real_smul_mem hx _) Complex.I)

/-- **The local step.** Two unitaries of `B` lying in a closed ⋆-subalgebra `S` and at distance
less than `2` are joined by a path *inside* `S`.  This is the manuscript's
"the spectrum of `q_{ν-1}^* q_ν` avoids `-1`, so the principal logarithm supplies a path":
Mathlib's `Unitary.joined`, applied in the C⋆-algebra `S`. -/
theorem joinedIn_unitaryIn_of_norm_sub_lt_two {S : StarSubalgebra ℂ B}
    (hS : IsClosed (S : Set B)) {u v : unitary B} (hu : (u : B) ∈ S) (hv : (v : B) ∈ S)
    (h : ‖(u : B) - (v : B)‖ < 2) :
    JoinedIn (unitaryIn S) v u := by
  haveI : IsClosed (S : Set B) := hS
  obtain ⟨γ⟩ := Unitary.joined (subUnitary v hv) (subUnitary u hu) (by simpa using h)
  refine ⟨(γ.map continuous_ofSubUnitary).cast
      (ofSubUnitary_subUnitary v hv).symm (ofSubUnitary_subUnitary u hu).symm, fun t => ?_⟩
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, mem_unitaryIn, coe_ofSubUnitary]
  exact (γ t).1.2

/-- Null-homotopy inside a stage implies null-homotopy in `B`; the whole point of the main
theorem below is the converse. -/
theorem Joined.of_joinedIn_unitaryIn {S : StarSubalgebra ℂ B} {u : unitary B}
    (h : JoinedIn (unitaryIn S) 1 u) : Joined 1 u :=
  h.joined

/-- Null-homotopy inside `S`, restated in the unitary group of `S` itself: this is the literal
statement "`u ∈ U₀(S)`". -/
theorem joined_subUnitary_of_joinedIn {S : StarSubalgebra ℂ B} {u : unitary B}
    (hu : (u : B) ∈ S) (h : JoinedIn (unitaryIn S) 1 u) :
    Joined (1 : unitary S) (subUnitary u hu) := by
  obtain ⟨γ⟩ := h.joined_subtype
  have hcont : Continuous
      (fun w : unitaryIn S => subUnitary (w : unitary B) w.2) :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _
  exact ⟨(γ.map hcont).cast (Subtype.ext (Subtype.ext rfl)) rfl⟩

/-! ### Approximation by unitaries of a stage -/

variable {ι : Type*} [SemilatticeSup ι] {S : ι → StarSubalgebra ℂ B}

/-- A selfadjoint element of `B` is approximated, to any accuracy, by a selfadjoint element of an
arbitrarily late stage: approximate it by any element of the dense union, and take the real part,
which moves nothing further away. -/
theorem exists_ge_selfAdjoint_mem (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    (k : ι) (x : selfAdjoint B) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, k ≤ j ∧ ∃ y : selfAdjoint B, (y : B) ∈ S j ∧ ‖(y : B) - (x : B)‖ < ε := by
  obtain ⟨z, hz₁, hz₂⟩ := Metric.dense_iff.mp hdense (x : B) ε hε
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz₂
  have hzj : z ∈ S (k ⊔ i) := hmono le_sup_right hzi
  refine ⟨k ⊔ i, le_sup_left, realPart z, ?_, ?_⟩
  · rw [realPart_apply_coe]
    exact real_smul_mem (add_mem hzj (star_mem hzj)) _
  · have hsub : ((realPart (z - (x : B)) : selfAdjoint B) : B)
        = (realPart z : B) - (x : B) := by
      rw [map_sub]
      simp [x.2.coe_realPart]
    rw [← hsub, ← AddSubgroupClass.coe_norm]
    refine lt_of_le_of_lt (realPart.norm_le _) ?_
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hz₁

/-- A finite product of exponential unitaries of `B` is approximated, to any accuracy, by a
unitary of an arbitrarily late stage which is null-homotopic *inside* that stage. -/
theorem exists_ge_joinedIn_prod (hclosed : ∀ i, IsClosed (S i : Set B)) (hmono : Monotone S)
    (hdense : Dense (⋃ i, (S i : Set B))) (l : List (selfAdjoint B)) :
    ∀ (k : ι) (ε : ℝ), 0 < ε → ∃ j, k ≤ j ∧ ∃ w : unitary B,
      JoinedIn (unitaryIn (S j)) 1 w ∧
        ‖(w : B) - (((l.map selfAdjoint.expUnitary).prod : unitary B) : B)‖ < ε := by
  induction l with
  | nil =>
    intro k ε hε
    refine ⟨k, le_rfl, 1, JoinedIn.refl (one_mem_unitaryIn _), ?_⟩
    simpa using hε
  | cons x xs ih =>
    intro k ε hε
    obtain ⟨j₀, hkj₀, w₀, hw₀, hw₀ε⟩ := ih k (ε / 2) (by linarith)
    obtain ⟨δ, hδ, hδ'⟩ :=
      Metric.continuous_iff.mp (selfAdjoint.continuous_expUnitary (A := B)) x (ε / 2) (by linarith)
    obtain ⟨j, hj₀j, y, hyS, hy⟩ := exists_ge_selfAdjoint_mem hmono hdense j₀ x hδ
    have hdist : dist y x < δ := by
      rw [dist_eq_norm, AddSubgroupClass.coe_norm]
      simpa using hy
    have hyx : ‖((selfAdjoint.expUnitary y : unitary B) : B)
        - ((selfAdjoint.expUnitary x : unitary B) : B)‖ < ε / 2 := by
      have := hδ' y hdist
      rwa [Subtype.dist_eq, dist_eq_norm] at this
    refine ⟨j, hkj₀.trans hj₀j, selfAdjoint.expUnitary y * w₀, ?_, ?_⟩
    · have h1 : JoinedIn (unitaryIn (S j)) 1 (selfAdjoint.expUnitary y) :=
        joinedIn_unitaryIn_one_expUnitary (hclosed j) hyS
      have h2 : JoinedIn (unitaryIn (S j)) 1 w₀ :=
        hw₀.mono (unitaryIn_mono (hmono hj₀j))
      simpa using (h1.mul h2).mono (unitaryIn_mul_subset (S j))
    · rw [List.map_cons, List.prod_cons]
      have hkey : ((selfAdjoint.expUnitary y * w₀ : unitary B) : B)
            - ((selfAdjoint.expUnitary x * (xs.map selfAdjoint.expUnitary).prod :
                unitary B) : B)
          = ((selfAdjoint.expUnitary y : unitary B) : B)
              * (((w₀ : unitary B) : B)
                  - ((((xs.map selfAdjoint.expUnitary).prod : unitary B) : B)))
            + (((selfAdjoint.expUnitary y : unitary B) : B)
                - ((selfAdjoint.expUnitary x : unitary B) : B))
              * ((((xs.map selfAdjoint.expUnitary).prod : unitary B) : B)) := by
        push_cast
        ring
      rw [hkey]
      refine lt_of_le_of_lt (norm_add_le _ _) ?_
      rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary]
      linarith

/-! ### Lemma 7 -/

/-- **Finite-stage detection of a null-homotopy** (manuscript Lemma 7).

Let `B` be a unital C⋆-algebra which is the closure of the increasing union of a family of
closed unital ⋆-subalgebras `S i`.  If a unitary `a` of `B` lying in the stage `S k` is
null-homotopic in `U(B)`, then it is already null-homotopic in `U(S j)` for some later stage
`j ≥ k`.

Equivalently: `U₀(B) ∩ U(S k) = ⋃_{j ≥ k} U₀(S j) ∩ U(S k)`, the inclusion `⊇` being
`Joined.of_joinedIn_unitaryIn`. -/
theorem exists_ge_joinedIn_one_of_joined (hclosed : ∀ i, IsClosed (S i : Set B))
    (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    {k : ι} {a : unitary B} (hak : (a : B) ∈ S k) (ha : Joined 1 a) :
    ∃ j, k ≤ j ∧ JoinedIn (unitaryIn (S j)) 1 a := by
  obtain ⟨l, hl⟩ := Unitary.mem_pathComponentOne_iff.mp (mem_pathComponent_iff.mpr ha)
  obtain ⟨j, hkj, w, hw, hwε⟩ :=
    exists_ge_joinedIn_prod hclosed hmono hdense l k 2 (by norm_num)
  rw [hl] at hwε
  refine ⟨j, hkj, hw.trans ?_⟩
  refine joinedIn_unitaryIn_of_norm_sub_lt_two (hclosed j) (hmono hkj hak) hw.target_mem ?_
  rwa [norm_sub_rev]

/-- Lemma 7 in the form "`a ∈ U₀(B)` and `a ∈ U(S k)` imply `a ∈ U₀(S j)` for some `j ≥ k`",
with `U₀(S j)` read literally as the path component of `1` in the unitary group of the
C⋆-algebra `S j`. -/
theorem exists_ge_joined_one_subUnitary (hclosed : ∀ i, IsClosed (S i : Set B))
    (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    {k : ι} {a : unitary B} (hak : (a : B) ∈ S k) (ha : Joined 1 a) :
    ∃ j, ∃ _ : k ≤ j, ∃ h : (a : B) ∈ S j, Joined (1 : unitary (S j)) (subUnitary a h) := by
  obtain ⟨j, hkj, hj⟩ := exists_ge_joinedIn_one_of_joined hclosed hmono hdense hak ha
  exact ⟨j, hkj, hmono hkj hak, joined_subUnitary_of_joinedIn _ hj⟩

end

end LIX

end GroupApproximation
