import GroupApproximation.GGT.DGOTheorem442NearMinimalHyperbolic
import GroupApproximation.GGT.DGOTheorem442StepProjection

/-!
# DGO inequality (41)

Choose one approximate projection to the subgroup orbit for every point,
taking the point itself whenever it already lies in that orbit.  Along an
admissible relative word, consecutive chosen projections are uniformly close
by the one-letter estimate.  For a peripheral letter the only exceptional
case is that the current prefix lies in `H`, and `AvoidsFrom` excludes exactly
that case.

Summing along a word of length at most `n` gives
`dist s (h s) <= C * n`.  The coefficient `alpha = 1 / C` is positive and
gives inequality (41).
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open CosetGraph

universe u v

variable {G : Type u} [Group G] {S : Type v} [PseudoMetricSpace S]
  [MulAction G S]

/-- An approximate projection can be chosen to equal its source whenever the
source already belongs to the subgroup orbit. -/
theorem exists_subgroupProjection_eq_self_of_mem
    (H : Subgroup G) (s : S) (delta : ℝ) (hdeltapos : 0 < delta)
    (a : S) :
    ∃ p : S, IsApproxProjectionTo (subgroupOrbitAt H s) a p delta ∧
      (a ∈ subgroupOrbitAt H s → p = a) := by
  by_cases ha : a ∈ subgroupOrbitAt H s
  · refine ⟨a, ⟨ha, ?_⟩, fun _ ↦ rfl⟩
    intro z _hz
    simp only [dist_self]
    linarith [dist_nonneg (x := a) (y := z)]
  · obtain ⟨p, hp⟩ := exists_isApproxProjectionTo
      (subgroupOrbitAt H s) a ⟨s, 1, H.one_mem, by simp⟩ hdeltapos
    exact ⟨p, hp, fun ha' ↦ (ha ha').elim⟩

/-- A chosen approximate projection to the subgroup orbit, fixed to be the
source point when that point already belongs to the orbit. -/
noncomputable def chosenSubgroupProjection
    (H : Subgroup G) (s : S) (delta : ℝ) (hdeltapos : 0 < delta)
    (a : S) : S :=
  Classical.choose (exists_subgroupProjection_eq_self_of_mem
    H s delta hdeltapos a)

/-- The chosen point is an approximate projection. -/
theorem chosenSubgroupProjection_isApprox
    (H : Subgroup G) (s : S) {delta : ℝ} (hdeltapos : 0 < delta) (a : S) :
    IsApproxProjectionTo (subgroupOrbitAt H s) a
      (chosenSubgroupProjection H s delta hdeltapos a) delta := by
  exact (Classical.choose_spec
    (exists_subgroupProjection_eq_self_of_mem H s delta hdeltapos a)).1

/-- On the subgroup orbit, the chosen projection is the point itself. -/
theorem chosenSubgroupProjection_eq_self
    (H : Subgroup G) (s : S) {delta : ℝ} (hdeltapos : 0 < delta)
    {a : S} (ha : a ∈ subgroupOrbitAt H s) :
    chosenSubgroupProjection H s delta hdeltapos a = a := by
  exact (Classical.choose_spec
    (exists_subgroupProjection_eq_self_of_mem H s delta hdeltapos a)).2 ha

omit [PseudoMetricSpace S] in
/-- Translating the subgroup orbit by `v⁻¹` gives the coset orbit indexed by
`v⁻¹H`. -/
theorem cosetOrbit_inv_eq_image_subgroupOrbit
    (H : Subgroup G) (s : S) (v : G) :
    cosetOrbitAt H s (QuotientGroup.mk v⁻¹) =
      (fun z : S ↦ v⁻¹ • z) '' subgroupOrbitAt H s := by
  have h := cosetOrbitAt_smul H s v⁻¹ (QuotientGroup.mk 1)
  simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    cosetOrbitAt_mk, leftCosetOrbitAt_one] using h

/-- Translating the chosen projections at one group step converts them to the
projection-span coordinates `s` and `x s`. -/
theorem dist_chosenProjection_step_le
    {delta C : ℝ} (hdeltapos : 0 < delta)
    (hiso : IsIsometricAction G S) (H : Subgroup G) (s : S)
    (X : Set G)
    (hbase : ∀ x ∈ X, ∀ Y : G ⧸ H,
      ApproxProjectionSpanLE H s delta Y s (x • s) C)
    (hperipheral : ∀ x ∈ H, ∀ Y : G ⧸ H,
      Y ≠ QuotientGroup.mk 1 →
        ApproxProjectionSpanLE H s delta Y s (x • s) C)
    {v x : G} (hx : x ∈ X ∨ (x ∈ H ∧ v ∉ H)) :
    dist (chosenSubgroupProjection H s delta hdeltapos (v • s))
        (chosenSubgroupProjection H s delta hdeltapos ((v * x) • s)) ≤ C := by
  let p := chosenSubgroupProjection H s delta hdeltapos (v • s)
  let q := chosenSubgroupProjection H s delta hdeltapos ((v * x) • s)
  have hp := chosenSubgroupProjection_isApprox H s hdeltapos (v • s)
  have hq := chosenSubgroupProjection_isApprox H s hdeltapos ((v * x) • s)
  have hpTranslated := isApproxProjectionTo_smul hiso v⁻¹
    (subgroupOrbitAt H s) hp
  have hqTranslated := isApproxProjectionTo_smul hiso v⁻¹
    (subgroupOrbitAt H s) hq
  have horbit := cosetOrbit_inv_eq_image_subgroupOrbit H s v
  have hp' : IsApproxProjectionTo
      (cosetOrbitAt H s (QuotientGroup.mk v⁻¹)) s (v⁻¹ • p) delta := by
    rw [horbit]
    simpa only [p, inv_smul_smul] using hpTranslated
  have hq' : IsApproxProjectionTo
      (cosetOrbitAt H s (QuotientGroup.mk v⁻¹)) (x • s) (v⁻¹ • q) delta := by
    rw [horbit]
    simpa only [q, ← mul_smul, inv_mul_cancel_left] using hqTranslated
  have hspan : ApproxProjectionSpanLE H s delta (QuotientGroup.mk v⁻¹)
      s (x • s) C := by
    rcases hx with hxBase | ⟨hxH, hvH⟩
    · exact hbase x hxBase (QuotientGroup.mk v⁻¹)
    · apply hperipheral x hxH (QuotientGroup.mk v⁻¹)
      intro heq
      have hmem := QuotientGroup.eq.mp heq
      apply hvH
      simpa only [inv_inv, mul_one] using hmem
  have hpq : dist (v⁻¹ • p) (v⁻¹ • q) ≤ C := hspan _ hp' _ hq'
  have hdist : dist p q = dist (v⁻¹ • p) (v⁻¹ • q) :=
    (hiso v⁻¹ p q).symm
  rw [hdist]
  exact hpq

/-- The chosen projections along an admissible relative word have total span
at most `C` times the word length. -/
theorem dist_chosenProjection_word_le
    {delta C : ℝ} (hdeltapos : 0 < delta)
    (hiso : IsIsometricAction G S) (H : Subgroup G) (s : S)
    (X : Set G)
    (hbase : ∀ x ∈ X, ∀ Y : G ⧸ H,
      ApproxProjectionSpanLE H s delta Y s (x • s) C)
    (hperipheral : ∀ x ∈ H, ∀ Y : G ⧸ H,
      Y ≠ QuotientGroup.mk 1 →
        ApproxProjectionSpanLE H s delta Y s (x • s) C) :
    ∀ (w : List (RelLetter G Unit)) (v : G),
      (∀ a ∈ w, match a with
        | RelLetter.base x => x ∈ X
        | RelLetter.comp _ x => x ∈ H) →
      AvoidsFrom (fun _ : Unit ↦ H) () w v →
      dist (chosenSubgroupProjection H s delta hdeltapos (v • s))
          (chosenSubgroupProjection H s delta hdeltapos
            ((v * RelLetter.listVal w) • s)) ≤ C * (w.length : ℝ) := by
  intro w
  induction w with
  | nil =>
      intro v _hlet _hav
      simp only [RelLetter.listVal_nil, mul_one, dist_self, List.length_nil,
        Nat.cast_zero, mul_zero]
      exact le_rfl
  | cons a w ih =>
      intro v hlet hav
      have ha := hlet a (by simp)
      have hw : ∀ b ∈ w, match b with
          | RelLetter.base x => x ∈ X
          | RelLetter.comp _ x => x ∈ H := by
        intro b hb
        exact hlet b (List.mem_cons_of_mem a hb)
      have htail := ih (v * a.val) hw hav.2
      have hstep : dist
          (chosenSubgroupProjection H s delta hdeltapos (v • s))
          (chosenSubgroupProjection H s delta hdeltapos ((v * a.val) • s)) ≤ C := by
        cases a with
        | base x =>
            apply dist_chosenProjection_step_le hdeltapos hiso H s X
              hbase hperipheral
            exact Or.inl ha
        | comp lam x =>
            have hxH : x ∈ H := ha
            have hvH : v ∉ H := by
              intro hv
              exact hav.1 ⟨rfl, hv⟩
            apply dist_chosenProjection_step_le hdeltapos hiso H s X
              hbase hperipheral
            exact Or.inr ⟨hxH, hvH⟩
      have htri := dist_triangle
        (chosenSubgroupProjection H s delta hdeltapos (v • s))
        (chosenSubgroupProjection H s delta hdeltapos ((v * a.val) • s))
        (chosenSubgroupProjection H s delta hdeltapos
          ((v * RelLetter.listVal (a :: w)) • s))
      have hend : v * RelLetter.listVal (a :: w) =
          (v * a.val) * RelLetter.listVal w := by
        simp only [RelLetter.listVal, List.map_cons, List.prod_cons]
        group
      rw [hend] at htri ⊢
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-! ## The relative generating set and inequality (41) -/

/-- The final relative generating set used in the unbounded-orbit branch of
DGO Theorem 4.42. -/
noncomputable def dgo442NearMinimalRelGenSet
    {delta : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) : RelGenSet G Unit :=
  let P := approxCosetEquivariantProjectionSystem
    hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
  nearMinimalRelGenSet hiso H s hdeltapos P.dgo442Graph
    P.dgo442Graph_adj_smul_iff P.dgo442Graph_preconnected

@[simp] theorem dgo442NearMinimalRelGenSet_fam
    {delta : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    (dgo442NearMinimalRelGenSet hdelta hdelta0 hdeltapos hgeo hiso
      H s hqc hsep).fam = fun _ ↦ H :=
  rfl

@[simp] theorem dgo442NearMinimalRelGenSet_base
    {delta : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    (dgo442NearMinimalRelGenSet hdelta hdelta0 hdeltapos hgeo hiso
      H s hqc hsep).base =
      nearMinimalBase H s delta
        (approxCosetEquivariantProjectionSystem
          hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep).dgo442Graph :=
  rfl

/-- **DGO inequality (41).**  The near-minimal relative generating set admits
a positive coefficient `alpha` for which relative radius bounds orbit
displacement. -/
theorem exists_dgo442NearMinimalRelGenSet_orbitLowerBound
    {delta : ℝ} (hdelta : IsHyperbolicSpace delta S)
    (hdelta0 : 0 ≤ delta) (hdeltapos : 0 < delta)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    let D := dgo442NearMinimalRelGenSet hdelta hdelta0 hdeltapos hgeo hiso
      H s hqc hsep
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ (n : ℕ) (h : G), h ∈ D.relBall () n →
        alpha * dist s (h • s) ≤ (n : ℝ) := by
  dsimp only
  let P := approxCosetEquivariantProjectionSystem
    hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
  let D := dgo442NearMinimalRelGenSet hdelta hdelta0 hdeltapos hgeo hiso
    H s hqc hsep
  obtain ⟨C, hC, hbase, hperipheral⟩ :=
    exists_dgo442_letter_projection_bound
      hdelta hdelta0 hdeltapos hgeo hiso H s hqc hsep
  refine ⟨1 / C, one_div_pos.mpr hC, ?_⟩
  intro n h hh
  obtain ⟨hhFam, w, hlet, hval, hav, hlen⟩ :=
    (RelGenSet.mem_relBall.mp hh)
  have hhH : h ∈ H := by
    change h ∈ D.fam () at hhFam
    rw [dgo442NearMinimalRelGenSet_fam] at hhFam
    exact hhFam
  have hletters : ∀ a ∈ w, match a with
      | RelLetter.base x => x ∈ nearMinimalBase H s delta P.dgo442Graph
      | RelLetter.comp _ x => x ∈ H := by
    intro a ha
    have ha' := hlet a ha
    cases a with
    | base x =>
        change x ∈ D.base at ha'
        rw [dgo442NearMinimalRelGenSet_base] at ha'
        exact ha'
    | comp lam x =>
        change x ∈ D.fam lam at ha'
        rw [dgo442NearMinimalRelGenSet_fam] at ha'
        exact ha'
  have hav' : AvoidsFrom (fun _ : Unit ↦ H) () w 1 := by
    change AvoidsFrom D.fam () w 1 at hav
    rw [dgo442NearMinimalRelGenSet_fam] at hav
    exact hav
  have hpath := dist_chosenProjection_word_le hdeltapos hiso H s
    (nearMinimalBase H s delta P.dgo442Graph) hbase hperipheral w 1 hletters hav'
  have hsOrbit : s ∈ subgroupOrbitAt H s := ⟨1, H.one_mem, by simp⟩
  have hhOrbit : h • s ∈ subgroupOrbitAt H s := ⟨h, hhH, rfl⟩
  have hstart : chosenSubgroupProjection H s delta hdeltapos ((1 : G) • s) = s := by
    simpa only [one_smul] using
      chosenSubgroupProjection_eq_self H s hdeltapos hsOrbit
  have hend : chosenSubgroupProjection H s delta hdeltapos
      (((1 : G) * RelLetter.listVal w) • s) = h • s := by
    rw [one_mul, hval]
    exact chosenSubgroupProjection_eq_self H s hdeltapos hhOrbit
  rw [hstart, hend] at hpath
  have hlenR : (w.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlen
  have hdist : dist s (h • s) ≤ C * (n : ℝ) := by
    exact hpath.trans (mul_le_mul_of_nonneg_left hlenR hC.le)
  calc
    (1 / C) * dist s (h • s) = C⁻¹ * dist s (h • s) := by rw [one_div]
    _ ≤ C⁻¹ * (C * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr hC.le)
    _ = (n : ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

end Elementary
end GGT
end GroupApproximation
