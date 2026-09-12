import GroupApproximation.GGT.SystolicDisc
import GroupApproximation.GGT.VanKampen.TypedTriangularDiscCounts

/-!
# Counting a triangulated disc

HC11 and HC12 of the minimal-disc layer (`GGT/SystolicDisc.lean`).

* `TriangulatedDisc.exists_typedCounts` (HC11): a disc in a triangle complex whose
  triangles carry three distinct vertex types, with every interior vertex of degree at
  least `6` (type `0`) or `8` (types `1`, `2`), supplies the record
  `GGT.VanKampen.TypedTriangularDiscCounts`, hence `F + 12 ≤ 6B`.  The angle bound
  `24 I ≤ 10 F` counts corners: a corner at a vertex of type `0` weighs `4`, the others `3`,
  so each triangle carries `10` and each interior vertex at least `24`.
* `TriangulatedDisc.abs_boundarySum_le` (HC12): an antisymmetric function on pairs of
  vertices whose sum around every triangle of `X` is at most `C₀` has boundary sum at most
  `C₀ F`.  The sum over all darts vanishes, since reversal negates each term; grouping the
  darts by faces, the outer face gives the boundary sum and each inner face a triangle
  sum.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route (hyperbolicity of `GHB(7)`); certifies no manuscript step on its
own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen

universe u

variable {V : Type u}

/-- The link bound of a vertex of type `τ x`: `6` at type `0`, `8` otherwise. -/
def typedGirth (τ : V → Fin 3) (x : V) : ℕ := if τ x = 0 then 6 else 8

/-- The corner weight in units of `π/12`: `4` at type `0`, `3` otherwise. -/
def cornerWeight (τ : V → Fin 3) (x : V) : ℕ := if τ x = 0 then 4 else 3

theorem cornerWeight_add (τ : V → Fin 3) {x y z : V}
    (hτ : τ x ≠ τ y ∧ τ y ≠ τ z ∧ τ x ≠ τ z) :
    cornerWeight τ x + cornerWeight τ y + cornerWeight τ z = 10 := by
  have key : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c →
      (if a = 0 then 4 else 3) + (if b = 0 then 4 else 3) + (if c = 0 then 4 else 3) = 10 := by
    decide
  exact key _ _ _ hτ.1 hτ.2.1 hτ.2.2

theorem twentyFour_le_mul_cornerWeight (τ : V → Fin 3) {x : V} {m : ℕ}
    (h : typedGirth τ x ≤ m) : 24 ≤ m * cornerWeight τ x := by
  unfold typedGirth at h
  unfold cornerWeight
  by_cases hτ : τ x = 0
  · rw [if_pos hτ] at h ⊢
    omega
  · rw [if_neg hτ] at h ⊢
    omega

namespace TriangulatedDisc

variable {X : TriangleComplex V} {γ : List V} (D : TriangulatedDisc X γ)

/-! ## The darts of an inner face -/

/-- The face of an inner dart consists of the dart and its two face successors. -/
theorem faceOf_eq_iff_of_inner {d : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer)
    (e : D.map.Dart) :
    D.map.faceOf e = D.map.faceOf d ↔
      e = d ∨ e = D.map.facePerm d ∨ e = (D.map.facePerm ^ 2) d := by
  have h3 := (D.tri d hd).1
  constructor
  · intro he
    have hcyc : D.map.facePerm.SameCycle d e := ((D.map.faceOf_eq_iff e d).mp he).symm
    obtain ⟨i, hi⟩ := hcyc.exists_nat_pow_eq
    have hq : (D.map.facePerm ^ (3 * (i / 3))) d = d := by
      rw [pow_mul]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h3 _
    have hmod : (D.map.facePerm ^ (i % 3)) d = e := by
      rw [← hi]
      conv_rhs => rw [← Nat.mod_add_div i 3, pow_add, Equiv.Perm.mul_apply, hq]
    have hlt : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : i % 3
    · left
      rw [← hmod, pow_zero, Equiv.Perm.one_apply]
    · right; left
      rw [← hmod, pow_one]
    · right; right
      exact hmod.symm
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact D.map.faceOf_facePerm _
    · rw [perm_pow_two_apply, D.map.faceOf_facePerm, D.map.faceOf_facePerm]

/-- The three darts of an inner face are distinct. -/
theorem innerFace_darts_ne {d : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer) :
    D.map.facePerm d ≠ d ∧ (D.map.facePerm ^ 2) d ≠ d ∧
      (D.map.facePerm ^ 2) d ≠ D.map.facePerm d := by
  obtain ⟨-, htri⟩ := D.tri d hd
  obtain ⟨h12, h23, h13⟩ := X.tri_adj htri
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at h12
    exact X.G.irrefl h12
  · rw [h] at h13
    exact X.G.irrefl h13
  · rw [h] at h23
    exact X.G.irrefl h23

/-- The darts of an inner face, as a finset. -/
theorem filter_faceOf_eq_of_inner [DecidableEq D.map.Dart] [DecidableEq D.map.Face]
    {d : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer) :
    Finset.univ.filter (fun e => D.map.faceOf e = D.map.faceOf d) =
      {d, D.map.facePerm d, (D.map.facePerm ^ 2) d} := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  exact D.faceOf_eq_iff_of_inner hd e

/-- A sum over the darts of an inner face is a sum over three darts. -/
theorem sum_filter_faceOf_of_inner {M : Type*} [AddCommMonoid M] [DecidableEq D.map.Dart]
    [DecidableEq D.map.Face] {d : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer)
    (J : D.map.Dart → M) :
    ∑ e ∈ Finset.univ.filter (fun e => D.map.faceOf e = D.map.faceOf d), J e =
      J d + J (D.map.facePerm d) + J ((D.map.facePerm ^ 2) d) := by
  obtain ⟨h1, h2, h12⟩ := D.innerFace_darts_ne hd
  rw [D.filter_faceOf_eq_of_inner hd, Finset.sum_insert, Finset.sum_insert,
    Finset.sum_singleton, add_assoc]
  · simpa using h12.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm⟩

/-- Summing over inner darts is summing over inner faces. -/
theorem sum_innerDarts {M : Type*} [AddCommMonoid M] [DecidableEq D.map.Dart]
    [DecidableEq D.map.Face] (J : D.map.Dart → M) :
    ∑ d ∈ Finset.univ.filter (fun d => D.map.faceOf d ≠ D.outer), J d =
      ∑ f ∈ Finset.univ.erase D.outer,
        (J (Quotient.out f) + J (D.map.facePerm (Quotient.out f)) +
          J ((D.map.facePerm ^ 2) (Quotient.out f))) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := D.map.faceOf) (t := Finset.univ.erase D.outer)
    (fun d hd => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hd).2, Finset.mem_univ _⟩)]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hne : f ≠ D.outer := Finset.ne_of_mem_erase hf
  have hrep : D.map.faceOf (Quotient.out f) = f := Quotient.out_eq f
  have hin : D.map.faceOf (Quotient.out f) ≠ D.outer := by rw [hrep]; exact hne
  rw [← D.sum_filter_faceOf_of_inner hin J, Finset.filter_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrep]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by rw [h]; exact hne, h⟩

/-! ## HC11: the typed count -/

/-- The boundary vertices number at most the boundary length. -/
theorem card_boundaryVertices_le [DecidablePred D.Interior] [DecidableEq D.map.Face]
    [DecidableEq D.map.Vertex] :
    (Finset.univ.filter (fun v => ¬ D.Interior v)).card ≤ D.map.faceDegree D.outer := by
  have hsub : Finset.univ.filter (fun v => ¬ D.Interior v) ⊆
      (Finset.univ.filter (fun d => D.map.faceOf d = D.outer)).image D.map.vertexOf := by
    intro v hv
    have hv' : ¬ D.Interior v := (Finset.mem_filter.mp hv).2
    unfold Interior at hv'
    push Not at hv'
    obtain ⟨d, hdv, hdo⟩ := hv'
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdo⟩, hdv⟩
  have hcard : (Finset.univ.filter (fun d => D.map.faceOf d = D.outer)).card =
      D.map.faceDegree D.outer := by
    change _ = Nat.card {e : D.map.Dart //
      (Quotient.mk'' e : CombMap.Orbit D.map.facePerm) = D.outer}
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hcard.le)

/-- The corners at interior vertices weigh at most the corners of inner faces. -/
theorem sum_interior_le [DecidablePred D.Interior] [DecidableEq D.map.Face]
    [DecidableEq D.map.Vertex] (w : V → ℕ) :
    ∑ v ∈ Finset.univ.filter D.Interior, D.map.vertexDegree v * w (D.vtx v) ≤
      ∑ d ∈ Finset.univ.filter (fun d => D.map.faceOf d ≠ D.outer),
        w (D.vtx (D.map.vertexOf d)) := by
  have hfib : ∑ v ∈ Finset.univ.filter D.Interior, D.map.vertexDegree v * w (D.vtx v) =
      ∑ d ∈ Finset.univ.filter (fun d => D.Interior (D.map.vertexOf d)),
        w (D.vtx (D.map.vertexOf d)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := D.map.vertexOf)
      (t := Finset.univ.filter D.Interior)
      (fun d hd => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩)]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hvint : D.Interior v := (Finset.mem_filter.mp hv).2
    rw [Finset.sum_const_nat (m := w (D.vtx v)) (fun d hd => by
      rw [(Finset.mem_filter.mp hd).2])]
    congr 1
    have hset : (Finset.univ.filter (fun d => D.Interior (D.map.vertexOf d))).filter
        (fun d => D.map.vertexOf d = v) =
          Finset.univ.filter (fun d => D.map.vertexOf d = v) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by rw [h]; exact hvint, h⟩
    rw [hset]
    change Nat.card {e : D.map.Dart //
      (Quotient.mk'' e : CombMap.Orbit D.map.sigma) = v} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [hfib]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
  intro d hd
  have hint : D.Interior (D.map.vertexOf d) := (Finset.mem_filter.mp hd).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hint d rfl⟩

/-- **HC11: the typed count.**  Three distinct types on every triangle and typed interior
degrees give the record of the angled curvature count. -/
theorem exists_typedCounts (τ : V → Fin 3)
    (hτ : ∀ {x y z}, X.Tri x y z → τ x ≠ τ y ∧ τ y ≠ τ z ∧ τ x ≠ τ z)
    (hdeg : ∀ w, D.Interior w → typedGirth τ (D.vtx w) ≤ D.map.vertexDegree w) :
    ∃ C : TypedTriangularDiscCounts,
      C.faceCount = D.innerFaceCount ∧ C.boundaryLength = D.map.faceDegree D.outer := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D.map.Vertex))
    D.Interior
  have hV : (Finset.univ : Finset D.map.Vertex).card = D.map.vertexCount := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  have hangle : 24 * (Finset.univ.filter D.Interior).card ≤ 10 * D.innerFaceCount := by
    have h1 : 24 * (Finset.univ.filter D.Interior).card ≤
        ∑ v ∈ Finset.univ.filter D.Interior,
          D.map.vertexDegree v * cornerWeight τ (D.vtx v) := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun v hv =>
        twentyFour_le_mul_cornerWeight τ (hdeg v (Finset.mem_filter.mp hv).2)
    have h2 := D.sum_interior_le (cornerWeight τ)
    have h3 : ∑ d ∈ Finset.univ.filter (fun d => D.map.faceOf d ≠ D.outer),
        cornerWeight τ (D.vtx (D.map.vertexOf d)) = 10 * D.innerFaceCount := by
      rw [D.sum_innerDarts]
      have hface : ∀ f ∈ Finset.univ.erase D.outer,
          cornerWeight τ (D.vtx (D.map.vertexOf (Quotient.out f))) +
            cornerWeight τ (D.vtx (D.map.vertexOf (D.map.facePerm (Quotient.out f)))) +
            cornerWeight τ (D.vtx (D.map.vertexOf ((D.map.facePerm ^ 2) (Quotient.out f)))) =
              10 := by
        intro f hf
        have hne : f ≠ D.outer := Finset.ne_of_mem_erase hf
        have hrep : D.map.faceOf (Quotient.out f) = f := Quotient.out_eq f
        have hin : D.map.faceOf (Quotient.out f) ≠ D.outer := by rw [hrep]; exact hne
        exact cornerWeight_add τ (hτ (D.tri _ hin).2)
      rw [Finset.sum_congr rfl hface, Finset.sum_const, smul_eq_mul,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card]
      change (D.map.faceCount - 1) * 10 = 10 * (D.map.faceCount - 1)
      ring
    omega
  refine ⟨{ vertexCount := D.map.vertexCount
            edgeCount := D.map.edgeCount
            faceCount := D.innerFaceCount
            boundaryLength := D.map.faceDegree D.outer
            boundaryVertexCount := (Finset.univ.filter (fun v => ¬ D.Interior v)).card
            interiorVertexCount := (Finset.univ.filter D.Interior).card
            boundaryVertexCount_le := D.card_boundaryVertices_le
            interiorVertexCount_eq := by omega
            euler := D.vertexCount_add_innerFaceCount
            faceIncidence := D.two_mul_edgeCount
            angleLower := hangle }, rfl, rfl⟩

/-! ## HC12: sums around the boundary -/

/-- **The sum of an antisymmetric function over all darts vanishes.** -/
theorem sum_darts_antisymm (I : V → V → ℤ) (hanti : ∀ x y, I y x = -I x y) :
    ∑ d : D.map.Dart,
      I (D.vtx (D.map.vertexOf d)) (D.vtx (D.map.vertexOf (D.map.alpha d))) = 0 := by
  have hswap := (Equiv.sum_comp D.map.alpha
    (fun d => I (D.vtx (D.map.vertexOf d)) (D.vtx (D.map.vertexOf (D.map.alpha d))))).symm
  simp only [D.map.alpha_involutive _] at hswap
  have hneg : ∑ d : D.map.Dart,
      I (D.vtx (D.map.vertexOf (D.map.alpha d))) (D.vtx (D.map.vertexOf d)) =
        -∑ d : D.map.Dart,
          I (D.vtx (D.map.vertexOf d)) (D.vtx (D.map.vertexOf (D.map.alpha d))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => hanti _ _
  rw [hneg] at hswap
  omega

/-- The outer darts, read from `base`, are the boundary. -/
theorem sum_outerDarts [DecidableEq D.map.Face] (J : D.map.Dart → ℤ) :
    ∑ d ∈ Finset.univ.filter (fun d => D.map.faceOf d = D.outer), J d =
      ∑ k : Fin (D.map.faceDegree D.outer), J ((D.map.facePerm ^ (k : ℕ)) D.base) := by
  classical
  let l := closedOrbitList D.map.facePerm D.base
  have hnd : l.Nodup := closedOrbitList.nodup D.map.facePerm D.base
  have hlen : l.length = D.map.faceDegree D.outer := by
    rw [← D.base_outer]
    exact closedOrbitList.length_eq_orbitDegree D.map.facePerm D.base
  have hset : l.toFinset = Finset.univ.filter (fun d => D.map.faceOf d = D.outer) := by
    ext e
    rw [List.mem_toFinset, closedOrbitList.mem_iff_sameCycle, Finset.mem_filter,
      ← D.base_outer]
    simp only [Finset.mem_univ, true_and]
    rw [D.map.faceOf_eq_iff]
    exact Equiv.Perm.sameCycle_comm
  have hget : ∀ (k : ℕ) (hk : k < l.length), l[k] = (D.map.facePerm ^ k) D.base := by
    intro k hk
    by_cases hfix : D.map.facePerm D.base = D.base
    · have hl : l = [D.base] := by simp [l, closedOrbitList, hfix]
      have hk0 : k = 0 := by
        have : l.length = 1 := by rw [hl]; rfl
        omega
      subst hk0
      simp only [hl, List.getElem_cons_zero, pow_zero, Equiv.Perm.one_apply]
    · have hl : l = D.map.facePerm.toList D.base := by simp [l, closedOrbitList, hfix]
      simp only [hl]
      exact Equiv.Perm.getElem_toList _ _
  have hofFn : l = List.ofFn (fun k : Fin (D.map.faceDegree D.outer) =>
      (D.map.facePerm ^ (k : ℕ)) D.base) := by
    apply List.ext_getElem
    · rw [List.length_ofFn, hlen]
    · intro k h1 h2
      rw [List.getElem_ofFn, hget k h1]
  rw [← hset, Finset.sum_toFinset J hnd, hofFn, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **HC12: boundary sums.**  An antisymmetric function whose sum around every triangle of
`X` is at most `C₀` has boundary sum at most `C₀` times the number of triangles. -/
theorem abs_boundarySum_le (I : V → V → ℤ) (hanti : ∀ x y, I y x = -I x y) {C₀ : ℕ}
    (htri : ∀ {x y z}, X.Tri x y z → |I x y + I y z + I z x| ≤ C₀) :
    |(List.zipWith I γ γ.tail).sum| ≤ C₀ * D.innerFaceCount := by
  classical
  let J : D.map.Dart → ℤ := fun d =>
    I (D.vtx (D.map.vertexOf d)) (D.vtx (D.map.vertexOf (D.map.alpha d)))
  -- the boundary sum is the sum over outer darts
  have hbd : (List.zipWith I γ γ.tail).sum =
      ∑ d ∈ Finset.univ.filter (fun d => D.map.faceOf d = D.outer), J d := by
    rw [D.sum_outerDarts J, ← D.boundary]
    have hzip : List.zipWith I
        (List.ofFn fun k : Fin (D.map.faceDegree D.outer + 1) =>
          D.vtx (D.map.vertexOf ((D.map.facePerm ^ (k : ℕ)) D.base)))
        (List.ofFn fun k : Fin (D.map.faceDegree D.outer + 1) =>
          D.vtx (D.map.vertexOf ((D.map.facePerm ^ (k : ℕ)) D.base))).tail =
        List.ofFn fun k : Fin (D.map.faceDegree D.outer) => J ((D.map.facePerm ^ (k : ℕ)) D.base) := by
      apply List.ext_getElem
      · simp only [List.length_zipWith, List.length_ofFn, List.length_tail]
        omega
      · intro k h1 h2
        rw [List.getElem_zipWith, List.getElem_tail, List.getElem_ofFn, List.getElem_ofFn,
          List.getElem_ofFn]
        show I (D.vtx (D.map.vertexOf ((D.map.facePerm ^ k) D.base)))
            (D.vtx (D.map.vertexOf ((D.map.facePerm ^ (k + 1)) D.base))) =
          I (D.vtx (D.map.vertexOf ((D.map.facePerm ^ k) D.base)))
            (D.vtx (D.map.vertexOf (D.map.alpha ((D.map.facePerm ^ k) D.base))))
        rw [pow_succ', Equiv.Perm.mul_apply, vertexOf_facePerm]
    rw [hzip, List.sum_ofFn]
  -- the sum over all darts vanishes
  have hall := D.sum_darts_antisymm I hanti
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun d => D.map.faceOf d = D.outer)]
    at hall
  have hinner : ∑ d ∈ Finset.univ.filter (fun d => ¬ D.map.faceOf d = D.outer), J d =
      ∑ f ∈ Finset.univ.erase D.outer,
        (J (Quotient.out f) + J (D.map.facePerm (Quotient.out f)) +
          J ((D.map.facePerm ^ 2) (Quotient.out f))) :=
    D.sum_innerDarts J
  have hface : ∀ f ∈ Finset.univ.erase D.outer,
      |J (Quotient.out f) + J (D.map.facePerm (Quotient.out f)) +
        J ((D.map.facePerm ^ 2) (Quotient.out f))| ≤ C₀ := by
    intro f hf
    have hne : f ≠ D.outer := Finset.ne_of_mem_erase hf
    have hrep : D.map.faceOf (Quotient.out f) = f := Quotient.out_eq f
    have hin : D.map.faceOf (Quotient.out f) ≠ D.outer := by rw [hrep]; exact hne
    obtain ⟨h3, htri'⟩ := D.tri _ hin
    have hclose : D.map.vertexOf (D.map.alpha ((D.map.facePerm ^ 2) (Quotient.out f))) =
        D.map.vertexOf (Quotient.out f) := by
      rw [← vertexOf_facePerm, ← perm_pow_three_apply, h3]
    have e2 : D.map.vertexOf (D.map.alpha (Quotient.out f)) =
        D.map.vertexOf (D.map.facePerm (Quotient.out f)) := (vertexOf_facePerm _ _).symm
    have e3 : D.map.vertexOf (D.map.alpha (D.map.facePerm (Quotient.out f))) =
        D.map.vertexOf ((D.map.facePerm ^ 2) (Quotient.out f)) := by
      rw [perm_pow_two_apply, vertexOf_facePerm]
    show |I (D.vtx (D.map.vertexOf (Quotient.out f)))
          (D.vtx (D.map.vertexOf (D.map.alpha (Quotient.out f)))) +
        I (D.vtx (D.map.vertexOf (D.map.facePerm (Quotient.out f))))
          (D.vtx (D.map.vertexOf (D.map.alpha (D.map.facePerm (Quotient.out f))))) +
        I (D.vtx (D.map.vertexOf ((D.map.facePerm ^ 2) (Quotient.out f))))
          (D.vtx (D.map.vertexOf (D.map.alpha ((D.map.facePerm ^ 2) (Quotient.out f)))))| ≤ C₀
    rw [e2, e3, hclose]
    exact htri htri'
  have hinner_le : |∑ d ∈ Finset.univ.filter (fun d => ¬ D.map.faceOf d = D.outer), J d| ≤
      C₀ * D.innerFaceCount := by
    rw [hinner]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hface).trans ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    change ((D.map.faceCount - 1 : ℕ) : ℤ) * (C₀ : ℤ) ≤ ((C₀ * (D.map.faceCount - 1) : ℕ) : ℤ)
    push_cast
    ring_nf
    exact le_refl _
  rw [hbd]
  have hout : ∑ d ∈ Finset.univ.filter (fun d => D.map.faceOf d = D.outer), J d =
      -∑ d ∈ Finset.univ.filter (fun d => ¬ D.map.faceOf d = D.outer), J d := by
    have hall' : ∑ d ∈ Finset.univ.filter (fun d => D.map.faceOf d = D.outer), J d +
        ∑ d ∈ Finset.univ.filter (fun d => ¬ D.map.faceOf d = D.outer), J d = 0 := hall
    omega
  rw [hout, abs_neg]
  exact hinner_le

end TriangulatedDisc

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms TriangulatedDisc.exists_typedCounts
#audit_axioms TriangulatedDisc.abs_boundarySum_le
