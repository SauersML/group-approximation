import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# Kakutani–Rokhlin tower coordinates

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–315 (Matui, Lemma 3.4 and Theorem 4.9).

Let `Y` be a clopen set that every orbit meets with bounded gaps
(`∀ x, ∃ j ≤ H, T^{-j} x ∈ Y`; `exists_bounded_return` for minimal systems). Every point `x` has a
unique coordinate `x = T^a y` with `y ∈ Y` and `T^k y ∉ Y` for `0 < k ≤ a` (`IsCoord T Y y a x`).
This is the Kakutani–Rokhlin tower over `Y` used by Matui (Internat. J. Math. 2006, Lemma 3.4, §4)
and Grigorchuk–Medynets (2014, §3). No metrizability is needed.

* `isCoord_unique`, `exists_isCoord`: coordinates exist and are unique; `NoReturn.le_of_ret` says
  levels are at most `H`;
* `isCoord_zpow_of_notMem_thin`: a point outside `thin T Y M` moved by at most `M` along its orbit
  stays in its tower over the same base point.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X}

/-- `y` does not return to `Y` within `n` steps. -/
def NoReturn (T : X ≃ₜ X) (Y : Set X) (y : X) (n : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ n → (T ^ (k : ℤ)) y ∉ Y

theorem NoReturn.mono {y : X} {n n' : ℕ} (h : NoReturn T Y y n) (hn : n' ≤ n) :
    NoReturn T Y y n' :=
  fun k hk1 hk2 => h k hk1 (by omega)

theorem noReturn_of_wandering {L : ℕ} (hY : Wandering T Y L) {y : X} (hy : y ∈ Y) :
    NoReturn T Y y L :=
  fun k hk1 hk2 => hY k (by omega) (by omega) (by omega) y hy

theorem isClopen_setOf_noReturn (hYc : IsClopen Y) (n : ℕ) :
    IsClopen {y | NoReturn T Y y n} := by
  have e : {y | NoReturn T Y y n} = ⋂ k ∈ Finset.Icc 1 n, ⇑(T ^ (k : ℤ)) ⁻¹' Yᶜ := by
    ext y
    rw [Set.mem_iInter₂]
    constructor
    · intro h k hk
      exact h k (by have := (Finset.mem_Icc.mp hk).1; omega) (Finset.mem_Icc.mp hk).2
    · intro h k hk1 hk2
      exact h k (Finset.mem_Icc.mpr ⟨by omega, hk2⟩)
  rw [e]
  exact isClopen_biInter_finset fun k _ => hYc.compl.preimage (T ^ (k : ℤ)).continuous

/-- `x = T^a y` sits at level `a` of the tower over the base point `y ∈ Y`. -/
def IsCoord (T : X ≃ₜ X) (Y : Set X) (y : X) (a : ℕ) (x : X) : Prop :=
  y ∈ Y ∧ NoReturn T Y y a ∧ (T ^ (a : ℤ)) y = x

theorem not_lt_of_zpow_eq {y y' : X} {a a' : ℕ} (hy : y ∈ Y) (hn : NoReturn T Y y' a')
    (he : (T ^ (a : ℤ)) y = (T ^ (a' : ℤ)) y') : ¬a < a' := by
  intro hlt
  refine hn (a' - a) (by omega) (by omega) ?_
  have e2 : (T ^ ((a' - a : ℕ) : ℤ)) y' = y := by
    rw [show ((a' - a : ℕ) : ℤ) = -(a : ℤ) + a' by omega, ← zpow_apply_zpow_apply, ← he,
      zpow_neg_apply_zpow_apply]
  rw [e2]
  exact hy

/-- Tower coordinates are unique. -/
theorem isCoord_unique {y y' x : X} {a a' : ℕ} (h : IsCoord T Y y a x)
    (h' : IsCoord T Y y' a' x) : a = a' ∧ y = y' := by
  obtain ⟨hy, hna, hxa⟩ := h
  obtain ⟨hy', hna', hxa'⟩ := h'
  have h1 : ¬a < a' := not_lt_of_zpow_eq hy hna' (hxa.trans hxa'.symm)
  have h2 : ¬a' < a := not_lt_of_zpow_eq hy' hna (hxa'.trans hxa.symm)
  have ha : a = a' := by omega
  subst ha
  exact ⟨rfl, (T ^ (a : ℤ)).injective (hxa.trans hxa'.symm)⟩

/-- Tower coordinates exist, at levels at most `H`. -/
theorem exists_isCoord {H : ℕ} (hret : ∀ x : X, ∃ j : ℕ, j ≤ H ∧ (T ^ (-(j : ℤ))) x ∈ Y)
    (x : X) : ∃ y a, a ≤ H ∧ IsCoord T Y y a x := by
  classical
  have hex : ∃ j : ℕ, (T ^ (-(j : ℤ))) x ∈ Y := by
    obtain ⟨j, -, hj⟩ := hret x
    exact ⟨j, hj⟩
  refine ⟨(T ^ (-((Nat.find hex : ℕ) : ℤ))) x, Nat.find hex, ?_, Nat.find_spec hex,
    fun k hk1 hk2 => ?_, ?_⟩
  · obtain ⟨j, hjH, hj⟩ := hret x
    exact (Nat.find_min' hex hj).trans hjH
  · have hmin := Nat.find_min hex (m := Nat.find hex - k) (by omega)
    rw [zpow_apply_zpow_apply_of_eq T (k : ℤ) (-((Nat.find hex : ℕ) : ℤ))
      (-((Nat.find hex - k : ℕ) : ℤ)) (by omega) x]
    exact hmin
  · rw [zpow_apply_zpow_apply_of_eq T ((Nat.find hex : ℕ) : ℤ) (-((Nat.find hex : ℕ) : ℤ)) 0
      (by ring) x, homeo_zpow_zero_apply]

/-- Levels of towers are at most the return bound `H`. -/
theorem NoReturn.le_of_ret {H : ℕ} (hret : ∀ x : X, ∃ j : ℕ, j ≤ H ∧ (T ^ (-(j : ℤ))) x ∈ Y)
    {y : X} {b : ℕ} (hb : NoReturn T Y y b) : b ≤ H := by
  by_contra hlt
  obtain ⟨j, hjH, hj⟩ := hret ((T ^ (b : ℤ)) y)
  refine hb (b - j) (by omega) (by omega) ?_
  rw [show ((b - j : ℕ) : ℤ) = -(j : ℤ) + b by omega, ← zpow_apply_zpow_apply]
  exact hj

/-- Orbits of a minimal system meet a nonempty clopen set with bounded gaps. -/
theorem exists_bounded_return [CompactSpace X] (hmin : SimpleKazhdanSofic.IsMinimalSystem T)
    (hYc : IsClopen Y) (hYne : Y.Nonempty) :
    ∃ H : ℕ, ∀ x : X, ∃ j : ℕ, j ≤ H ∧ (T ^ (-(j : ℤ))) x ∈ Y := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun j : ℤ => ⇑(T ^ j) ⁻¹' Y)
    (fun j => hYc.isOpen.preimage (T ^ j).continuous) fun x _ => by
      obtain ⟨z, ⟨j, rfl⟩, hz⟩ := (hmin x).exists_mem_open hYc.isOpen hYne
      exact Set.mem_iUnion.mpr ⟨j, hz⟩
  refine ⟨2 * t.sup Int.natAbs, fun x => ?_⟩
  obtain ⟨j, hj, hjx⟩ :=
    Set.mem_iUnion₂.mp (ht (Set.mem_univ ((T ^ (-((t.sup Int.natAbs : ℕ) : ℤ))) x)))
  have hjK : j.natAbs ≤ t.sup Int.natAbs := Finset.le_sup hj
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = (t.sup Int.natAbs : ℤ) - j :=
    ⟨((t.sup Int.natAbs : ℤ) - j).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hjx' : (T ^ j) ((T ^ (-((t.sup Int.natAbs : ℕ) : ℤ))) x) ∈ Y := hjx
  rw [zpow_apply_zpow_apply_of_eq T j (-((t.sup Int.natAbs : ℕ) : ℤ)) (-(i : ℤ)) (by omega) x]
    at hjx'
  exact ⟨i, by omega, hjx'⟩

/-- A point outside `thin T Y M`, moved by at most `M` along its orbit, stays in its tower. -/
theorem isCoord_zpow_of_notMem_thin {M : ℕ} {x y : X} {a : ℕ} (hx : x ∉ thin T Y M)
    (h : IsCoord T Y y a x) {n : ℤ} (hn1 : -(M : ℤ) ≤ n) (hn2 : n ≤ M) :
    ∃ b : ℕ, IsCoord T Y y b ((T ^ n) x) := by
  obtain ⟨hy, hna, hxa⟩ := h
  have haM : M < a := by
    by_contra hle
    refine hx (mem_thin_of (k := -(a : ℤ)) (by omega) (by omega) ?_)
    rw [← hxa, zpow_neg_apply_zpow_apply]
    exact hy
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = a + n := ⟨((a : ℤ) + n).toNat, Int.toNat_of_nonneg (by omega)⟩
  refine ⟨b, hy, fun k hk1 hk2 => ?_, ?_⟩
  · by_cases hka : k ≤ a
    · exact hna k hk1 hka
    · intro hk
      refine hx (mem_thin_of (k := (k : ℤ) - a) (by omega) (by omega) ?_)
      rw [← hxa, zpow_apply_zpow_apply_of_eq T ((k : ℤ) - a) (a : ℤ) (k : ℤ) (by ring) y]
      exact hk
  · rw [← hxa, zpow_apply_zpow_apply_of_eq T n (a : ℤ) (b : ℤ) (by omega) y]

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.isCoord_unique
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_isCoord
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_bounded_return
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.isCoord_zpow_of_notMem_thin
